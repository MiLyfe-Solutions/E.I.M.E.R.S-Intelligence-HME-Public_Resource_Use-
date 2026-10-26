import V185TrunkScan23Chunk1307

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7747278 : List Nat := [4, 1, 1, 1, 3, 1, 2, 5, 5]
def baseStart_7747278 : Nat := 118140960795 + 7747278 * 2 ^ 59
def prefixEnd_7747278 : Nat := 4983230072969 + 3 ^ 40 * 7747278 * 2
def baseEnd_7747278 : Nat := 442008597555916108099547

theorem tailTrace_7747278 : CollatzResearch.WordTrace tailWord_7747278 prefixEnd_7747278 442008597555916108099547 := by
  unfold tailWord_7747278
  simp only [CollatzResearch.WordTrace]
  refine ⟨35320805303367801323471311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188377628284628273725180325 35320805303367801323471311)
  ·
    refine ⟨52981207955051701985206967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35320805303367801323471311 52981207955051701985206967)
    ·
      refine ⟨79471811932577552977810451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52981207955051701985206967 79471811932577552977810451)
      ·
        refine ⟨119207717898866329466715677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79471811932577552977810451 119207717898866329466715677)
        ·
          refine ⟨44702894212074873550018379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119207717898866329466715677 44702894212074873550018379)
          ·
            refine ⟨67054341318112310325027569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44702894212074873550018379 67054341318112310325027569)
            ·
              refine ⟨50290755988584232743770677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67054341318112310325027569 50290755988584232743770677)
              ·
                refine ⟨4714758373929771819728501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50290755988584232743770677 4714758373929771819728501)
                ·
                  refine ⟨442008597555916108099547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4714758373929771819728501 442008597555916108099547)
                  ·
                    rfl

theorem cell23_7747278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_7747278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747278 prefixEnd_7747278 := by exact prefixLift 7747278
  have htrace : WordTrace (prefixWord ++ tailWord_7747278) baseStart_7747278 baseEnd_7747278 := by
    simpa [prefixWord, tailWord_7747278, baseEnd_7747278] using wordTrace_append hprefix tailTrace_7747278
  have hstable : (prefixWord ++ tailWord_7747278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747278).length < 2 ^ (prefixWord ++ tailWord_7747278).sum := by decide
  have hdescent : baseEnd_7747278 < baseStart_7747278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747301 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 1, 2, 5]
def baseStart_7747301 : Nat := 118140960795 + 7747301 * 2 ^ 59
def prefixEnd_7747301 : Nat := 4983230072969 + 3 ^ 40 * 7747301 * 2
def baseEnd_7747301 : Nat := 3978089188058298382908317

theorem tailTrace_7747301 : CollatzResearch.WordTrace tailWord_7747301 prefixEnd_7747301 3978089188058298382908317 := by
  unfold tailWord_7747301
  simp only [CollatzResearch.WordTrace]
  refine ⟨282567281305859085515857757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188378187537239390343905171 282567281305859085515857757)
  ·
    refine ⟨105962730489697157068446659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282567281305859085515857757 105962730489697157068446659)
    ·
      refine ⟨158944095734545735602669989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105962730489697157068446659 158944095734545735602669989)
      ·
        refine ⟨29802017950227325425500623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158944095734545735602669989 29802017950227325425500623)
        ·
          refine ⟨44703026925340988138250935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29802017950227325425500623 44703026925340988138250935)
          ·
            refine ⟨67054540388011482207376403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44703026925340988138250935 67054540388011482207376403)
            ·
              refine ⟨100581810582017223311064605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67054540388011482207376403 100581810582017223311064605)
              ·
                refine ⟨37718178968256458741649227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100581810582017223311064605 37718178968256458741649227)
                ·
                  refine ⟨56577268452384688112473841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37718178968256458741649227 56577268452384688112473841)
                  ·
                    refine ⟨42432951339288516084355381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56577268452384688112473841 42432951339288516084355381)
                    ·
                      refine ⟨3978089188058298382908317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42432951339288516084355381 3978089188058298382908317)
                      ·
                        rfl

theorem cell23_7747301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_7747301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747301 prefixEnd_7747301 := by exact prefixLift 7747301
  have htrace : WordTrace (prefixWord ++ tailWord_7747301) baseStart_7747301 baseEnd_7747301 := by
    simpa [prefixWord, tailWord_7747301, baseEnd_7747301] using wordTrace_append hprefix tailTrace_7747301
  have hstable : (prefixWord ++ tailWord_7747301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747301).length < 2 ^ (prefixWord ++ tailWord_7747301).sum := by decide
  have hdescent : baseEnd_7747301 < baseStart_7747301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747311 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 4]
def baseStart_7747311 : Nat := 118140960795 + 7747311 * 2 ^ 59
def prefixEnd_7747311 : Nat := 4983230072969 + 3 ^ 40 * 7747311 * 2
def baseEnd_7747311 : Nat := 3978094322864843343783271

theorem tailTrace_7747311 : CollatzResearch.WordTrace tailWord_7747311 prefixEnd_7747311 3978094322864843343783271 := by
  unfold tailWord_7747311
  simp only [CollatzResearch.WordTrace]
  refine ⟨282567646035822857223721787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188378430690548571482481191 282567646035822857223721787)
  ·
    refine ⟨423851469053734285835582681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282567646035822857223721787 423851469053734285835582681)
    ·
      refine ⟨317888601790300714376687011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423851469053734285835582681 317888601790300714376687011)
      ·
        refine ⟨476832902685451071565030517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317888601790300714376687011 476832902685451071565030517)
        ·
          refine ⟨44703084626761037959221611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 476832902685451071565030517 44703084626761037959221611)
          ·
            refine ⟨67054626940141556938832417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44703084626761037959221611 67054626940141556938832417)
            ·
              refine ⟨50290970205106167704124313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67054626940141556938832417 50290970205106167704124313)
              ·
                refine ⟨37718227653829625778093235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50290970205106167704124313 37718227653829625778093235)
                ·
                  refine ⟨56577341480744438667139853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37718227653829625778093235 56577341480744438667139853)
                  ·
                    refine ⟨21216503055279164500177445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56577341480744438667139853 21216503055279164500177445)
                    ·
                      refine ⟨3978094322864843343783271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21216503055279164500177445 3978094322864843343783271)
                      ·
                        rfl

theorem cell23_7747311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 4].length) (baseStart_7747311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747311 prefixEnd_7747311 := by exact prefixLift 7747311
  have htrace : WordTrace (prefixWord ++ tailWord_7747311) baseStart_7747311 baseEnd_7747311 := by
    simpa [prefixWord, tailWord_7747311, baseEnd_7747311] using wordTrace_append hprefix tailTrace_7747311
  have hstable : (prefixWord ++ tailWord_7747311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747311).length < 2 ^ (prefixWord ++ tailWord_7747311).sum := by decide
  have hdescent : baseEnd_7747311 < baseStart_7747311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747389 : List Nat := [1, 4, 1, 4, 1, 3, 1, 3, 1, 4]
def baseStart_7747389 : Nat := 118140960795 + 7747389 * 2 ^ 59
def prefixEnd_7747389 : Nat := 4983230072969 + 3 ^ 40 * 7747389 * 2
def baseEnd_7747389 : Nat := 1326044791451964679535971

theorem tailTrace_7747389 : CollatzResearch.WordTrace tailWord_7747389 prefixEnd_7747389 1326044791451964679535971 := by
  unfold tailWord_7747389
  simp only [CollatzResearch.WordTrace]
  refine ⟨282570490929540276545061221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188380327286360184363374147 282570490929540276545061221)
  ·
    refine ⟨52981967049288801852198979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282570490929540276545061221 52981967049288801852198979)
    ·
      refine ⟨79472950573933202778298469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52981967049288801852198979 79472950573933202778298469)
      ·
        refine ⟨14901178232612475520930963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79472950573933202778298469 14901178232612475520930963)
        ·
          refine ⟨22351767348918713281396445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14901178232612475520930963 22351767348918713281396445)
          ·
            refine ⟨8381912755844517480523667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22351767348918713281396445 8381912755844517480523667)
            ·
              refine ⟨12572869133766776220785501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8381912755844517480523667 12572869133766776220785501)
              ·
                refine ⟨4714825925162541082794563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12572869133766776220785501 4714825925162541082794563)
                ·
                  refine ⟨7072238887743811624191845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4714825925162541082794563 7072238887743811624191845)
                  ·
                    refine ⟨1326044791451964679535971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7072238887743811624191845 1326044791451964679535971)
                    ·
                      rfl

theorem cell23_7747389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_7747389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747389 prefixEnd_7747389 := by exact prefixLift 7747389
  have htrace : WordTrace (prefixWord ++ tailWord_7747389) baseStart_7747389 baseEnd_7747389 := by
    simpa [prefixWord, tailWord_7747389, baseEnd_7747389] using wordTrace_append hprefix tailTrace_7747389
  have hstable : (prefixWord ++ tailWord_7747389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747389).length < 2 ^ (prefixWord ++ tailWord_7747389).sum := by decide
  have hdescent : baseEnd_7747389 < baseStart_7747389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747412 : List Nat := [2, 4, 1, 1, 3, 1, 3, 1, 3, 1, 3]
def baseStart_7747412 : Nat := 118140960795 + 7747412 * 2 ^ 59
def prefixEnd_7747412 : Nat := 4983230072969 + 3 ^ 40 * 7747412 * 2
def baseEnd_7747412 : Nat := 3978146184410947448620307

theorem tailTrace_7747412 : CollatzResearch.WordTrace tailWord_7747412 prefixEnd_7747412 3978146184410947448620307 := by
  unfold tailWord_7747412
  simp only [CollatzResearch.WordTrace]
  refine ⟨141285664904228475736574245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188380886538971300982098993 141285664904228475736574245)
  ·
    refine ⟨26491062169542839200607671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141285664904228475736574245 26491062169542839200607671)
    ·
      refine ⟨39736593254314258800911507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26491062169542839200607671 39736593254314258800911507)
      ·
        refine ⟨59604889881471388201367261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39736593254314258800911507 59604889881471388201367261)
        ·
          refine ⟨22351833705551770575512723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59604889881471388201367261 22351833705551770575512723)
          ·
            refine ⟨33527750558327655863269085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22351833705551770575512723 33527750558327655863269085)
            ·
              refine ⟨12572906459372870948725907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33527750558327655863269085 12572906459372870948725907)
              ·
                refine ⟨18859359689059306423088861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12572906459372870948725907 18859359689059306423088861)
                ·
                  refine ⟨7072259883397239908658323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18859359689059306423088861 7072259883397239908658323)
                  ·
                    refine ⟨10608389825095859862987485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7072259883397239908658323 10608389825095859862987485)
                    ·
                      refine ⟨3978146184410947448620307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10608389825095859862987485 3978146184410947448620307)
                      ·
                        rfl

theorem cell23_7747412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_7747412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747412 prefixEnd_7747412 := by exact prefixLift 7747412
  have htrace : WordTrace (prefixWord ++ tailWord_7747412) baseStart_7747412 baseEnd_7747412 := by
    simpa [prefixWord, tailWord_7747412, baseEnd_7747412] using wordTrace_append hprefix tailTrace_7747412
  have hstable : (prefixWord ++ tailWord_7747412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747412).length < 2 ^ (prefixWord ++ tailWord_7747412).sum := by decide
  have hdescent : baseEnd_7747412 < baseStart_7747412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747418 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4]
def baseStart_7747418 : Nat := 118140960795 + 7747418 * 2 ^ 59
def prefixEnd_7747418 : Nat := 4983230072969 + 3 ^ 40 * 7747418 * 2
def baseEnd_7747418 : Nat := 3978149265294874425145279

theorem tailTrace_7747418 : CollatzResearch.WordTrace tailWord_7747418 prefixEnd_7747418 3978149265294874425145279 := by
  unfold tailWord_7747418
  simp only [CollatzResearch.WordTrace]
  refine ⟨70642887161608803624466727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188381032430956809665244605 70642887161608803624466727)
  ·
    refine ⟨105964330742413205436700091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70642887161608803624466727 105964330742413205436700091)
    ·
      refine ⟨158946496113619808155050137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105964330742413205436700091 158946496113619808155050137)
      ·
        refine ⟨119209872085214856116287603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158946496113619808155050137 119209872085214856116287603)
        ·
          refine ⟨178814808127822284174431405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119209872085214856116287603 178814808127822284174431405)
          ·
            refine ⟨67055553047933356565411777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178814808127822284174431405 67055553047933356565411777)
            ·
              refine ⟨50291664785950017424058833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67055553047933356565411777 50291664785950017424058833)
              ·
                refine ⟨37718748589462513068044125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50291664785950017424058833 37718748589462513068044125)
                ·
                  refine ⟨14144530721048442400516547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37718748589462513068044125 14144530721048442400516547)
                  ·
                    refine ⟨21216796081572663600774821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14144530721048442400516547 21216796081572663600774821)
                    ·
                      refine ⟨3978149265294874425145279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21216796081572663600774821 3978149265294874425145279)
                      ·
                        rfl

theorem cell23_7747418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_7747418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747418 prefixEnd_7747418 := by exact prefixLift 7747418
  have htrace : WordTrace (prefixWord ++ tailWord_7747418) baseStart_7747418 baseEnd_7747418 := by
    simpa [prefixWord, tailWord_7747418, baseEnd_7747418] using wordTrace_append hprefix tailTrace_7747418
  have hstable : (prefixWord ++ tailWord_7747418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747418).length < 2 ^ (prefixWord ++ tailWord_7747418).sum := by decide
  have hdescent : baseEnd_7747418 < baseStart_7747418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747435 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 5, 2, 2]
def baseStart_7747435 : Nat := 118140960795 + 7747435 * 2 ^ 59
def prefixEnd_7747435 : Nat := 4983230072969 + 3 ^ 40 * 7747435 * 2
def baseEnd_7747435 : Nat := 3978157994466000858632701

theorem tailTrace_7747435 : CollatzResearch.WordTrace tailWord_7747435 prefixEnd_7747435 3978157994466000858632701 := by
  unfold tailWord_7747435
  simp only [CollatzResearch.WordTrace]
  refine ⟨282572168687373626401235759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188381445791582417600823839 282572168687373626401235759)
  ·
    refine ⟨423858253031060439601853639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282572168687373626401235759 423858253031060439601853639)
    ·
      refine ⟨635787379546590659402780459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423858253031060439601853639 635787379546590659402780459)
      ·
        refine ⟨953681069319885989104170689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635787379546590659402780459 953681069319885989104170689)
        ·
          refine ⟨715260801989914491828128017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 953681069319885989104170689 715260801989914491828128017)
          ·
            refine ⟨536445601492435868871096013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 715260801989914491828128017 536445601492435868871096013)
            ·
              refine ⟨201167100559663450826661005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 536445601492435868871096013 201167100559663450826661005)
              ·
                refine ⟨75437662709873794059997877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201167100559663450826661005 75437662709873794059997877)
                ·
                  refine ⟨7072280879050668193124801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75437662709873794059997877 7072280879050668193124801)
                  ·
                    refine ⟨5304210659288001144843601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7072280879050668193124801 5304210659288001144843601)
                    ·
                      refine ⟨3978157994466000858632701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5304210659288001144843601 3978157994466000858632701)
                      ·
                        rfl

theorem cell23_7747435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 2, 2].length) (baseStart_7747435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747435 prefixEnd_7747435 := by exact prefixLift 7747435
  have htrace : WordTrace (prefixWord ++ tailWord_7747435) baseStart_7747435 baseEnd_7747435 := by
    simpa [prefixWord, tailWord_7747435, baseEnd_7747435] using wordTrace_append hprefix tailTrace_7747435
  have hstable : (prefixWord ++ tailWord_7747435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747435).length < 2 ^ (prefixWord ++ tailWord_7747435).sum := by decide
  have hdescent : baseEnd_7747435 < baseStart_7747435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747441 : List Nat := [1, 2, 2, 2, 1, 3, 1, 11]
def baseStart_7747441 : Nat := 118140960795 + 7747441 * 2 ^ 59
def prefixEnd_7747441 : Nat := 4983230072969 + 3 ^ 40 * 7747441 * 2
def baseEnd_7747441 : Nat := 147339299087034364265099

theorem tailTrace_7747441 : CollatzResearch.WordTrace tailWord_7747441 prefixEnd_7747441 147339299087034364265099 := by
  unfold tailWord_7747441
  simp only [CollatzResearch.WordTrace]
  refine ⟨282572387525351889425954177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188381591683567926283969451 282572387525351889425954177)
  ·
    refine ⟨211929290644013917069465633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282572387525351889425954177 211929290644013917069465633)
    ·
      refine ⟨158946967983010437802099225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211929290644013917069465633 158946967983010437802099225)
      ·
        refine ⟨119210225987257828351574419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158946967983010437802099225 119210225987257828351574419)
        ·
          refine ⟨178815338980886742527361629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119210225987257828351574419 178815338980886742527361629)
          ·
            refine ⟨67055752117832528447760611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178815338980886742527361629 67055752117832528447760611)
            ·
              refine ⟨100583628176748792671640917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67055752117832528447760611 100583628176748792671640917)
              ·
                refine ⟨147339299087034364265099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 100583628176748792671640917 147339299087034364265099)
                ·
                  rfl

theorem cell23_7747441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 11].length) (baseStart_7747441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747441 prefixEnd_7747441 := by exact prefixLift 7747441
  have htrace : WordTrace (prefixWord ++ tailWord_7747441) baseStart_7747441 baseEnd_7747441 := by
    simpa [prefixWord, tailWord_7747441, baseEnd_7747441] using wordTrace_append hprefix tailTrace_7747441
  have hstable : (prefixWord ++ tailWord_7747441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747441).length < 2 ^ (prefixWord ++ tailWord_7747441).sum := by decide
  have hdescent : baseEnd_7747441 < baseStart_7747441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747458 : List Nat := [3, 4, 2, 14]
def baseStart_7747458 : Nat := 118140960795 + 7747458 * 2 ^ 59
def prefixEnd_7747458 : Nat := 4983230072969 + 3 ^ 40 * 7747458 * 2
def baseEnd_7747458 : Nat := 1819007683823070081685

theorem tailTrace_7747458 : CollatzResearch.WordTrace tailWord_7747458 prefixEnd_7747458 1819007683823070081685 := by
  unfold tailWord_7747458
  simp only [CollatzResearch.WordTrace]
  refine ⟨70643251891572575332330757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188382005044193534219548685 70643251891572575332330757)
  ·
    refine ⟨13245609729669857874812017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70643251891572575332330757 13245609729669857874812017)
    ·
      refine ⟨9934207297252393406109013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13245609729669857874812017 9934207297252393406109013)
      ·
        refine ⟨1819007683823070081685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 9934207297252393406109013 1819007683823070081685)
        ·
          rfl

theorem cell23_7747458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 14].length) (baseStart_7747458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747458 prefixEnd_7747458 := by exact prefixLift 7747458
  have htrace : WordTrace (prefixWord ++ tailWord_7747458) baseStart_7747458 baseEnd_7747458 := by
    simpa [prefixWord, tailWord_7747458, baseEnd_7747458] using wordTrace_append hprefix tailTrace_7747458
  have hstable : (prefixWord ++ tailWord_7747458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747458).length < 2 ^ (prefixWord ++ tailWord_7747458).sum := by decide
  have hdescent : baseEnd_7747458 < baseStart_7747458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747463 : List Nat := [1, 1, 4, 2, 5, 1, 2, 2, 1, 1, 3]
def baseStart_7747463 : Nat := 118140960795 + 7747463 * 2 ^ 59
def prefixEnd_7747463 : Nat := 4983230072969 + 3 ^ 40 * 7747463 * 2
def baseEnd_7747463 : Nat := 3978172371924326749082573

theorem tailTrace_7747463 : CollatzResearch.WordTrace tailWord_7747463 prefixEnd_7747463 3978172371924326749082573 := by
  unfold tailWord_7747463
  simp only [CollatzResearch.WordTrace]
  refine ⟨282573189931272187183255043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188382126620848124788836695 282573189931272187183255043)
  ·
    refine ⟨423859784896908280774882565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282573189931272187183255043 423859784896908280774882565)
    ·
      refine ⟨79473709668170302645290481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 423859784896908280774882565 79473709668170302645290481)
      ·
        refine ⟨59605282251127726983967861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79473709668170302645290481 59605282251127726983967861)
        ·
          refine ⟨5587995211043224404746987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59605282251127726983967861 5587995211043224404746987)
          ·
            refine ⟨8381992816564836607120481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5587995211043224404746987 8381992816564836607120481)
            ·
              refine ⟨6286494612423627455340361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8381992816564836607120481 6286494612423627455340361)
              ·
                refine ⟨4714870959317720591505271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6286494612423627455340361 4714870959317720591505271)
                ·
                  refine ⟨7072306438976580887257907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4714870959317720591505271 7072306438976580887257907)
                  ·
                    refine ⟨10608459658464871330886861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7072306438976580887257907 10608459658464871330886861)
                    ·
                      refine ⟨3978172371924326749082573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10608459658464871330886861 3978172371924326749082573)
                      ·
                        rfl

theorem cell23_7747463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_7747463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747463 prefixEnd_7747463 := by exact prefixLift 7747463
  have htrace : WordTrace (prefixWord ++ tailWord_7747463) baseStart_7747463 baseEnd_7747463 := by
    simpa [prefixWord, tailWord_7747463, baseEnd_7747463] using wordTrace_append hprefix tailTrace_7747463
  have hstable : (prefixWord ++ tailWord_7747463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747463).length < 2 ^ (prefixWord ++ tailWord_7747463).sum := by decide
  have hdescent : baseEnd_7747463 < baseStart_7747463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747468 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 5, 3, 3]
def baseStart_7747468 : Nat := 118140960795 + 7747468 * 2 ^ 59
def prefixEnd_7747468 : Nat := 4983230072969 + 3 ^ 40 * 7747468 * 2
def baseEnd_7747468 : Nat := 3978174939327599229520049

theorem tailTrace_7747468 : CollatzResearch.WordTrace tailWord_7747468 prefixEnd_7747468 3978174939327599229520049 := by
  unfold tailWord_7747468
  simp only [CollatzResearch.WordTrace]
  refine ⟨141286686148127036518593529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188382248197502715358124705 141286686148127036518593529)
  ·
    refine ⟨105965014611095277388945147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141286686148127036518593529 105965014611095277388945147)
    ·
      refine ⟨158947521916642916083417721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105965014611095277388945147 158947521916642916083417721)
      ·
        refine ⟨119210641437482187062563291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158947521916642916083417721 119210641437482187062563291)
        ·
          refine ⟨178815962156223280593844937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119210641437482187062563291 178815962156223280593844937)
          ·
            refine ⟨134111971617167460445383703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178815962156223280593844937 134111971617167460445383703)
            ·
              refine ⟨201167957425751190668075555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134111971617167460445383703 201167957425751190668075555)
              ·
                refine ⟨301751936138626786002113333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201167957425751190668075555 301751936138626786002113333)
                ·
                  refine ⟨28289244012996261187698125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 301751936138626786002113333 28289244012996261187698125)
                  ·
                    refine ⟨10608466504873597945386797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28289244012996261187698125 10608466504873597945386797)
                    ·
                      refine ⟨3978174939327599229520049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10608466504873597945386797 3978174939327599229520049)
                      ·
                        rfl

theorem cell23_7747468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_7747468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747468 prefixEnd_7747468 := by exact prefixLift 7747468
  have htrace : WordTrace (prefixWord ++ tailWord_7747468) baseStart_7747468 baseEnd_7747468 := by
    simpa [prefixWord, tailWord_7747468, baseEnd_7747468] using wordTrace_append hprefix tailTrace_7747468
  have hstable : (prefixWord ++ tailWord_7747468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747468).length < 2 ^ (prefixWord ++ tailWord_7747468).sum := by decide
  have hdescent : baseEnd_7747468 < baseStart_7747468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747485 : List Nat := [1, 4, 2, 1, 2, 2, 1, 3, 1, 3, 3]
def baseStart_7747485 : Nat := 118140960795 + 7747485 * 2 ^ 59
def prefixEnd_7747485 : Nat := 4983230072969 + 3 ^ 40 * 7747485 * 2
def baseEnd_7747485 : Nat := 3978183668498725663007471

theorem tailTrace_7747485 : CollatzResearch.WordTrace tailWord_7747485 prefixEnd_7747485 3978183668498725663007471 := by
  unfold tailWord_7747485
  simp only [CollatzResearch.WordTrace]
  refine ⟨282573992337192484940555909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188382661558128323293703939 282573992337192484940555909)
  ·
    refine ⟨52982623563223590926354233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282573992337192484940555909 52982623563223590926354233)
    ·
      refine ⟨39736967672417693194765675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52982623563223590926354233 39736967672417693194765675)
      ·
        refine ⟨59605451508626539792148513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39736967672417693194765675 59605451508626539792148513)
        ·
          refine ⟨44704088631469904844111385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59605451508626539792148513 44704088631469904844111385)
          ·
            refine ⟨33528066473602428633083539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44704088631469904844111385 33528066473602428633083539)
            ·
              refine ⟨50292099710403642949625309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33528066473602428633083539 50292099710403642949625309)
              ·
                refine ⟨18859537391401366106109491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50292099710403642949625309 18859537391401366106109491)
                ·
                  refine ⟨28289306087102049159164237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18859537391401366106109491 28289306087102049159164237)
                  ·
                    refine ⟨10608489782663268434686589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28289306087102049159164237 10608489782663268434686589)
                    ·
                      refine ⟨3978183668498725663007471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10608489782663268434686589 3978183668498725663007471)
                      ·
                        rfl

theorem cell23_7747485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_7747485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747485 prefixEnd_7747485 := by exact prefixLift 7747485
  have htrace : WordTrace (prefixWord ++ tailWord_7747485) baseStart_7747485 baseEnd_7747485 := by
    simpa [prefixWord, tailWord_7747485, baseEnd_7747485] using wordTrace_append hprefix tailTrace_7747485
  have hstable : (prefixWord ++ tailWord_7747485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747485).length < 2 ^ (prefixWord ++ tailWord_7747485).sum := by decide
  have hdescent : baseEnd_7747485 < baseStart_7747485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747512 : List Nat := [2, 1, 2, 1, 2, 3, 3, 3, 1, 3, 2]
def baseStart_7747512 : Nat := 118140960795 + 7747512 * 2 ^ 59
def prefixEnd_7747512 : Nat := 4983230072969 + 3 ^ 40 * 7747512 * 2
def baseEnd_7747512 : Nat := 3978197532476397057369847

theorem tailTrace_7747512 : CollatzResearch.WordTrace tailWord_7747512 prefixEnd_7747512 3978197532476397057369847 := by
  unfold tailWord_7747512
  simp only [CollatzResearch.WordTrace]
  refine ⟨141287488554047334275894395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188383318072063112367859193 141287488554047334275894395)
  ·
    refine ⟨211931232831071001413841593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141287488554047334275894395 211931232831071001413841593)
    ·
      refine ⟨158948424623303251060381195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211931232831071001413841593 158948424623303251060381195)
      ·
        refine ⟨238422636934954876590571793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158948424623303251060381195 238422636934954876590571793)
        ·
          refine ⟨178816977701216157442928845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238422636934954876590571793 178816977701216157442928845)
          ·
            refine ⟨67056366637956059041098317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178816977701216157442928845 67056366637956059041098317)
            ·
              refine ⟨25146137489233522140411869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67056366637956059041098317 25146137489233522140411869)
              ·
                refine ⟨9429801558462570802654451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25146137489233522140411869 9429801558462570802654451)
                ·
                  refine ⟨14144702337693856203981677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9429801558462570802654451 14144702337693856203981677)
                  ·
                    refine ⟨5304263376635196076493129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14144702337693856203981677 5304263376635196076493129)
                    ·
                      refine ⟨3978197532476397057369847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5304263376635196076493129 3978197532476397057369847)
                      ·
                        rfl

theorem cell23_7747512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 1, 3, 2].length) (baseStart_7747512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747512 prefixEnd_7747512 := by exact prefixLift 7747512
  have htrace : WordTrace (prefixWord ++ tailWord_7747512) baseStart_7747512 baseEnd_7747512 := by
    simpa [prefixWord, tailWord_7747512, baseEnd_7747512] using wordTrace_append hprefix tailTrace_7747512
  have hstable : (prefixWord ++ tailWord_7747512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747512).length < 2 ^ (prefixWord ++ tailWord_7747512).sum := by decide
  have hdescent : baseEnd_7747512 < baseStart_7747512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747582 : List Nat := [4, 2, 2, 2, 1, 1, 3, 1, 7]
def baseStart_7747582 : Nat := 118140960795 + 7747582 * 2 ^ 59
def prefixEnd_7747582 : Nat := 4983230072969 + 3 ^ 40 * 7747582 * 2
def baseEnd_7747582 : Nat := 442025941791356864832725

theorem tailTrace_7747582 : CollatzResearch.WordTrace tailWord_7747582 prefixEnd_7747582 442025941791356864832725 := by
  unfold tailWord_7747582
  simp only [CollatzResearch.WordTrace]
  refine ⟨35322191277230133813354625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188385020145227380337891333 35322191277230133813354625)
  ·
    refine ⟨26491643457922600360015969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35322191277230133813354625 26491643457922600360015969)
    ·
      refine ⟨19868732593441950270011977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26491643457922600360015969 19868732593441950270011977)
      ·
        refine ⟨14901549445081462702508983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19868732593441950270011977 14901549445081462702508983)
        ·
          refine ⟨22352324167622194053763475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14901549445081462702508983 22352324167622194053763475)
          ·
            refine ⟨33528486251433291080645213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22352324167622194053763475 33528486251433291080645213)
            ·
              refine ⟨12573182344287484155241955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33528486251433291080645213 12573182344287484155241955)
              ·
                refine ⟨18859773516431226232862933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12573182344287484155241955 18859773516431226232862933)
                ·
                  refine ⟨442025941791356864832725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18859773516431226232862933 442025941791356864832725)
                  ·
                    rfl

theorem cell23_7747582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_7747582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747582 prefixEnd_7747582 := by exact prefixLift 7747582
  have htrace : WordTrace (prefixWord ++ tailWord_7747582) baseStart_7747582 baseEnd_7747582 := by
    simpa [prefixWord, tailWord_7747582, baseEnd_7747582] using wordTrace_append hprefix tailTrace_7747582
  have hstable : (prefixWord ++ tailWord_7747582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747582).length < 2 ^ (prefixWord ++ tailWord_7747582).sum := by decide
  have hdescent : baseEnd_7747582 < baseStart_7747582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747597 : List Nat := [1, 7, 1, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_7747597 : Nat := 118140960795 + 7747597 * 2 ^ 59
def prefixEnd_7747597 : Nat := 4983230072969 + 3 ^ 40 * 7747597 * 2
def baseEnd_7747597 : Nat := 3978241178332029224806957

theorem tailTrace_7747597 : CollatzResearch.WordTrace tailWord_7747597 prefixEnd_7747597 3978241178332029224806957 := by
  unfold tailWord_7747597
  simp only [CollatzResearch.WordTrace]
  refine ⟨282578077312786728068633045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188385384875191152045755363 282578077312786728068633045)
  ·
    refine ⟨6622923687018438939108587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 282578077312786728068633045 6622923687018438939108587)
    ·
      refine ⟨9934385530527658408662881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6622923687018438939108587 9934385530527658408662881)
      ·
        refine ⟨7450789147895743806497161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9934385530527658408662881 7450789147895743806497161)
        ·
          refine ⟨5588091860921807854872871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7450789147895743806497161 5588091860921807854872871)
          ·
            refine ⟨8382137791382711782309307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5588091860921807854872871 8382137791382711782309307)
            ·
              refine ⟨12573206687074067673463961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8382137791382711782309307 12573206687074067673463961)
              ·
                refine ⟨9429905015305550755097971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12573206687074067673463961 9429905015305550755097971)
                ·
                  refine ⟨14144857522958326132646957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9429905015305550755097971 14144857522958326132646957)
                  ·
                    refine ⟨5304321571109372299742609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14144857522958326132646957 5304321571109372299742609)
                    ·
                      refine ⟨3978241178332029224806957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5304321571109372299742609 3978241178332029224806957)
                      ·
                        rfl

theorem cell23_7747597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_7747597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747597 prefixEnd_7747597 := by exact prefixLift 7747597
  have htrace : WordTrace (prefixWord ++ tailWord_7747597) baseStart_7747597 baseEnd_7747597 := by
    simpa [prefixWord, tailWord_7747597, baseEnd_7747597] using wordTrace_append hprefix tailTrace_7747597
  have hstable : (prefixWord ++ tailWord_7747597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747597).length < 2 ^ (prefixWord ++ tailWord_7747597).sum := by decide
  have hdescent : baseEnd_7747597 < baseStart_7747597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747612 : List Nat := [2, 2, 3, 1, 3, 2, 2, 1, 2, 5]
def baseStart_7747612 : Nat := 118140960795 + 7747612 * 2 ^ 59
def prefixEnd_7747612 : Nat := 4983230072969 + 3 ^ 40 * 7747612 * 2
def baseEnd_7747612 : Nat := 1326082960180615555373129

theorem tailTrace_7747612 : CollatzResearch.WordTrace tailWord_7747612 prefixEnd_7747612 1326082960180615555373129 := by
  unfold tailWord_7747612
  simp only [CollatzResearch.WordTrace]
  refine ⟨141289312203866192815214545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188385749605154923753619393 141289312203866192815214545)
  ·
    refine ⟨105966984152899644611410909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141289312203866192815214545 105966984152899644611410909)
    ·
      refine ⟨39737619057337366729279091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105966984152899644611410909 39737619057337366729279091)
      ·
        refine ⟨59606428586006050093918637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39737619057337366729279091 59606428586006050093918637)
        ·
          refine ⟨22352410719752268785219489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59606428586006050093918637 22352410719752268785219489)
          ·
            refine ⟨16764308039814201588914617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22352410719752268785219489 16764308039814201588914617)
            ·
              refine ⟨12573231029860651191685963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16764308039814201588914617 12573231029860651191685963)
              ·
                refine ⟨18859846544790976787528945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12573231029860651191685963 18859846544790976787528945)
                ·
                  refine ⟨14144884908593232590646709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18859846544790976787528945 14144884908593232590646709)
                  ·
                    refine ⟨1326082960180615555373129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14144884908593232590646709 1326082960180615555373129)
                    ·
                      rfl

theorem cell23_7747612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_7747612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747612 prefixEnd_7747612 := by exact prefixLift 7747612
  have htrace : WordTrace (prefixWord ++ tailWord_7747612) baseStart_7747612 baseEnd_7747612 := by
    simpa [prefixWord, tailWord_7747612, baseEnd_7747612] using wordTrace_append hprefix tailTrace_7747612
  have hstable : (prefixWord ++ tailWord_7747612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747612).length < 2 ^ (prefixWord ++ tailWord_7747612).sum := by decide
  have hdescent : baseEnd_7747612 < baseStart_7747612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747649 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 2, 4, 2]
def baseStart_7747649 : Nat := 118140960795 + 7747649 * 2 ^ 59
def prefixEnd_7747649 : Nat := 4983230072969 + 3 ^ 40 * 7747649 * 2
def baseEnd_7747649 : Nat := 3978267879326063021356717

theorem tailTrace_7747649 : CollatzResearch.WordTrace tailWord_7747649 prefixEnd_7747649 3978267879326063021356717 := by
  unfold tailWord_7747649
  simp only [CollatzResearch.WordTrace]
  refine ⟨282579973908598340949526001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188386649272398893966350667 282579973908598340949526001)
  ·
    refine ⟨211934980431448755712144501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282579973908598340949526001 211934980431448755712144501)
    ·
      refine ⟨19868904415448320848013547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211934980431448755712144501 19868904415448320848013547)
      ·
        refine ⟨29803356623172481272020321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19868904415448320848013547 29803356623172481272020321)
        ·
          refine ⟨22352517467379360954015241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29803356623172481272020321 22352517467379360954015241)
          ·
            refine ⟨16764388100534520715511431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22352517467379360954015241 16764388100534520715511431)
            ·
              refine ⟨25146582150801781073267147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16764388100534520715511431 25146582150801781073267147)
              ·
                refine ⟨37719873226202671609900721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25146582150801781073267147 37719873226202671609900721)
                ·
                  refine ⟨28289904919652003707425541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37719873226202671609900721 28289904919652003707425541)
                  ·
                    refine ⟨5304357172434750695142289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28289904919652003707425541 5304357172434750695142289)
                    ·
                      refine ⟨3978267879326063021356717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5304357172434750695142289 3978267879326063021356717)
                      ·
                        rfl

theorem cell23_7747649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_7747649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747649 prefixEnd_7747649 := by exact prefixLift 7747649
  have htrace : WordTrace (prefixWord ++ tailWord_7747649) baseStart_7747649 baseEnd_7747649 := by
    simpa [prefixWord, tailWord_7747649, baseEnd_7747649] using wordTrace_append hprefix tailTrace_7747649
  have hstable : (prefixWord ++ tailWord_7747649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747649).length < 2 ^ (prefixWord ++ tailWord_7747649).sum := by decide
  have hdescent : baseEnd_7747649 < baseStart_7747649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747655 : List Nat := [1, 1, 4, 1, 3, 1, 1, 5, 6]
def baseStart_7747655 : Nat := 118140960795 + 7747655 * 2 ^ 59
def prefixEnd_7747655 : Nat := 4983230072969 + 3 ^ 40 * 7747655 * 2
def baseEnd_7747655 : Nat := 442030106689998888653521

theorem tailTrace_7747655 : CollatzResearch.WordTrace tailWord_7747655 prefixEnd_7747655 442030106689998888653521 := by
  unfold tailWord_7747655
  simp only [CollatzResearch.WordTrace]
  refine ⟨282580192746576603974244419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188386795164384402649496279 282580192746576603974244419)
  ·
    refine ⟨423870289119864905961366629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282580192746576603974244419 423870289119864905961366629)
    ·
      refine ⟨79475679209974669867756243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 423870289119864905961366629 79475679209974669867756243)
      ·
        refine ⟨119213518814962004801634365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79475679209974669867756243 119213518814962004801634365)
        ·
          refine ⟨44705069555610751800612887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119213518814962004801634365 44705069555610751800612887)
          ·
            refine ⟨67057604333416127700919331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44705069555610751800612887 67057604333416127700919331)
            ·
              refine ⟨100586406500124191551378997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67057604333416127700919331 100586406500124191551378997)
              ·
                refine ⟨9429975609386642957941781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100586406500124191551378997 9429975609386642957941781)
                ·
                  refine ⟨442030106689998888653521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9429975609386642957941781 442030106689998888653521)
                  ·
                    rfl

theorem cell23_7747655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 6].length) (baseStart_7747655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747655 prefixEnd_7747655 := by exact prefixLift 7747655
  have htrace : WordTrace (prefixWord ++ tailWord_7747655) baseStart_7747655 baseEnd_7747655 := by
    simpa [prefixWord, tailWord_7747655, baseEnd_7747655] using wordTrace_append hprefix tailTrace_7747655
  have hstable : (prefixWord ++ tailWord_7747655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747655).length < 2 ^ (prefixWord ++ tailWord_7747655).sum := by decide
  have hdescent : baseEnd_7747655 < baseStart_7747655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747666 : List Nat := [3, 2, 2, 1, 5, 1, 1, 1, 2, 1, 4]
def baseStart_7747666 : Nat := 118140960795 + 7747666 * 2 ^ 59
def prefixEnd_7747666 : Nat := 4983230072969 + 3 ^ 40 * 7747666 * 2
def baseEnd_7747666 : Nat := 3978276608497189454844139

theorem tailTrace_7747666 : CollatzResearch.WordTrace tailWord_7747666 prefixEnd_7747666 3978276608497189454844139 := by
  unfold tailWord_7747666
  simp only [CollatzResearch.WordTrace]
  refine ⟨70645148487384188213223713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188387062633024501901929901 70645148487384188213223713)
  ·
    refine ⟨52983861365538141159917785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70645148487384188213223713 52983861365538141159917785)
    ·
      refine ⟨39737896024153605869938339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52983861365538141159917785 39737896024153605869938339)
      ·
        refine ⟨59606844036230408804907509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39737896024153605869938339 59606844036230408804907509)
        ·
          refine ⟨5588141628396600825460079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59606844036230408804907509 5588141628396600825460079)
          ·
            refine ⟨8382212442594901238190119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5588141628396600825460079 8382212442594901238190119)
            ·
              refine ⟨12573318663892351857285179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8382212442594901238190119 12573318663892351857285179)
              ·
                refine ⟨18859977995838527785927769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12573318663892351857285179 18859977995838527785927769)
                ·
                  refine ⟨14144983496878895839445827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18859977995838527785927769 14144983496878895839445827)
                  ·
                    refine ⟨21217475245318343759168741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14144983496878895839445827 21217475245318343759168741)
                    ·
                      refine ⟨3978276608497189454844139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21217475245318343759168741 3978276608497189454844139)
                      ·
                        rfl

theorem cell23_7747666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_7747666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747666 prefixEnd_7747666 := by exact prefixLift 7747666
  have htrace : WordTrace (prefixWord ++ tailWord_7747666) baseStart_7747666 baseEnd_7747666 := by
    simpa [prefixWord, tailWord_7747666, baseEnd_7747666] using wordTrace_append hprefix tailTrace_7747666
  have hstable : (prefixWord ++ tailWord_7747666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747666).length < 2 ^ (prefixWord ++ tailWord_7747666).sum := by decide
  have hdescent : baseEnd_7747666 < baseStart_7747666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747669 : List Nat := [1, 3, 2, 2, 1, 5, 1, 1, 2, 2, 3]
def baseStart_7747669 : Nat := 118140960795 + 7747669 * 2 ^ 59
def prefixEnd_7747669 : Nat := 4983230072969 + 3 ^ 40 * 7747669 * 2
def baseEnd_7747669 : Nat := 3978278148939152943106625

theorem tailTrace_7747669 : CollatzResearch.WordTrace tailWord_7747669 prefixEnd_7747669 3978278148939152943106625 := by
  unfold tailWord_7747669
  simp only [CollatzResearch.WordTrace]
  refine ⟨282580703368525884365254061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188387135579017256243502707 282580703368525884365254061)
  ·
    refine ⟨105967763763197206636970273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282580703368525884365254061 105967763763197206636970273)
    ·
      refine ⟨79475822822397904977727705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105967763763197206636970273 79475822822397904977727705)
      ·
        refine ⟨59606867116798428733295779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79475822822397904977727705 59606867116798428733295779)
        ·
          refine ⟨89410300675197643099943669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59606867116798428733295779 89410300675197643099943669)
          ·
            refine ⟨8382215688299779040619719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89410300675197643099943669 8382215688299779040619719)
            ·
              refine ⟨12573323532449668560929579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8382215688299779040619719 12573323532449668560929579)
              ·
                refine ⟨18859985298674502841394369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12573323532449668560929579 18859985298674502841394369)
                ·
                  refine ⟨14144988974005877131045777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18859985298674502841394369 14144988974005877131045777)
                  ·
                    refine ⟨10608741730504407848284333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14144988974005877131045777 10608741730504407848284333)
                    ·
                      refine ⟨3978278148939152943106625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10608741730504407848284333 3978278148939152943106625)
                      ·
                        rfl

theorem cell23_7747669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_7747669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747669 prefixEnd_7747669 := by exact prefixLift 7747669
  have htrace : WordTrace (prefixWord ++ tailWord_7747669) baseStart_7747669 baseEnd_7747669 := by
    simpa [prefixWord, tailWord_7747669, baseEnd_7747669] using wordTrace_append hprefix tailTrace_7747669
  have hstable : (prefixWord ++ tailWord_7747669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747669).length < 2 ^ (prefixWord ++ tailWord_7747669).sum := by decide
  have hdescent : baseEnd_7747669 < baseStart_7747669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747676 : List Nat := [2, 2, 4, 1, 1, 3, 2, 3, 1, 4]
def baseStart_7747676 : Nat := 118140960795 + 7747676 * 2 ^ 59
def prefixEnd_7747676 : Nat := 4983230072969 + 3 ^ 40 * 7747676 * 2
def baseEnd_7747676 : Nat := 1326093914434578138573031

theorem tailTrace_7747676 : CollatzResearch.WordTrace tailWord_7747676 prefixEnd_7747676 1326093914434578138573031 := by
  unfold tailWord_7747676
  simp only [CollatzResearch.WordTrace]
  refine ⟨141290479339750262280379441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188387305786333683040505921 141290479339750262280379441)
  ·
    refine ⟨105967859504812696710284581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141290479339750262280379441 105967859504812696710284581)
    ·
      refine ⟨19868973657152380633178359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105967859504812696710284581 19868973657152380633178359)
      ·
        refine ⟨29803460485728570949767539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19868973657152380633178359 29803460485728570949767539)
        ·
          refine ⟨44705190728592856424651309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29803460485728570949767539 44705190728592856424651309)
          ·
            refine ⟨16764446523222321159244241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44705190728592856424651309 16764446523222321159244241)
            ·
              refine ⟨12573334892416740869433181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16764446523222321159244241 12573334892416740869433181)
              ·
                refine ⟨4715000584656277826037443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12573334892416740869433181 4715000584656277826037443)
                ·
                  refine ⟨7072500876984416739056165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715000584656277826037443 7072500876984416739056165)
                  ·
                    refine ⟨1326093914434578138573031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7072500876984416739056165 1326093914434578138573031)
                    ·
                      rfl

theorem cell23_7747676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_7747676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747676 prefixEnd_7747676 := by exact prefixLift 7747676
  have htrace : WordTrace (prefixWord ++ tailWord_7747676) baseStart_7747676 baseEnd_7747676 := by
    simpa [prefixWord, tailWord_7747676, baseEnd_7747676] using wordTrace_append hprefix tailTrace_7747676
  have hstable : (prefixWord ++ tailWord_7747676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747676).length < 2 ^ (prefixWord ++ tailWord_7747676).sum := by decide
  have hdescent : baseEnd_7747676 < baseStart_7747676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747745 : List Nat := [1, 2, 3, 3, 1, 2, 11]
def baseStart_7747745 : Nat := 118140960795 + 7747745 * 2 ^ 59
def prefixEnd_7747745 : Nat := 4983230072969 + 3 ^ 40 * 7747745 * 2
def baseEnd_7747745 : Nat := 49115026832949316614275

theorem tailTrace_7747745 : CollatzResearch.WordTrace tailWord_7747745 prefixEnd_7747745 49115026832949316614275 := by
  unfold tailWord_7747745
  simp only [CollatzResearch.WordTrace]
  refine ⟨282583475316250549345020689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188388983544167032896680459 282583475316250549345020689)
  ·
    refine ⟨211937606487187912008765517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282583475316250549345020689 211937606487187912008765517)
    ·
      refine ⟨79476602432695467003287069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211937606487187912008765517 79476602432695467003287069)
      ·
        refine ⟨29803725912260800126232651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79476602432695467003287069 29803725912260800126232651)
        ·
          refine ⟨44705588868391200189348977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29803725912260800126232651 44705588868391200189348977)
          ·
            refine ⟨33529191651293400142011733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44705588868391200189348977 33529191651293400142011733)
            ·
              refine ⟨49115026832949316614275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 33529191651293400142011733 49115026832949316614275)
              ·
                rfl

theorem cell23_7747745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 11].length) (baseStart_7747745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747745 prefixEnd_7747745 := by exact prefixLift 7747745
  have htrace : WordTrace (prefixWord ++ tailWord_7747745) baseStart_7747745 baseEnd_7747745 := by
    simpa [prefixWord, tailWord_7747745, baseEnd_7747745] using wordTrace_append hprefix tailTrace_7747745
  have hstable : (prefixWord ++ tailWord_7747745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747745).length < 2 ^ (prefixWord ++ tailWord_7747745).sum := by decide
  have hdescent : baseEnd_7747745 < baseStart_7747745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747776 : List Nat := [2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 3]
def baseStart_7747776 : Nat := 118140960795 + 7747776 * 2 ^ 59
def prefixEnd_7747776 : Nat := 4983230072969 + 3 ^ 40 * 7747776 * 2
def baseEnd_7747776 : Nat := 3978333091369184024468633

theorem tailTrace_7747776 : CollatzResearch.WordTrace tailWord_7747776 prefixEnd_7747776 3978333091369184024468633 := by
  unfold tailWord_7747776
  simp only [CollatzResearch.WordTrace]
  refine ⟨141292302989569120819699591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188389737319425494426266121 141292302989569120819699591)
  ·
    refine ⟨211938454484353681229549387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141292302989569120819699591 211938454484353681229549387)
    ·
      refine ⟨317907681726530521844324081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211938454484353681229549387 317907681726530521844324081)
      ·
        refine ⟨238430761294897891383243061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317907681726530521844324081 238430761294897891383243061)
        ·
          refine ⟨22352883871396677317179037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 238430761294897891383243061 22352883871396677317179037)
          ·
            refine ⟨8382331451773753993942139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22352883871396677317179037 8382331451773753993942139)
            ·
              refine ⟨12573497177660630990913209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8382331451773753993942139 12573497177660630990913209)
              ·
                refine ⟨9430122883245473243184907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12573497177660630990913209 9430122883245473243184907)
                ·
                  refine ⟨14145184324868209864777361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9430122883245473243184907 14145184324868209864777361)
                  ·
                    refine ⟨10608888243651157398583021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14145184324868209864777361 10608888243651157398583021)
                    ·
                      refine ⟨3978333091369184024468633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10608888243651157398583021 3978333091369184024468633)
                      ·
                        rfl

theorem cell23_7747776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 3].length) (baseStart_7747776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747776 prefixEnd_7747776 := by exact prefixLift 7747776
  have htrace : WordTrace (prefixWord ++ tailWord_7747776) baseStart_7747776 baseEnd_7747776 := by
    simpa [prefixWord, tailWord_7747776, baseEnd_7747776] using wordTrace_append hprefix tailTrace_7747776
  have hstable : (prefixWord ++ tailWord_7747776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747776).length < 2 ^ (prefixWord ++ tailWord_7747776).sum := by decide
  have hdescent : baseEnd_7747776 < baseStart_7747776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747785 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 2, 2, 5]
def baseStart_7747785 : Nat := 118140960795 + 7747785 * 2 ^ 59
def prefixEnd_7747785 : Nat := 4983230072969 + 3 ^ 40 * 7747785 * 2
def baseEnd_7747785 : Nat := 3978337712695074489256091

theorem tailTrace_7747785 : CollatzResearch.WordTrace tailWord_7747785 prefixEnd_7747785 3978337712695074489256091 := by
  unfold tailWord_7747785
  simp only [CollatzResearch.WordTrace]
  refine ⟨282584934236105636176476809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188389956157403757450984539 282584934236105636176476809)
  ·
    refine ⟨211938700677079227132357607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282584934236105636176476809 211938700677079227132357607)
    ·
      refine ⟨317908051015618840698536411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211938700677079227132357607 317908051015618840698536411)
      ·
        refine ⟨476862076523428261047804617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317908051015618840698536411 476862076523428261047804617)
        ·
          refine ⟨357646557392571195785853463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476862076523428261047804617 357646557392571195785853463)
          ·
            refine ⟨536469836088856793678780195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357646557392571195785853463 536469836088856793678780195)
            ·
              refine ⟨804704754133285190518170293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536469836088856793678780195 804704754133285190518170293)
              ·
                refine ⟨75441070699995486611078465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 804704754133285190518170293 75441070699995486611078465)
                ·
                  refine ⟨56580803024996614958308849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75441070699995486611078465 56580803024996614958308849)
                  ·
                    refine ⟨42435602268747461218731637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56580803024996614958308849 42435602268747461218731637)
                    ·
                      refine ⟨3978337712695074489256091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42435602268747461218731637 3978337712695074489256091)
                      ·
                        rfl

theorem cell23_7747785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_7747785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747785 prefixEnd_7747785 := by exact prefixLift 7747785
  have htrace : WordTrace (prefixWord ++ tailWord_7747785) baseStart_7747785 baseEnd_7747785 := by
    simpa [prefixWord, tailWord_7747785, baseEnd_7747785] using wordTrace_append hprefix tailTrace_7747785
  have hstable : (prefixWord ++ tailWord_7747785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747785).length < 2 ^ (prefixWord ++ tailWord_7747785).sum := by decide
  have hdescent : baseEnd_7747785 < baseStart_7747785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747795 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 4]
def baseStart_7747795 : Nat := 118140960795 + 7747795 * 2 ^ 59
def prefixEnd_7747795 : Nat := 4983230072969 + 3 ^ 40 * 7747795 * 2
def baseEnd_7747795 : Nat := 3978342847501619450131045

theorem tailTrace_7747795 : CollatzResearch.WordTrace tailWord_7747795 prefixEnd_7747795 3978342847501619450131045 := by
  unfold tailWord_7747795
  simp only [CollatzResearch.WordTrace]
  refine ⟨282585298966069407884340839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188390199310712938589560559 282585298966069407884340839)
  ·
    refine ⟨423877948449104111826511259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282585298966069407884340839 423877948449104111826511259)
    ·
      refine ⟨635816922673656167739766889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423877948449104111826511259 635816922673656167739766889)
      ·
        refine ⟨476862692005242125804825167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635816922673656167739766889 476862692005242125804825167)
        ·
          refine ⟨715294038007863188707237751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476862692005242125804825167 715294038007863188707237751)
          ·
            refine ⟨1072941057011794783060856627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715294038007863188707237751 1072941057011794783060856627)
            ·
              refine ⟨1609411585517692174591284941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1072941057011794783060856627 1609411585517692174591284941)
              ·
                refine ⟨603529344569134565471731853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1609411585517692174591284941 603529344569134565471731853)
                ·
                  refine ⟨226323504213425462051899445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 603529344569134565471731853 226323504213425462051899445)
                  ·
                    refine ⟨21217828520008637067365573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 226323504213425462051899445 21217828520008637067365573)
                    ·
                      refine ⟨3978342847501619450131045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21217828520008637067365573 3978342847501619450131045)
                      ·
                        rfl

theorem cell23_7747795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 4].length) (baseStart_7747795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747795 prefixEnd_7747795 := by exact prefixLift 7747795
  have htrace : WordTrace (prefixWord ++ tailWord_7747795) baseStart_7747795 baseEnd_7747795 := by
    simpa [prefixWord, tailWord_7747795, baseEnd_7747795] using wordTrace_append hprefix tailTrace_7747795
  have hstable : (prefixWord ++ tailWord_7747795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747795).length < 2 ^ (prefixWord ++ tailWord_7747795).sum := by decide
  have hdescent : baseEnd_7747795 < baseStart_7747795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747863 : List Nat := [1, 1, 3, 4, 1, 2, 3, 2, 2, 2, 2]
def baseStart_7747863 : Nat := 118140960795 + 7747863 * 2 ^ 59
def prefixEnd_7747863 : Nat := 4983230072969 + 3 ^ 40 * 7747863 * 2
def baseEnd_7747863 : Nat := 3978377764186125184080733

theorem tailTrace_7747863 : CollatzResearch.WordTrace tailWord_7747863 prefixEnd_7747863 3978377764186125184080733 := by
  unfold tailWord_7747863
  simp only [CollatzResearch.WordTrace]
  refine ⟨282587779129823055497816243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188391852753215370331877495 282587779129823055497816243)
  ·
    refine ⟨423881668694734583246724365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282587779129823055497816243 423881668694734583246724365)
    ·
      refine ⟨158955625760525468717521637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423881668694734583246724365 158955625760525468717521637)
      ·
        refine ⟨29804179830098525384535307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158955625760525468717521637 29804179830098525384535307)
        ·
          refine ⟨44706269745147788076802961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29804179830098525384535307 44706269745147788076802961)
          ·
            refine ⟨33529702308860841057602221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44706269745147788076802961 33529702308860841057602221)
            ·
              refine ⟨12573638365822815396600833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33529702308860841057602221 12573638365822815396600833)
              ·
                refine ⟨9430228774367111547450625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12573638365822815396600833 9430228774367111547450625)
                ·
                  refine ⟨7072671580775333660587969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9430228774367111547450625 7072671580775333660587969)
                  ·
                    refine ⟨5304503685581500245440977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7072671580775333660587969 5304503685581500245440977)
                    ·
                      refine ⟨3978377764186125184080733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5304503685581500245440977 3978377764186125184080733)
                      ·
                        rfl

theorem cell23_7747863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_7747863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747863 prefixEnd_7747863 := by exact prefixLift 7747863
  have htrace : WordTrace (prefixWord ++ tailWord_7747863) baseStart_7747863 baseEnd_7747863 := by
    simpa [prefixWord, tailWord_7747863, baseEnd_7747863] using wordTrace_append hprefix tailTrace_7747863
  have hstable : (prefixWord ++ tailWord_7747863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747863).length < 2 ^ (prefixWord ++ tailWord_7747863).sum := by decide
  have hdescent : baseEnd_7747863 < baseStart_7747863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747880 : List Nat := [2, 1, 5, 1, 4, 1, 1, 1, 1, 4, 2]
def baseStart_7747880 : Nat := 118140960795 + 7747880 * 2 ^ 59
def prefixEnd_7747880 : Nat := 4983230072969 + 3 ^ 40 * 7747880 * 2
def baseEnd_7747880 : Nat := 3978386493357251617568155

theorem tailTrace_7747880 : CollatzResearch.WordTrace tailWord_7747880 prefixEnd_7747880 3978386493357251617568155 := by
  unfold tailWord_7747880
  simp only [CollatzResearch.WordTrace]
  refine ⟨141294199585380733700592547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188392266113840978267456729 141294199585380733700592547)
  ·
    refine ⟨211941299378071100550888821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141294199585380733700592547 211941299378071100550888821)
    ·
      refine ⟨19869496816694165676645827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211941299378071100550888821 19869496816694165676645827)
      ·
        refine ⟨29804245225041248514968741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19869496816694165676645827 29804245225041248514968741)
        ·
          refine ⟨5588295979695234096556639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29804245225041248514968741 5588295979695234096556639)
          ·
            refine ⟨8382443969542851144834959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5588295979695234096556639 8382443969542851144834959)
            ·
              refine ⟨12573665954314276717252439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8382443969542851144834959 12573665954314276717252439)
              ·
                refine ⟨18860498931471415075878659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12573665954314276717252439 18860498931471415075878659)
                ·
                  refine ⟨28290748397207122613817989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18860498931471415075878659 28290748397207122613817989)
                  ·
                    refine ⟨5304515324476335490090873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28290748397207122613817989 5304515324476335490090873)
                    ·
                      refine ⟨3978386493357251617568155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5304515324476335490090873 3978386493357251617568155)
                      ·
                        rfl

theorem cell23_7747880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_7747880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747880 prefixEnd_7747880 := by exact prefixLift 7747880
  have htrace : WordTrace (prefixWord ++ tailWord_7747880) baseStart_7747880 baseEnd_7747880 := by
    simpa [prefixWord, tailWord_7747880, baseEnd_7747880] using wordTrace_append hprefix tailTrace_7747880
  have hstable : (prefixWord ++ tailWord_7747880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747880).length < 2 ^ (prefixWord ++ tailWord_7747880).sum := by decide
  have hdescent : baseEnd_7747880 < baseStart_7747880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747919 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 2, 4, 2]
def baseStart_7747919 : Nat := 118140960795 + 7747919 * 2 ^ 59
def prefixEnd_7747919 : Nat := 4983230072969 + 3 ^ 40 * 7747919 * 2
def baseEnd_7747919 : Nat := 3978406519102776964980475

theorem tailTrace_7747919 : CollatzResearch.WordTrace tailWord_7747919 prefixEnd_7747919 3978406519102776964980475 := by
  unfold tailWord_7747919
  simp only [CollatzResearch.WordTrace]
  refine ⟨282589821617620177061854811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188393214411746784707903207 282589821617620177061854811)
  ·
    refine ⟨423884732426430265592782217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282589821617620177061854811 423884732426430265592782217)
    ·
      refine ⟨317913549319822699194586663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423884732426430265592782217 317913549319822699194586663)
      ·
        refine ⟨476870323979734048791879995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317913549319822699194586663 476870323979734048791879995)
        ·
          refine ⟨715305485969601073187819993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476870323979734048791879995 715305485969601073187819993)
          ·
            refine ⟨536479114477200804890864995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 715305485969601073187819993 536479114477200804890864995)
            ·
              refine ⟨804718671715801207336297493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536479114477200804890864995 804718671715801207336297493)
              ·
                refine ⟨37721187736678181593888945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 804718671715801207336297493 37721187736678181593888945)
                ·
                  refine ⟨28290890802508636195416709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37721187736678181593888945 28290890802508636195416709)
                  ·
                    refine ⟨5304542025470369286640633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28290890802508636195416709 5304542025470369286640633)
                    ·
                      refine ⟨3978406519102776964980475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5304542025470369286640633 3978406519102776964980475)
                      ·
                        rfl

theorem cell23_7747919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 4, 2].length) (baseStart_7747919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747919 prefixEnd_7747919 := by exact prefixLift 7747919
  have htrace : WordTrace (prefixWord ++ tailWord_7747919) baseStart_7747919 baseEnd_7747919 := by
    simpa [prefixWord, tailWord_7747919, baseEnd_7747919] using wordTrace_append hprefix tailTrace_7747919
  have hstable : (prefixWord ++ tailWord_7747919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747919).length < 2 ^ (prefixWord ++ tailWord_7747919).sum := by decide
  have hdescent : baseEnd_7747919 < baseStart_7747919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747939 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 3]
def baseStart_7747939 : Nat := 118140960795 + 7747939 * 2 ^ 59
def prefixEnd_7747939 : Nat := 4983230072969 + 3 ^ 40 * 7747939 * 2
def baseEnd_7747939 : Nat := 3978416788715866886730383

theorem tailTrace_7747939 : CollatzResearch.WordTrace tailWord_7747939 prefixEnd_7747939 3978416788715866886730383 := by
  unfold tailWord_7747939
  simp only [CollatzResearch.WordTrace]
  refine ⟨282590551077547720477582871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188393700718365146985055247 282590551077547720477582871)
  ·
    refine ⟨423885826616321580716374307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282590551077547720477582871 423885826616321580716374307)
    ·
      refine ⟨635828739924482371074561461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423885826616321580716374307 635828739924482371074561461)
      ·
        refine ⟨59608944367920222288240137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 635828739924482371074561461 59608944367920222288240137)
        ·
          refine ⟨44706708275940166716180103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59608944367920222288240137 44706708275940166716180103)
          ·
            refine ⟨67060062413910250074270155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44706708275940166716180103 67060062413910250074270155)
            ·
              refine ⟨100590093620865375111405233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67060062413910250074270155 100590093620865375111405233)
              ·
                refine ⟨75442570215649031333553925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100590093620865375111405233 75442570215649031333553925)
                ·
                  refine ⟨14145481915434193375041361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75442570215649031333553925 14145481915434193375041361)
                  ·
                    refine ⟨10609111436575645031281021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14145481915434193375041361 10609111436575645031281021)
                    ·
                      refine ⟨3978416788715866886730383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10609111436575645031281021 3978416788715866886730383)
                      ·
                        rfl

theorem cell23_7747939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_7747939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747939 prefixEnd_7747939 := by exact prefixLift 7747939
  have htrace : WordTrace (prefixWord ++ tailWord_7747939) baseStart_7747939 baseEnd_7747939 := by
    simpa [prefixWord, tailWord_7747939, baseEnd_7747939] using wordTrace_append hprefix tailTrace_7747939
  have hstable : (prefixWord ++ tailWord_7747939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747939).length < 2 ^ (prefixWord ++ tailWord_7747939).sum := by decide
  have hdescent : baseEnd_7747939 < baseStart_7747939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747980 : List Nat := [2, 2, 1, 2, 1, 6, 2, 2, 1, 4]
def baseStart_7747980 : Nat := 118140960795 + 7747980 * 2 ^ 59
def prefixEnd_7747980 : Nat := 4983230072969 + 3 ^ 40 * 7747980 * 2
def baseEnd_7747980 : Nat := 1326145947140900408772565

theorem tailTrace_7747980 : CollatzResearch.WordTrace tailWord_7747980 prefixEnd_7747980 1326145947140900408772565 := by
  unfold tailWord_7747980
  simp only [CollatzResearch.WordTrace]
  refine ⟨141296023235199592239912697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188394697646932789653216929 141296023235199592239912697)
  ·
    refine ⟨105972017426399694179934523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141296023235199592239912697 105972017426399694179934523)
    ·
      refine ⟨158958026139599541269901785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105972017426399694179934523 158958026139599541269901785)
      ·
        refine ⟨119218519604699655952426339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158958026139599541269901785 119218519604699655952426339)
        ·
          refine ⟨178827779407049483928639509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119218519604699655952426339 178827779407049483928639509)
          ·
            refine ⟨8382552159705444559154977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 178827779407049483928639509 8382552159705444559154977)
            ·
              refine ⟨6286914119779083419366233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8382552159705444559154977 6286914119779083419366233)
              ·
                refine ⟨4715185589834312564524675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6286914119779083419366233 4715185589834312564524675)
                ·
                  refine ⟨7072778384751468846787013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715185589834312564524675 7072778384751468846787013)
                  ·
                    refine ⟨1326145947140900408772565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7072778384751468846787013 1326145947140900408772565)
                    ·
                      rfl

theorem cell23_7747980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 1, 4].length) (baseStart_7747980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747980 prefixEnd_7747980 := by exact prefixLift 7747980
  have htrace : WordTrace (prefixWord ++ tailWord_7747980) baseStart_7747980 baseEnd_7747980 := by
    simpa [prefixWord, tailWord_7747980, baseEnd_7747980] using wordTrace_append hprefix tailTrace_7747980
  have hstable : (prefixWord ++ tailWord_7747980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747980).length < 2 ^ (prefixWord ++ tailWord_7747980).sum := by decide
  have hdescent : baseEnd_7747980 < baseStart_7747980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748023 : List Nat := [1, 1, 3, 1, 3, 5, 2, 1, 1, 5]
def baseStart_7748023 : Nat := 118140960795 + 7748023 * 2 ^ 59
def prefixEnd_7748023 : Nat := 4983230072969 + 3 ^ 40 * 7748023 * 2
def baseEnd_7748023 : Nat := 1326153307030281519359999

theorem tailTrace_7748023 : CollatzResearch.WordTrace tailWord_7748023 prefixEnd_7748023 1326153307030281519359999 := by
  unfold tailWord_7748023
  simp only [CollatzResearch.WordTrace]
  refine ⟨282593614809243402823640723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188395743206162268549093815 282593614809243402823640723)
  ·
    refine ⟨423890422213865104235461085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282593614809243402823640723 423890422213865104235461085)
    ·
      refine ⟨158958908330199414088297907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423890422213865104235461085 158958908330199414088297907)
      ·
        refine ⟨238438362495299121132446861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158958908330199414088297907 238438362495299121132446861)
        ·
          refine ⟨89414385935737170424667573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238438362495299121132446861 89414385935737170424667573)
          ·
            refine ⟨8382598681475359727312585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89414385935737170424667573 8382598681475359727312585)
            ·
              refine ⟨6286949011106519795484439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8382598681475359727312585 6286949011106519795484439)
              ·
                refine ⟨9430423516659779693226659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6286949011106519795484439 9430423516659779693226659)
                ·
                  refine ⟨14145635274989669539839989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9430423516659779693226659 14145635274989669539839989)
                  ·
                    refine ⟨1326153307030281519359999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14145635274989669539839989 1326153307030281519359999)
                    ·
                      rfl

theorem cell23_7748023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 1, 5].length) (baseStart_7748023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748023 prefixEnd_7748023 := by exact prefixLift 7748023
  have htrace : WordTrace (prefixWord ++ tailWord_7748023) baseStart_7748023 baseEnd_7748023 := by
    simpa [prefixWord, tailWord_7748023, baseEnd_7748023] using wordTrace_append hprefix tailTrace_7748023
  have hstable : (prefixWord ++ tailWord_7748023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748023).length < 2 ^ (prefixWord ++ tailWord_7748023).sum := by decide
  have hdescent : baseEnd_7748023 < baseStart_7748023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748063 : List Nat := [1, 1, 2, 3, 3, 3, 2, 2, 1, 2, 3]
def baseStart_7748063 : Nat := 118140960795 + 7748063 * 2 ^ 59
def prefixEnd_7748063 : Nat := 4983230072969 + 3 ^ 40 * 7748063 * 2
def baseEnd_7748063 : Nat := 3978480460317024401579813

theorem tailTrace_7748063 : CollatzResearch.WordTrace tailWord_7748063 prefixEnd_7748063 3978480460317024401579813 := by
  unfold tailWord_7748063
  simp only [CollatzResearch.WordTrace]
  refine ⟨282595073729098489655096843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188396715819398993103397895 282595073729098489655096843)
  ·
    refine ⟨423892610593647734482645265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282595073729098489655096843 423892610593647734482645265)
    ·
      refine ⟨317919457945235800861983949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423892610593647734482645265 317919457945235800861983949)
      ·
        refine ⟨119219796729463425323243981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317919457945235800861983949 119219796729463425323243981)
        ·
          refine ⟨44707423773548784496216493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119219796729463425323243981 44707423773548784496216493)
          ·
            refine ⟨16765283915080794186081185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44707423773548784496216493 16765283915080794186081185)
            ·
              refine ⟨12573962936310595639560889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16765283915080794186081185 12573962936310595639560889)
              ·
                refine ⟨9430472202232946729670667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12573962936310595639560889 9430472202232946729670667)
                ·
                  refine ⟨14145708303349420094506001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9430472202232946729670667 14145708303349420094506001)
                  ·
                    refine ⟨10609281227512065070879501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14145708303349420094506001 10609281227512065070879501)
                    ·
                      refine ⟨3978480460317024401579813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10609281227512065070879501 3978480460317024401579813)
                      ·
                        rfl

theorem cell23_7748063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_7748063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748063 prefixEnd_7748063 := by exact prefixLift 7748063
  have htrace : WordTrace (prefixWord ++ tailWord_7748063) baseStart_7748063 baseEnd_7748063 := by
    simpa [prefixWord, tailWord_7748063, baseEnd_7748063] using wordTrace_append hprefix tailTrace_7748063
  have hstable : (prefixWord ++ tailWord_7748063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748063).length < 2 ^ (prefixWord ++ tailWord_7748063).sum := by decide
  have hdescent : baseEnd_7748063 < baseStart_7748063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748076 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 3]
def baseStart_7748076 : Nat := 118140960795 + 7748076 * 2 ^ 59
def prefixEnd_7748076 : Nat := 4983230072969 + 3 ^ 40 * 7748076 * 2
def baseEnd_7748076 : Nat := 3978487135565532850717253

theorem tailTrace_7748076 : CollatzResearch.WordTrace tailWord_7748076 prefixEnd_7748076 3978487135565532850717253 := by
  unfold tailWord_7748076
  simp only [CollatzResearch.WordTrace]
  refine ⟨141297773939025696437660041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188397031918700928583546721 141297773939025696437660041)
  ·
    refine ⟨105973330454269272328245031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141297773939025696437660041 105973330454269272328245031)
    ·
      refine ⟨158959995681403908492367547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105973330454269272328245031 158959995681403908492367547)
      ·
        refine ⟨238439993522105862738551321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158959995681403908492367547 238439993522105862738551321)
        ·
          refine ⟨178829995141579397053913491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238439993522105862738551321 178829995141579397053913491)
          ·
            refine ⟨268244992712369095580870237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178829995141579397053913491 268244992712369095580870237)
            ·
              refine ⟨100591872267138410842826339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268244992712369095580870237 100591872267138410842826339)
              ·
                refine ⟨150887808400707616264239509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100591872267138410842826339 150887808400707616264239509)
                ·
                  refine ⟨7072866018783169512386227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150887808400707616264239509 7072866018783169512386227)
                  ·
                    refine ⟨10609299028174754268579341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7072866018783169512386227 10609299028174754268579341)
                    ·
                      refine ⟨3978487135565532850717253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10609299028174754268579341 3978487135565532850717253)
                      ·
                        rfl

theorem cell23_7748076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 3].length) (baseStart_7748076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748076 prefixEnd_7748076 := by exact prefixLift 7748076
  have htrace : WordTrace (prefixWord ++ tailWord_7748076) baseStart_7748076 baseEnd_7748076 := by
    simpa [prefixWord, tailWord_7748076, baseEnd_7748076] using wordTrace_append hprefix tailTrace_7748076
  have hstable : (prefixWord ++ tailWord_7748076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748076).length < 2 ^ (prefixWord ++ tailWord_7748076).sum := by decide
  have hdescent : baseEnd_7748076 < baseStart_7748076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748093 : List Nat := [1, 4, 1, 1, 1, 3, 2, 4, 2, 1, 3]
def baseStart_7748093 : Nat := 118140960795 + 7748093 * 2 ^ 59
def prefixEnd_7748093 : Nat := 4983230072969 + 3 ^ 40 * 7748093 * 2
def baseEnd_7748093 : Nat := 3978495864736659284204675

theorem tailTrace_7748093 : CollatzResearch.WordTrace tailWord_7748093 prefixEnd_7748093 3978495864736659284204675 := by
  unfold tailWord_7748093
  simp only [CollatzResearch.WordTrace]
  refine ⟨282596167918989804778688933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188397445279326536519125955 282596167918989804778688933)
  ·
    refine ⟨52986781484810588396004175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282596167918989804778688933 52986781484810588396004175)
    ·
      refine ⟨79480172227215882594006263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52986781484810588396004175 79480172227215882594006263)
      ·
        refine ⟨119220258340823823891009395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79480172227215882594006263 119220258340823823891009395)
        ·
          refine ⟨178830387511235735836514093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119220258340823823891009395 178830387511235735836514093)
          ·
            refine ⟨67061395316713400938692785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178830387511235735836514093 67061395316713400938692785)
            ·
              refine ⟨50296046487535050704019589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67061395316713400938692785 50296046487535050704019589)
              ·
                refine ⟨9430508716412822007003673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50296046487535050704019589 9430508716412822007003673)
                ·
                  refine ⟨7072881537309616505252755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9430508716412822007003673 7072881537309616505252755)
                  ·
                    refine ⟨10609322305964424757879133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7072881537309616505252755 10609322305964424757879133)
                    ·
                      refine ⟨3978495864736659284204675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10609322305964424757879133 3978495864736659284204675)
                      ·
                        rfl

theorem cell23_7748093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_7748093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748093 prefixEnd_7748093 := by exact prefixLift 7748093
  have htrace : WordTrace (prefixWord ++ tailWord_7748093) baseStart_7748093 baseEnd_7748093 := by
    simpa [prefixWord, tailWord_7748093, baseEnd_7748093] using wordTrace_append hprefix tailTrace_7748093
  have hstable : (prefixWord ++ tailWord_7748093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748093).length < 2 ^ (prefixWord ++ tailWord_7748093).sum := by decide
  have hdescent : baseEnd_7748093 < baseStart_7748093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748099 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 4]
def baseStart_7748099 : Nat := 118140960795 + 7748099 * 2 ^ 59
def prefixEnd_7748099 : Nat := 4983230072969 + 3 ^ 40 * 7748099 * 2
def baseEnd_7748099 : Nat := 3978498945620586260729647

theorem tailTrace_7748099 : CollatzResearch.WordTrace tailWord_7748099 prefixEnd_7748099 3978498945620586260729647 := by
  unfold tailWord_7748099
  simp only [CollatzResearch.WordTrace]
  refine ⟨282596386756968067803407351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188397591171312045202271567 282596386756968067803407351)
  ·
    refine ⟨423894580135452101705111027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282596386756968067803407351 423894580135452101705111027)
    ·
      refine ⟨635841870203178152557666541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423894580135452101705111027 635841870203178152557666541)
      ·
        refine ⟨238440701326191807209124953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 635841870203178152557666541 238440701326191807209124953)
        ·
          refine ⟨178830525994643855406843715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238440701326191807209124953 178830525994643855406843715)
          ·
            refine ⟨268245788991965783110265573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178830525994643855406843715 268245788991965783110265573)
            ·
              refine ⟨50296085435993584333174795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268245788991965783110265573 50296085435993584333174795)
              ·
                refine ⟨75444128153990376499762193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50296085435993584333174795 75444128153990376499762193)
                ·
                  refine ⟨56583096115492782374821645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75444128153990376499762193 56583096115492782374821645)
                  ·
                    refine ⟨21218661043309793390558117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56583096115492782374821645 21218661043309793390558117)
                    ·
                      refine ⟨3978498945620586260729647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21218661043309793390558117 3978498945620586260729647)
                      ·
                        rfl

theorem cell23_7748099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_7748099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748099 prefixEnd_7748099 := by exact prefixLift 7748099
  have htrace : WordTrace (prefixWord ++ tailWord_7748099) baseStart_7748099 baseEnd_7748099 := by
    simpa [prefixWord, tailWord_7748099, baseEnd_7748099] using wordTrace_append hprefix tailTrace_7748099
  have hstable : (prefixWord ++ tailWord_7748099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748099).length < 2 ^ (prefixWord ++ tailWord_7748099).sum := by decide
  have hdescent : baseEnd_7748099 < baseStart_7748099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748110 : List Nat := [4, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3]
def baseStart_7748110 : Nat := 118140960795 + 7748110 * 2 ^ 59
def prefixEnd_7748110 : Nat := 4983230072969 + 3 ^ 40 * 7748110 * 2
def baseEnd_7748110 : Nat := 3978504593907785717692097

theorem tailTrace_7748110 : CollatzResearch.WordTrace tailWord_7748110 prefixEnd_7748110 3978504593907785717692097 := by
  unfold tailWord_7748110
  simp only [CollatzResearch.WordTrace]
  refine ⟨35324598494991027085257223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188397858639952144454705189 35324598494991027085257223)
  ·
    refine ⟨52986897742486540627885835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35324598494991027085257223 52986897742486540627885835)
    ·
      refine ⟨79480346613729810941828753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52986897742486540627885835 79480346613729810941828753)
      ·
        refine ⟨59610259960297358206371565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79480346613729810941828753 59610259960297358206371565)
        ·
          refine ⟨22353847485111509327389337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59610259960297358206371565 22353847485111509327389337)
          ·
            refine ⟨16765385613833631995542003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22353847485111509327389337 16765385613833631995542003)
            ·
              refine ⟨25148078420750447993313005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16765385613833631995542003 25148078420750447993313005)
              ·
                refine ⟨9430529407781417997492377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25148078420750447993313005 9430529407781417997492377)
                ·
                  refine ⟨7072897055836063498119283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9430529407781417997492377 7072897055836063498119283)
                  ·
                    refine ⟨10609345583754095247178925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7072897055836063498119283 10609345583754095247178925)
                    ·
                      refine ⟨3978504593907785717692097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10609345583754095247178925 3978504593907785717692097)
                      ·
                        rfl

theorem cell23_7748110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_7748110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748110 prefixEnd_7748110 := by exact prefixLift 7748110
  have htrace : WordTrace (prefixWord ++ tailWord_7748110) baseStart_7748110 baseEnd_7748110 := by
    simpa [prefixWord, tailWord_7748110, baseEnd_7748110] using wordTrace_append hprefix tailTrace_7748110
  have hstable : (prefixWord ++ tailWord_7748110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748110).length < 2 ^ (prefixWord ++ tailWord_7748110).sum := by decide
  have hdescent : baseEnd_7748110 < baseStart_7748110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748120 : List Nat := [2, 1, 2, 3, 3, 1, 3, 2, 1, 3, 2]
def baseStart_7748120 : Nat := 118140960795 + 7748120 * 2 ^ 59
def prefixEnd_7748120 : Nat := 4983230072969 + 3 ^ 40 * 7748120 * 2
def baseEnd_7748120 : Nat := 3978509728714330678567051

theorem tailTrace_7748120 : CollatzResearch.WordTrace tailWord_7748120 prefixEnd_7748120 3978509728714330678567051 := by
  unfold tailWord_7748120
  simp only [CollatzResearch.WordTrace]
  refine ⟨141298576344945994194960907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188398101793261325593281209 141298576344945994194960907)
  ·
    refine ⟨211947864517418991292441361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141298576344945994194960907 211947864517418991292441361)
    ·
      refine ⟨158960898388064243469331021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211947864517418991292441361 158960898388064243469331021)
      ·
        refine ⟨59610336895524091300999133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158960898388064243469331021 59610336895524091300999133)
        ·
          refine ⟨22353876335821534237874675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59610336895524091300999133 22353876335821534237874675)
          ·
            refine ⟨33530814503732301356812013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22353876335821534237874675 33530814503732301356812013)
            ·
              refine ⟨12574055438899613008804505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33530814503732301356812013 12574055438899613008804505)
              ·
                refine ⟨9430541579174709756603379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12574055438899613008804505 9430541579174709756603379)
                ·
                  refine ⟨14145812368762064634905069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9430541579174709756603379 14145812368762064634905069)
                  ·
                    refine ⟨5304679638285774238089401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14145812368762064634905069 5304679638285774238089401)
                    ·
                      refine ⟨3978509728714330678567051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5304679638285774238089401 3978509728714330678567051)
                      ·
                        rfl

theorem cell23_7748120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_7748120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748120 prefixEnd_7748120 := by exact prefixLift 7748120
  have htrace : WordTrace (prefixWord ++ tailWord_7748120) baseStart_7748120 baseEnd_7748120 := by
    simpa [prefixWord, tailWord_7748120, baseEnd_7748120] using wordTrace_append hprefix tailTrace_7748120
  have hstable : (prefixWord ++ tailWord_7748120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748120).length < 2 ^ (prefixWord ++ tailWord_7748120).sum := by decide
  have hdescent : baseEnd_7748120 < baseStart_7748120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748133 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 6, 2, 2]
def baseStart_7748133 : Nat := 118140960795 + 7748133 * 2 ^ 59
def prefixEnd_7748133 : Nat := 4983230072969 + 3 ^ 40 * 7748133 * 2
def baseEnd_7748133 : Nat := 3978516403962839127704491

theorem tailTrace_7748133 : CollatzResearch.WordTrace tailWord_7748133 prefixEnd_7748133 3978516403962839127704491 := by
  unfold tailWord_7748133
  simp only [CollatzResearch.WordTrace]
  refine ⟨282597626838844891610145053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188398417892563261073430035 282597626838844891610145053)
  ·
    refine ⟨105974110064566834353804395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282597626838844891610145053 105974110064566834353804395)
    ·
      refine ⟨158961165096850251530706593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105974110064566834353804395 158961165096850251530706593)
      ·
        refine ⟨119220873822637688648029945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158961165096850251530706593 119220873822637688648029945)
        ·
          refine ⟨89415655366978266486022459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119220873822637688648029945 89415655366978266486022459)
          ·
            refine ⟨134123483050467399729033689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89415655366978266486022459 134123483050467399729033689)
            ·
              refine ⟨100592612287850549796775267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134123483050467399729033689 100592612287850549796775267)
              ·
                refine ⟨150888918431775824695162901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100592612287850549796775267 150888918431775824695162901)
                ·
                  refine ⟨7072918051489491782585761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150888918431775824695162901 7072918051489491782585761)
                  ·
                    refine ⟨5304688538617118836939321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7072918051489491782585761 5304688538617118836939321)
                    ·
                      refine ⟨3978516403962839127704491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5304688538617118836939321 3978516403962839127704491)
                      ·
                        rfl

theorem cell23_7748133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 2, 2].length) (baseStart_7748133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748133 prefixEnd_7748133 := by exact prefixLift 7748133
  have htrace : WordTrace (prefixWord ++ tailWord_7748133) baseStart_7748133 baseEnd_7748133 := by
    simpa [prefixWord, tailWord_7748133, baseEnd_7748133] using wordTrace_append hprefix tailTrace_7748133
  have hstable : (prefixWord ++ tailWord_7748133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748133).length < 2 ^ (prefixWord ++ tailWord_7748133).sum := by decide
  have hdescent : baseEnd_7748133 < baseStart_7748133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748173 : List Nat := [1, 6, 1, 1, 2, 2, 1, 2, 7]
def baseStart_7748173 : Nat := 118140960795 + 7748173 * 2 ^ 59
def prefixEnd_7748173 : Nat := 4983230072969 + 3 ^ 40 * 7748173 * 2
def baseEnd_7748173 : Nat := 442059660354335441244923

theorem tailTrace_7748173 : CollatzResearch.WordTrace tailWord_7748173 prefixEnd_7748173 442059660354335441244923 := by
  unfold tailWord_7748173
  simp only [CollatzResearch.WordTrace]
  refine ⟨282599085758699978441601173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188399390505799985627734115 282599085758699978441601173)
  ·
    refine ⟨13246832144939061489450055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 282599085758699978441601173 13246832144939061489450055)
    ·
      refine ⟨19870248217408592234175083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13246832144939061489450055 19870248217408592234175083)
      ·
        refine ⟨29805372326112888351262625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19870248217408592234175083 29805372326112888351262625)
        ·
          refine ⟨22354029244584666263446969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29805372326112888351262625 22354029244584666263446969)
          ·
            refine ⟨16765521933438499697585227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22354029244584666263446969 16765521933438499697585227)
            ·
              refine ⟨25148282900157749546377841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16765521933438499697585227 25148282900157749546377841)
              ·
                refine ⟨18861212175118312159783381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25148282900157749546377841 18861212175118312159783381)
                ·
                  refine ⟨442059660354335441244923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18861212175118312159783381 442059660354335441244923)
                  ·
                    rfl

theorem cell23_7748173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_7748173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748173 prefixEnd_7748173 := by exact prefixLift 7748173
  have htrace : WordTrace (prefixWord ++ tailWord_7748173) baseStart_7748173 baseEnd_7748173 := by
    simpa [prefixWord, tailWord_7748173, baseEnd_7748173] using wordTrace_append hprefix tailTrace_7748173
  have hstable : (prefixWord ++ tailWord_7748173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748173).length < 2 ^ (prefixWord ++ tailWord_7748173).sum := by decide
  have hdescent : baseEnd_7748173 < baseStart_7748173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748216 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 7, 4]
def baseStart_7748216 : Nat := 118140960795 + 7748216 * 2 ^ 59
def prefixEnd_7748216 : Nat := 4983230072969 + 3 ^ 40 * 7748216 * 2
def baseEnd_7748216 : Nat := 1326186340952387434322203

theorem tailTrace_7748216 : CollatzResearch.WordTrace tailWord_7748216 prefixEnd_7748216 1326186340952387434322203 := by
  unfold tailWord_7748216
  simp only [CollatzResearch.WordTrace]
  refine ⟨141300327048772098392708251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188400436065029464523611001 141300327048772098392708251)
  ·
    refine ⟨211950490573158147589062377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141300327048772098392708251 211950490573158147589062377)
    ·
      refine ⟨158962867929868610691796783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211950490573158147589062377 158962867929868610691796783)
      ·
        refine ⟨238444301894802916037695175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158962867929868610691796783 238444301894802916037695175)
        ·
          refine ⟨357666452842204374056542763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238444301894802916037695175 357666452842204374056542763)
          ·
            refine ⟨536499679263306561084814145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357666452842204374056542763 536499679263306561084814145)
            ·
              refine ⟨402374759447479920813610609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 536499679263306561084814145 402374759447479920813610609)
              ·
                refine ⟨301781069585609940610207957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402374759447479920813610609 301781069585609940610207957)
                ·
                  refine ⟨7072993818412732983051749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 301781069585609940610207957 7072993818412732983051749)
                  ·
                    refine ⟨1326186340952387434322203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7072993818412732983051749 1326186340952387434322203)
                    ·
                      rfl

theorem cell23_7748216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 7, 4].length) (baseStart_7748216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748216 prefixEnd_7748216 := by exact prefixLift 7748216
  have htrace : WordTrace (prefixWord ++ tailWord_7748216) baseStart_7748216 baseEnd_7748216 := by
    simpa [prefixWord, tailWord_7748216, baseEnd_7748216] using wordTrace_append hprefix tailTrace_7748216
  have hstable : (prefixWord ++ tailWord_7748216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748216).length < 2 ^ (prefixWord ++ tailWord_7748216).sum := by decide
  have hdescent : baseEnd_7748216 < baseStart_7748216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748324 : List Nat := [2, 3, 1, 1, 1, 4, 4, 2, 1, 1, 3]
def baseStart_7748324 : Nat := 118140960795 + 7748324 * 2 ^ 59
def prefixEnd_7748324 : Nat := 4983230072969 + 3 ^ 40 * 7748324 * 2
def baseEnd_7748324 : Nat := 3978614478767847880416113

theorem tailTrace_7748324 : CollatzResearch.WordTrace tailWord_7748324 prefixEnd_7748324 3978614478767847880416113 := by
  unfold tailWord_7748324
  simp only [CollatzResearch.WordTrace]
  refine ⟨141302296590576465615174013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188403062120768620820232017 141302296590576465615174013)
  ·
    refine ⟨52988361221466174605690255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141302296590576465615174013 52988361221466174605690255)
    ·
      refine ⟨79482541832199261908535383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52988361221466174605690255 79482541832199261908535383)
      ·
        refine ⟨119223812748298892862803075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79482541832199261908535383 119223812748298892862803075)
        ·
          refine ⟨178835719122448339294204613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119223812748298892862803075 178835719122448339294204613)
          ·
            refine ⟨33531697335459063617663365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178835719122448339294204613 33531697335459063617663365)
            ·
              refine ⟨6287193250398574428311881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33531697335459063617663365 6287193250398574428311881)
              ·
                refine ⟨4715394937798930821233911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6287193250398574428311881 4715394937798930821233911)
                ·
                  refine ⟨7073092406698396231850867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715394937798930821233911 7073092406698396231850867)
                  ·
                    refine ⟨10609638610047594347776301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7073092406698396231850867 10609638610047594347776301)
                    ·
                      refine ⟨3978614478767847880416113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10609638610047594347776301 3978614478767847880416113)
                      ·
                        rfl

theorem cell23_7748324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 1, 1, 3].length) (baseStart_7748324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748324 prefixEnd_7748324 := by exact prefixLift 7748324
  have htrace : WordTrace (prefixWord ++ tailWord_7748324) baseStart_7748324 baseEnd_7748324 := by
    simpa [prefixWord, tailWord_7748324, baseEnd_7748324] using wordTrace_append hprefix tailTrace_7748324
  have hstable : (prefixWord ++ tailWord_7748324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748324).length < 2 ^ (prefixWord ++ tailWord_7748324).sum := by decide
  have hdescent : baseEnd_7748324 < baseStart_7748324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748333 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_7748333 : Nat := 118140960795 + 7748333 * 2 ^ 59
def prefixEnd_7748333 : Nat := 4983230072969 + 3 ^ 40 * 7748333 * 2
def baseEnd_7748333 : Nat := 3978619100093738345203571

theorem tailTrace_7748333 : CollatzResearch.WordTrace tailWord_7748333 prefixEnd_7748333 3978619100093738345203571 := by
  unfold tailWord_7748333
  simp only [CollatzResearch.WordTrace]
  refine ⟨282604921438120325767425653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188403280958746883844950435 282604921438120325767425653)
  ·
    refine ⟨26494211384823780540696155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 282604921438120325767425653 26494211384823780540696155)
    ·
      refine ⟨39741317077235670811044233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26494211384823780540696155 39741317077235670811044233)
      ·
        refine ⟨29805987807926753108283175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39741317077235670811044233 29805987807926753108283175)
        ·
          refine ⟨44708981711890129662424763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29805987807926753108283175 44708981711890129662424763)
          ·
            refine ⟨67063472567835194493637145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44708981711890129662424763 67063472567835194493637145)
            ·
              refine ⟨50297604425876395870227859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67063472567835194493637145 50297604425876395870227859)
              ·
                refine ⟨75446406638814593805341789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50297604425876395870227859 75446406638814593805341789)
                ·
                  refine ⟨28292402489555472677003171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75446406638814593805341789 28292402489555472677003171)
                  ·
                    refine ⟨42438603734333209015504757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28292402489555472677003171 42438603734333209015504757)
                    ·
                      refine ⟨3978619100093738345203571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42438603734333209015504757 3978619100093738345203571)
                      ·
                        rfl

theorem cell23_7748333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_7748333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748333 prefixEnd_7748333 := by exact prefixLift 7748333
  have htrace : WordTrace (prefixWord ++ tailWord_7748333) baseStart_7748333 baseEnd_7748333 := by
    simpa [prefixWord, tailWord_7748333, baseEnd_7748333] using wordTrace_append hprefix tailTrace_7748333
  have hstable : (prefixWord ++ tailWord_7748333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748333).length < 2 ^ (prefixWord ++ tailWord_7748333).sum := by decide
  have hdescent : baseEnd_7748333 < baseStart_7748333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748341 : List Nat := [1, 3, 6, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_7748341 : Nat := 118140960795 + 7748341 * 2 ^ 59
def prefixEnd_7748341 : Nat := 4983230072969 + 3 ^ 40 * 7748341 * 2
def baseEnd_7748341 : Nat := 3978623207938974313903535

theorem tailTrace_7748341 : CollatzResearch.WordTrace tailWord_7748341 prefixEnd_7748341 3978623207938974313903535 := by
  unfold tailWord_7748341
  simp only [CollatzResearch.WordTrace]
  refine ⟨282605213222091343133716877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188403475481394228755811251 282605213222091343133716877)
  ·
    refine ⟨105976954958284253675143829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282605213222091343133716877 105976954958284253675143829)
    ·
      refine ⟨4967669763669574391022367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 105976954958284253675143829 4967669763669574391022367)
      ·
        refine ⟨7451504645504361586533551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4967669763669574391022367 7451504645504361586533551)
        ·
          refine ⟨11177256968256542379800327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7451504645504361586533551 11177256968256542379800327)
          ·
            refine ⟨16765885452384813569700491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11177256968256542379800327 16765885452384813569700491)
            ·
              refine ⟨25148828178577220354550737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16765885452384813569700491 25148828178577220354550737)
              ·
                refine ⟨18861621133932915265913053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25148828178577220354550737 18861621133932915265913053)
                ·
                  refine ⟨7073107925224843224717395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18861621133932915265913053 7073107925224843224717395)
                  ·
                    refine ⟨10609661887837264837076093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7073107925224843224717395 10609661887837264837076093)
                    ·
                      refine ⟨3978623207938974313903535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10609661887837264837076093 3978623207938974313903535)
                      ·
                        rfl

theorem cell23_7748341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_7748341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748341 prefixEnd_7748341 := by exact prefixLift 7748341
  have htrace : WordTrace (prefixWord ++ tailWord_7748341) baseStart_7748341 baseEnd_7748341 := by
    simpa [prefixWord, tailWord_7748341, baseEnd_7748341] using wordTrace_append hprefix tailTrace_7748341
  have hstable : (prefixWord ++ tailWord_7748341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748341).length < 2 ^ (prefixWord ++ tailWord_7748341).sum := by decide
  have hdescent : baseEnd_7748341 < baseStart_7748341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748370 : List Nat := [3, 2, 4, 1, 2, 1, 10]
def baseStart_7748370 : Nat := 118140960795 + 7748370 * 2 ^ 59
def prefixEnd_7748370 : Nat := 4983230072969 + 3 ^ 40 * 7748370 * 2
def baseEnd_7748370 : Nat := 49118988875036477783221

theorem tailTrace_7748370 : CollatzResearch.WordTrace tailWord_7748370 prefixEnd_7748370 49118988875036477783221 := by
  unfold tailWord_7748370
  simp only [CollatzResearch.WordTrace]
  refine ⟨70651567734746570271630641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188404180625990854057681709 70651567734746570271630641)
  ·
    refine ⟨52988675801059927703722981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70651567734746570271630641 52988675801059927703722981)
    ·
      refine ⟨9935376712698736444448059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52988675801059927703722981 9935376712698736444448059)
      ·
        refine ⟨14903065069048104666672089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9935376712698736444448059 14903065069048104666672089)
        ·
          refine ⟨11177298801786078500004067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14903065069048104666672089 11177298801786078500004067)
          ·
            refine ⟨16765948202679117750006101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11177298801786078500004067 16765948202679117750006101)
            ·
              refine ⟨49118988875036477783221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16765948202679117750006101 49118988875036477783221)
              ·
                rfl

theorem cell23_7748370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 10].length) (baseStart_7748370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748370 prefixEnd_7748370 := by exact prefixLift 7748370
  have htrace : WordTrace (prefixWord ++ tailWord_7748370) baseStart_7748370 baseEnd_7748370 := by
    simpa [prefixWord, tailWord_7748370, baseEnd_7748370] using wordTrace_append hprefix tailTrace_7748370
  have hstable : (prefixWord ++ tailWord_7748370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748370).length < 2 ^ (prefixWord ++ tailWord_7748370).sum := by decide
  have hdescent : baseEnd_7748370 < baseStart_7748370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748381 : List Nat := [1, 4, 2, 4, 1, 1, 2, 1, 3, 2, 2]
def baseStart_7748381 : Nat := 118140960795 + 7748381 * 2 ^ 59
def prefixEnd_7748381 : Nat := 4983230072969 + 3 ^ 40 * 7748381 * 2
def baseEnd_7748381 : Nat := 3978643747165154157403351

theorem tailTrace_7748381 : CollatzResearch.WordTrace tailWord_7748381 prefixEnd_7748381 3978643747165154157403351 := by
  unfold tailWord_7748381
  simp only [CollatzResearch.WordTrace]
  refine ⟨282606672141946429965172997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188404448094630953310115331 282606672141946429965172997)
  ·
    refine ⟨52988751026614955618469937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282606672141946429965172997 52988751026614955618469937)
    ·
      refine ⟨39741563269961216713852453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52988751026614955618469937 39741563269961216713852453)
      ·
        refine ⟨7451543113117728133847335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39741563269961216713852453 7451543113117728133847335)
        ·
          refine ⟨11177314669676592200771003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7451543113117728133847335 11177314669676592200771003)
          ·
            refine ⟨16765972004514888301156505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11177314669676592200771003 16765972004514888301156505)
            ·
              refine ⟨12574479003386166225867379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16765972004514888301156505 12574479003386166225867379)
              ·
                refine ⟨18861718505079249338801069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12574479003386166225867379 18861718505079249338801069)
                ·
                  refine ⟨7073144439404718502050401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18861718505079249338801069 7073144439404718502050401)
                  ·
                    refine ⟨5304858329553538876537801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7073144439404718502050401 5304858329553538876537801)
                    ·
                      refine ⟨3978643747165154157403351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5304858329553538876537801 3978643747165154157403351)
                      ·
                        rfl

theorem cell23_7748381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_7748381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748381 prefixEnd_7748381 := by exact prefixLift 7748381
  have htrace : WordTrace (prefixWord ++ tailWord_7748381) baseStart_7748381 baseEnd_7748381 := by
    simpa [prefixWord, tailWord_7748381, baseEnd_7748381] using wordTrace_append hprefix tailTrace_7748381
  have hstable : (prefixWord ++ tailWord_7748381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748381).length < 2 ^ (prefixWord ++ tailWord_7748381).sum := by decide
  have hdescent : baseEnd_7748381 < baseStart_7748381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748394 : List Nat := [3, 1, 4, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_7748394 : Nat := 118140960795 + 7748394 * 2 ^ 59
def prefixEnd_7748394 : Nat := 4983230072969 + 3 ^ 40 * 7748394 * 2
def baseEnd_7748394 : Nat := 3978650422413662606540791

theorem tailTrace_7748394 : CollatzResearch.WordTrace tailWord_7748394 prefixEnd_7748394 3978650422413662606540791 := by
  unfold tailWord_7748394
  simp only [CollatzResearch.WordTrace]
  refine ⟨70651786572724833296349059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188404764193932888790264157 70651786572724833296349059)
  ·
    refine ⟨105977679859087249944523589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70651786572724833296349059 105977679859087249944523589)
    ·
      refine ⟨19870814973578859364598173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105977679859087249944523589 19870814973578859364598173)
      ·
        refine ⟨7451555615092072261724315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19870814973578859364598173 7451555615092072261724315)
        ·
          refine ⟨11177333422638108392586473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7451555615092072261724315 11177333422638108392586473)
          ·
            refine ⟨8383000066978581294439855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11177333422638108392586473 8383000066978581294439855)
            ·
              refine ⟨12574500100467871941659783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8383000066978581294439855 12574500100467871941659783)
              ·
                refine ⟨18861750150701807912489675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12574500100467871941659783 18861750150701807912489675)
                ·
                  refine ⟨28292625226052711868734513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18861750150701807912489675 28292625226052711868734513)
                  ·
                    refine ⟨21219468919539533901550885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28292625226052711868734513 21219468919539533901550885)
                    ·
                      refine ⟨3978650422413662606540791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21219468919539533901550885 3978650422413662606540791)
                      ·
                        rfl

theorem cell23_7748394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_7748394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748394 prefixEnd_7748394 := by exact prefixLift 7748394
  have htrace : WordTrace (prefixWord ++ tailWord_7748394) baseStart_7748394 baseEnd_7748394 := by
    simpa [prefixWord, tailWord_7748394, baseEnd_7748394] using wordTrace_append hprefix tailTrace_7748394
  have hstable : (prefixWord ++ tailWord_7748394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748394).length < 2 ^ (prefixWord ++ tailWord_7748394).sum := by decide
  have hdescent : baseEnd_7748394 < baseStart_7748394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748404 : List Nat := [2, 5, 1, 1, 4, 1, 2, 7]
def baseStart_7748404 : Nat := 118140960795 + 7748404 * 2 ^ 59
def prefixEnd_7748404 : Nat := 4983230072969 + 3 ^ 40 * 7748404 * 2
def baseEnd_7748404 : Nat := 147357613230378058052435

theorem tailTrace_7748404 : CollatzResearch.WordTrace tailWord_7748404 prefixEnd_7748404 147357613230378058052435 := by
  unfold tailWord_7748404
  simp only [CollatzResearch.WordTrace]
  refine ⟨141303755510431552446630133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188405007347242069928840177 141303755510431552446630133)
  ·
    refine ⟨13247227079102958041871575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141303755510431552446630133 13247227079102958041871575)
    ·
      refine ⟨19870840618654437062807363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13247227079102958041871575 19870840618654437062807363)
      ·
        refine ⟨29806260927981655594211045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19870840618654437062807363 29806260927981655594211045)
        ·
          refine ⟨5588673923996560423914571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29806260927981655594211045 5588673923996560423914571)
          ·
            refine ⟨8383010885994840635871857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5588673923996560423914571 8383010885994840635871857)
            ·
              refine ⟨6287258164496130476903893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8383010885994840635871857 6287258164496130476903893)
              ·
                refine ⟨147357613230378058052435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6287258164496130476903893 147357613230378058052435)
                ·
                  rfl

theorem cell23_7748404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 7].length) (baseStart_7748404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748404 prefixEnd_7748404 := by exact prefixLift 7748404
  have htrace : WordTrace (prefixWord ++ tailWord_7748404) baseStart_7748404 baseEnd_7748404 := by
    simpa [prefixWord, tailWord_7748404, baseEnd_7748404] using wordTrace_append hprefix tailTrace_7748404
  have hstable : (prefixWord ++ tailWord_7748404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748404).length < 2 ^ (prefixWord ++ tailWord_7748404).sum := by decide
  have hdescent : baseEnd_7748404 < baseStart_7748404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748407 : List Nat := [1, 1, 3, 1, 2, 1, 6, 2, 1, 3, 2]
def baseStart_7748407 : Nat := 118140960795 + 7748407 * 2 ^ 59
def prefixEnd_7748407 : Nat := 4983230072969 + 3 ^ 40 * 7748407 * 2
def baseEnd_7748407 : Nat := 3978657097662171055678231

theorem tailTrace_7748407 : CollatzResearch.WordTrace tailWord_7748407 prefixEnd_7748407 3978657097662171055678231 := by
  unfold tailWord_7748407
  simp only [CollatzResearch.WordTrace]
  refine ⟨282607620439852236405619475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188405080293234824270412983 282607620439852236405619475)
  ·
    refine ⟨423911430659778354608429213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282607620439852236405619475 423911430659778354608429213)
    ·
      refine ⟨158966786497416882978160955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423911430659778354608429213 158966786497416882978160955)
      ·
        refine ⟨238450179746125324467241433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158966786497416882978160955 238450179746125324467241433)
        ·
          refine ⟨178837634809593993350431075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238450179746125324467241433 178837634809593993350431075)
          ·
            refine ⟨268256452214390990025646613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178837634809593993350431075 268256452214390990025646613)
            ·
              refine ⟨12574521197549577657452185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 268256452214390990025646613 12574521197549577657452185)
              ·
                refine ⟨9430890898162183243089139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12574521197549577657452185 9430890898162183243089139)
                ·
                  refine ⟨14146336347243274864633709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9430890898162183243089139 14146336347243274864633709)
                  ·
                    refine ⟨5304876130216228074237641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14146336347243274864633709 5304876130216228074237641)
                    ·
                      refine ⟨3978657097662171055678231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5304876130216228074237641 3978657097662171055678231)
                      ·
                        rfl

theorem cell23_7748407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 3, 2].length) (baseStart_7748407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748407 prefixEnd_7748407 := by exact prefixLift 7748407
  have htrace : WordTrace (prefixWord ++ tailWord_7748407) baseStart_7748407 baseEnd_7748407 := by
    simpa [prefixWord, tailWord_7748407, baseEnd_7748407] using wordTrace_append hprefix tailTrace_7748407
  have hstable : (prefixWord ++ tailWord_7748407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748407).length < 2 ^ (prefixWord ++ tailWord_7748407).sum := by decide
  have hdescent : baseEnd_7748407 < baseStart_7748407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748423 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 3]
def baseStart_7748423 : Nat := 118140960795 + 7748423 * 2 ^ 59
def prefixEnd_7748423 : Nat := 4983230072969 + 3 ^ 40 * 7748423 * 2
def baseEnd_7748423 : Nat := 3978665313352642993078157

theorem tailTrace_7748423 : CollatzResearch.WordTrace tailWord_7748423 prefixEnd_7748423 3978665313352642993078157 := by
  unfold tailWord_7748423
  simp only [CollatzResearch.WordTrace]
  refine ⟨282608204007794271138201923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188405469338529514092134615 282608204007794271138201923)
  ·
    refine ⟨423912306011691406707302885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282608204007794271138201923 423912306011691406707302885)
    ·
      refine ⟨79483557377192138757619291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 423912306011691406707302885 79483557377192138757619291)
      ·
        refine ⟨119225336065788208136428937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79483557377192138757619291 119225336065788208136428937)
        ·
          refine ⟨89419002049341156102321703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119225336065788208136428937 89419002049341156102321703)
          ·
            refine ⟨134128503074011734153482555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89419002049341156102321703 134128503074011734153482555)
            ·
              refine ⟨201192754611017601230223833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134128503074011734153482555 201192754611017601230223833)
              ·
                refine ⟨150894565958263200922667875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201192754611017601230223833 150894565958263200922667875)
                ·
                  refine ⟨226341848937394801384001813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150894565958263200922667875 226341848937394801384001813)
                  ·
                    refine ⟨10609774168940381314875085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 226341848937394801384001813 10609774168940381314875085)
                    ·
                      refine ⟨3978665313352642993078157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10609774168940381314875085 3978665313352642993078157)
                      ·
                        rfl

theorem cell23_7748423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_7748423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748423 prefixEnd_7748423 := by exact prefixLift 7748423
  have htrace : WordTrace (prefixWord ++ tailWord_7748423) baseStart_7748423 baseEnd_7748423 := by
    simpa [prefixWord, tailWord_7748423, baseEnd_7748423] using wordTrace_append hprefix tailTrace_7748423
  have hstable : (prefixWord ++ tailWord_7748423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748423).length < 2 ^ (prefixWord ++ tailWord_7748423).sum := by decide
  have hdescent : baseEnd_7748423 < baseStart_7748423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748437 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 4, 2, 2]
def baseStart_7748437 : Nat := 118140960795 + 7748437 * 2 ^ 59
def prefixEnd_7748437 : Nat := 4983230072969 + 3 ^ 40 * 7748437 * 2
def baseEnd_7748437 : Nat := 3978672502081805938303093

theorem tailTrace_7748437 : CollatzResearch.WordTrace tailWord_7748437 prefixEnd_7748437 3978672502081805938303093 := by
  unfold tailWord_7748437
  simp only [CollatzResearch.WordTrace]
  refine ⟨282608714629743551529211565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188405809753162367686141043 282608714629743551529211565)
  ·
    refine ⟨105978267986153831823454337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282608714629743551529211565 105978267986153831823454337)
    ·
      refine ⟨79483700989615373867590753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105978267986153831823454337 79483700989615373867590753)
      ·
        refine ⟨59612775742211530400693065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79483700989615373867590753 59612775742211530400693065)
        ·
          refine ⟨44709581806658647800519799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59612775742211530400693065 44709581806658647800519799)
          ·
            refine ⟨67064372709987971700779699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44709581806658647800519799 67064372709987971700779699)
            ·
              refine ⟨100596559064981957551169549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67064372709987971700779699 100596559064981957551169549)
              ·
                refine ⟨37723709649368234081688581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100596559064981957551169549 37723709649368234081688581)
                ·
                  refine ⟨7073195559256543890316609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37723709649368234081688581 7073195559256543890316609)
                  ·
                    refine ⟨5304896669442407917737457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7073195559256543890316609 5304896669442407917737457)
                    ·
                      refine ⟨3978672502081805938303093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5304896669442407917737457 3978672502081805938303093)
                      ·
                        rfl

theorem cell23_7748437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_7748437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748437 prefixEnd_7748437 := by exact prefixLift 7748437
  have htrace : WordTrace (prefixWord ++ tailWord_7748437) baseStart_7748437 baseEnd_7748437 := by
    simpa [prefixWord, tailWord_7748437, baseEnd_7748437] using wordTrace_append hprefix tailTrace_7748437
  have hstable : (prefixWord ++ tailWord_7748437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748437).length < 2 ^ (prefixWord ++ tailWord_7748437).sum := by decide
  have hdescent : baseEnd_7748437 < baseStart_7748437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748483 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 5]
def baseStart_7748483 : Nat := 118140960795 + 7748483 * 2 ^ 59
def prefixEnd_7748483 : Nat := 4983230072969 + 3 ^ 40 * 7748483 * 2
def baseEnd_7748483 : Nat := 3978696122191912758327881

theorem tailTrace_7748483 : CollatzResearch.WordTrace tailWord_7748483 prefixEnd_7748483 3978696122191912758327881 := by
  unfold tailWord_7748483
  simp only [CollatzResearch.WordTrace]
  refine ⟨282610392387576901385386103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188406928258384600923590735 282610392387576901385386103)
  ·
    refine ⟨423915588581365352078079155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282610392387576901385386103 423915588581365352078079155)
    ·
      refine ⟨635873382872048028117118733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423915588581365352078079155 635873382872048028117118733)
      ·
        refine ⟨238452518577018010543919525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 635873382872048028117118733 238452518577018010543919525)
        ·
          refine ⟨44709847233190876976984911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238452518577018010543919525 44709847233190876976984911)
          ·
            refine ⟨67064770849786315465477367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44709847233190876976984911 67064770849786315465477367)
            ·
              refine ⟨100597156274679473198216051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67064770849786315465477367 100597156274679473198216051)
              ·
                refine ⟨150895734412019209797324077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100597156274679473198216051 150895734412019209797324077)
                ·
                  refine ⟨56585900404507203673996529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150895734412019209797324077 56585900404507203673996529)
                  ·
                    refine ⟨42439425303380402755497397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56585900404507203673996529 42439425303380402755497397)
                    ·
                      refine ⟨3978696122191912758327881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42439425303380402755497397 3978696122191912758327881)
                      ·
                        rfl

theorem cell23_7748483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_7748483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748483 prefixEnd_7748483 := by exact prefixLift 7748483
  have htrace : WordTrace (prefixWord ++ tailWord_7748483) baseStart_7748483 baseEnd_7748483 := by
    simpa [prefixWord, tailWord_7748483, baseEnd_7748483] using wordTrace_append hprefix tailTrace_7748483
  have hstable : (prefixWord ++ tailWord_7748483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748483).length < 2 ^ (prefixWord ++ tailWord_7748483).sum := by decide
  have hdescent : baseEnd_7748483 < baseStart_7748483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748500 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_7748500 : Nat := 118140960795 + 7748500 * 2 ^ 59
def prefixEnd_7748500 : Nat := 4983230072969 + 3 ^ 40 * 7748500 * 2
def baseEnd_7748500 : Nat := 3978704851363039191815303

theorem tailTrace_7748500 : CollatzResearch.WordTrace tailWord_7748500 prefixEnd_7748500 3978704851363039191815303 := by
  unfold tailWord_7748500
  simp only [CollatzResearch.WordTrace]
  refine ⟨141305506214257656644377477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188407341619010208859169969 141305506214257656644377477)
  ·
    refine ⟨26494782415173310620820777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141305506214257656644377477 26494782415173310620820777)
    ·
      refine ⟨19871086811379982965615583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26494782415173310620820777 19871086811379982965615583)
      ·
        refine ⟨29806630217069974448423375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19871086811379982965615583 29806630217069974448423375)
        ·
          refine ⟨44709945325604961672635063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29806630217069974448423375 44709945325604961672635063)
          ·
            refine ⟨67064917988407442508952595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44709945325604961672635063 67064917988407442508952595)
            ·
              refine ⟨100597376982611163763428893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67064917988407442508952595 100597376982611163763428893)
              ·
                refine ⟨37724016368479186411285835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100597376982611163763428893 37724016368479186411285835)
                ·
                  refine ⟨56586024552718779616928753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37724016368479186411285835 56586024552718779616928753)
                  ·
                    refine ⟨42439518414539084712696565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56586024552718779616928753 42439518414539084712696565)
                    ·
                      refine ⟨3978704851363039191815303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42439518414539084712696565 3978704851363039191815303)
                      ·
                        rfl

theorem cell23_7748500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_7748500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748500 prefixEnd_7748500 := by exact prefixLift 7748500
  have htrace : WordTrace (prefixWord ++ tailWord_7748500) baseStart_7748500 baseEnd_7748500 := by
    simpa [prefixWord, tailWord_7748500, baseEnd_7748500] using wordTrace_append hprefix tailTrace_7748500
  have hstable : (prefixWord ++ tailWord_7748500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748500).length < 2 ^ (prefixWord ++ tailWord_7748500).sum := by decide
  have hdescent : baseEnd_7748500 < baseStart_7748500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748523 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 4]
def baseStart_7748523 : Nat := 118140960795 + 7748523 * 2 ^ 59
def prefixEnd_7748523 : Nat := 4983230072969 + 3 ^ 40 * 7748523 * 2
def baseEnd_7748523 : Nat := 3978716661418092601827697

theorem tailTrace_7748523 : CollatzResearch.WordTrace tailWord_7748523 prefixEnd_7748523 3978716661418092601827697 := by
  unfold tailWord_7748523
  simp only [CollatzResearch.WordTrace]
  refine ⟨282611851307431988216842223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188407900871621325477894815 282611851307431988216842223)
  ·
    refine ⟨423917776961147982325263335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282611851307431988216842223 423917776961147982325263335)
    ·
      refine ⟨635876665441721973487895003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423917776961147982325263335 635876665441721973487895003)
      ·
        refine ⟨953814998162582960231842505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635876665441721973487895003 953814998162582960231842505)
        ·
          refine ⟨715361248621937220173881879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 953814998162582960231842505 715361248621937220173881879)
          ·
            refine ⟨1073041872932905830260822819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715361248621937220173881879 1073041872932905830260822819)
            ·
              refine ⟨1609562809399358745391234229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1073041872932905830260822819 1609562809399358745391234229)
              ·
                refine ⟨150896513381189882380428209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1609562809399358745391234229 150896513381189882380428209)
                ·
                  refine ⟨113172385035892411785321157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150896513381189882380428209 113172385035892411785321157)
                  ·
                    refine ⟨21219822194229827209747717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113172385035892411785321157 21219822194229827209747717)
                    ·
                      refine ⟨3978716661418092601827697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21219822194229827209747717 3978716661418092601827697)
                      ·
                        rfl

theorem cell23_7748523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 4].length) (baseStart_7748523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748523 prefixEnd_7748523 := by exact prefixLift 7748523
  have htrace : WordTrace (prefixWord ++ tailWord_7748523) baseStart_7748523 baseEnd_7748523 := by
    simpa [prefixWord, tailWord_7748523, baseEnd_7748523] using wordTrace_append hprefix tailTrace_7748523
  have hstable : (prefixWord ++ tailWord_7748523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748523).length < 2 ^ (prefixWord ++ tailWord_7748523).sum := by decide
  have hdescent : baseEnd_7748523 < baseStart_7748523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748600 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 5, 1, 4]
def baseStart_7748600 : Nat := 118140960795 + 7748600 * 2 ^ 59
def prefixEnd_7748600 : Nat := 4983230072969 + 3 ^ 40 * 7748600 * 2
def baseEnd_7748600 : Nat := 3978756199428488800564843

theorem tailTrace_7748600 : CollatzResearch.WordTrace tailWord_7748600 prefixEnd_7748600 3978756199428488800564843 := by
  unfold tailWord_7748600
  simp only [CollatzResearch.WordTrace]
  refine ⟨141307329864076515183697627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188409773152102020244930169 141307329864076515183697627)
  ·
    refine ⟨211960994796114772775546441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141307329864076515183697627 211960994796114772775546441)
    ·
      refine ⟨158970746097086079581659831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211960994796114772775546441 158970746097086079581659831)
      ·
        refine ⟨238456119145629119372489747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158970746097086079581659831 238456119145629119372489747)
        ·
          refine ⟨357684178718443679058734621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238456119145629119372489747 357684178718443679058734621)
          ·
            refine ⟨134131567019416379647025483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357684178718443679058734621 134131567019416379647025483)
            ·
              refine ⟨201197350529124569470538225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134131567019416379647025483 201197350529124569470538225)
              ·
                refine ⟨150898012896843427102903669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201197350529124569470538225 150898012896843427102903669)
                ·
                  refine ⟨14146688709079071290897219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150898012896843427102903669 14146688709079071290897219)
                  ·
                    refine ⟨21220033063618606936345829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14146688709079071290897219 21220033063618606936345829)
                    ·
                      refine ⟨3978756199428488800564843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21220033063618606936345829 3978756199428488800564843)
                      ·
                        rfl

theorem cell23_7748600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_7748600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748600 prefixEnd_7748600 := by exact prefixLift 7748600
  have htrace : WordTrace (prefixWord ++ tailWord_7748600) baseStart_7748600 baseEnd_7748600 := by
    simpa [prefixWord, tailWord_7748600, baseEnd_7748600] using wordTrace_append hprefix tailTrace_7748600
  have hstable : (prefixWord ++ tailWord_7748600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748600).length < 2 ^ (prefixWord ++ tailWord_7748600).sum := by decide
  have hdescent : baseEnd_7748600 < baseStart_7748600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748604 : List Nat := [2, 2, 2, 1, 2, 4, 1, 2, 2, 3, 2]
def baseStart_7748604 : Nat := 118140960795 + 7748604 * 2 ^ 59
def prefixEnd_7748604 : Nat := 4983230072969 + 3 ^ 40 * 7748604 * 2
def baseEnd_7748604 : Nat := 3978758253351106784914825

theorem tailTrace_7748604 : CollatzResearch.WordTrace tailWord_7748604 prefixEnd_7748604 3978758253351106784914825 := by
  unfold tailWord_7748604
  simp only [CollatzResearch.WordTrace]
  refine ⟨141307402810069269525270433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188409870413425692700360577 141307402810069269525270433)
  ·
    refine ⟨105980552107551952143952825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141307402810069269525270433 105980552107551952143952825)
    ·
      refine ⟨79485414080663964107964619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105980552107551952143952825 79485414080663964107964619)
      ·
        refine ⟨119228121120995946161946929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79485414080663964107964619 119228121120995946161946929)
        ·
          refine ⟨89421090840746959621460197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119228121120995946161946929 89421090840746959621460197)
          ·
            refine ⟨16766454532640054929023787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89421090840746959621460197 16766454532640054929023787)
            ·
              refine ⟨25149681798960082393535681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16766454532640054929023787 25149681798960082393535681)
              ·
                refine ⟨18862261349220061795151761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25149681798960082393535681 18862261349220061795151761)
                ·
                  refine ⟨14146696011915046346363821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18862261349220061795151761 14146696011915046346363821)
                  ·
                    refine ⟨5305011004468142379886433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14146696011915046346363821 5305011004468142379886433)
                    ·
                      refine ⟨3978758253351106784914825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5305011004468142379886433 3978758253351106784914825)
                      ·
                        rfl

theorem cell23_7748604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 2, 3, 2].length) (baseStart_7748604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748604 prefixEnd_7748604 := by exact prefixLift 7748604
  have htrace : WordTrace (prefixWord ++ tailWord_7748604) baseStart_7748604 baseEnd_7748604 := by
    simpa [prefixWord, tailWord_7748604, baseEnd_7748604] using wordTrace_append hprefix tailTrace_7748604
  have hstable : (prefixWord ++ tailWord_7748604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748604).length < 2 ^ (prefixWord ++ tailWord_7748604).sum := by decide
  have hdescent : baseEnd_7748604 < baseStart_7748604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748634 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2]
def baseStart_7748634 : Nat := 118140960795 + 7748634 * 2 ^ 59
def prefixEnd_7748634 : Nat := 4983230072969 + 3 ^ 40 * 7748634 * 2
def baseEnd_7748634 : Nat := 3978773657770741667539687

theorem tailTrace_7748634 : CollatzResearch.WordTrace tailWord_7748634 prefixEnd_7748634 3978773657770741667539687 := by
  unfold tailWord_7748634
  simp only [CollatzResearch.WordTrace]
  refine ⟨70653974952507463543533239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188410599873353236116088637 70653974952507463543533239)
  ·
    refine ⟨105980962428761195315299859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70653974952507463543533239 105980962428761195315299859)
    ·
      refine ⟨158971443643141792972949789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105980962428761195315299859 158971443643141792972949789)
      ·
        refine ⟨59614291366178172364856171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158971443643141792972949789 59614291366178172364856171)
        ·
          refine ⟨89421437049267258547284257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59614291366178172364856171 89421437049267258547284257)
          ·
            refine ⟨67066077786950443910463193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89421437049267258547284257 67066077786950443910463193)
            ·
              refine ⟨50299558340212832932847395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67066077786950443910463193 50299558340212832932847395)
              ·
                refine ⟨75449337510319249399271093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50299558340212832932847395 75449337510319249399271093)
                ·
                  refine ⟨7073375391592429631181665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75449337510319249399271093 7073375391592429631181665)
                  ·
                    refine ⟨5305031543694322223386249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7073375391592429631181665 5305031543694322223386249)
                    ·
                      refine ⟨3978773657770741667539687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5305031543694322223386249 3978773657770741667539687)
                      ·
                        rfl

theorem cell23_7748634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_7748634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748634 prefixEnd_7748634 := by exact prefixLift 7748634
  have htrace : WordTrace (prefixWord ++ tailWord_7748634) baseStart_7748634 baseEnd_7748634 := by
    simpa [prefixWord, tailWord_7748634, baseEnd_7748634] using wordTrace_append hprefix tailTrace_7748634
  have hstable : (prefixWord ++ tailWord_7748634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748634).length < 2 ^ (prefixWord ++ tailWord_7748634).sum := by decide
  have hdescent : baseEnd_7748634 < baseStart_7748634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748651 : List Nat := [1, 1, 1, 1, 2, 1, 6, 5, 1, 2, 2]
def baseStart_7748651 : Nat := 118140960795 + 7748651 * 2 ^ 59
def prefixEnd_7748651 : Nat := 4983230072969 + 3 ^ 40 * 7748651 * 2
def baseEnd_7748651 : Nat := 3978782386941868101027109

theorem tailTrace_7748651 : CollatzResearch.WordTrace tailWord_7748651 prefixEnd_7748651 3978782386941868101027109 := by
  unfold tailWord_7748651
  simp only [CollatzResearch.WordTrace]
  refine ⟨282616519850968266077501807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188411013233978844051667871 282616519850968266077501807)
  ·
    refine ⟨423924779776452399116252711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282616519850968266077501807 423924779776452399116252711)
    ·
      refine ⟨635887169664678598674379067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423924779776452399116252711 635887169664678598674379067)
      ·
        refine ⟨953830754497017898011568601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635887169664678598674379067 953830754497017898011568601)
        ·
          refine ⟨715373065872763423508676451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 953830754497017898011568601 715373065872763423508676451)
          ·
            refine ⟨1073059598809145135263014677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715373065872763423508676451 1073059598809145135263014677)
            ·
              refine ⟨50299668694178678215453813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1073059598809145135263014677 50299668694178678215453813)
              ·
                refine ⟨4715593940079251082698795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50299668694178678215453813 4715593940079251082698795)
                ·
                  refine ⟨7073390910118876624048193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715593940079251082698795 7073390910118876624048193)
                  ·
                    refine ⟨5305043182589157468036145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7073390910118876624048193 5305043182589157468036145)
                    ·
                      refine ⟨3978782386941868101027109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5305043182589157468036145 3978782386941868101027109)
                      ·
                        rfl

theorem cell23_7748651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 1, 2, 2].length) (baseStart_7748651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748651 prefixEnd_7748651 := by exact prefixLift 7748651
  have htrace : WordTrace (prefixWord ++ tailWord_7748651) baseStart_7748651 baseEnd_7748651 := by
    simpa [prefixWord, tailWord_7748651, baseEnd_7748651] using wordTrace_append hprefix tailTrace_7748651
  have hstable : (prefixWord ++ tailWord_7748651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748651).length < 2 ^ (prefixWord ++ tailWord_7748651).sum := by decide
  have hdescent : baseEnd_7748651 < baseStart_7748651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748668 : List Nat := [2, 2, 2, 2, 2, 3, 1, 4, 1, 2, 2]
def baseStart_7748668 : Nat := 118140960795 + 7748668 * 2 ^ 59
def prefixEnd_7748668 : Nat := 4983230072969 + 3 ^ 40 * 7748668 * 2
def baseEnd_7748668 : Nat := 3978791116112994534514531

theorem tailTrace_7748668 : CollatzResearch.WordTrace tailWord_7748668 prefixEnd_7748668 3978791116112994534514531 := by
  unfold tailWord_7748668
  simp only [CollatzResearch.WordTrace]
  refine ⟨141308569945953338990435329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188411426594604451987247105 141308569945953338990435329)
  ·
    refine ⟨105981427459465004242826497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141308569945953338990435329 105981427459465004242826497)
    ·
      refine ⟨79486070594598753182119873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105981427459465004242826497 79486070594598753182119873)
      ·
        refine ⟨59614552945949064886589905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79486070594598753182119873 59614552945949064886589905)
        ·
          refine ⟨44710914709461798664942429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59614552945949064886589905 44710914709461798664942429)
          ·
            refine ⟨16766593016048174499353411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44710914709461798664942429 16766593016048174499353411)
            ·
              refine ⟨25149889524072261749030117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16766593016048174499353411 25149889524072261749030117)
              ·
                refine ⟨4715604285763549077943147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25149889524072261749030117 4715604285763549077943147)
                ·
                  refine ⟨7073406428645323616914721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715604285763549077943147 7073406428645323616914721)
                  ·
                    refine ⟨5305054821483992712686041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7073406428645323616914721 5305054821483992712686041)
                    ·
                      refine ⟨3978791116112994534514531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5305054821483992712686041 3978791116112994534514531)
                      ·
                        rfl

theorem cell23_7748668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_7748668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748668 prefixEnd_7748668 := by exact prefixLift 7748668
  have htrace : WordTrace (prefixWord ++ tailWord_7748668) baseStart_7748668 baseEnd_7748668 := by
    simpa [prefixWord, tailWord_7748668, baseEnd_7748668] using wordTrace_append hprefix tailTrace_7748668
  have hstable : (prefixWord ++ tailWord_7748668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748668).length < 2 ^ (prefixWord ++ tailWord_7748668).sum := by decide
  have hdescent : baseEnd_7748668 < baseStart_7748668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748702 : List Nat := [4, 4, 1, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_7748702 : Nat := 118140960795 + 7748702 * 2 ^ 59
def prefixEnd_7748702 : Nat := 4983230072969 + 3 ^ 40 * 7748702 * 2
def baseEnd_7748702 : Nat := 3978808574455247401489375

theorem tailTrace_7748702 : CollatzResearch.WordTrace tailWord_7748702 prefixEnd_7748702 3978808574455247401489375 := by
  unfold tailWord_7748702
  simp only [CollatzResearch.WordTrace]
  refine ⟨35327297496722937723451045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188412253315855667858405573 35327297496722937723451045)
  ·
    refine ⟨6623868280635550823147071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35327297496722937723451045 6623868280635550823147071)
    ·
      refine ⟨9935802420953326234720607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6623868280635550823147071 9935802420953326234720607)
      ·
        refine ⟨14903703631429989352080911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9935802420953326234720607 14903703631429989352080911)
        ·
          refine ⟨22355555447144984028121367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14903703631429989352080911 22355555447144984028121367)
          ·
            refine ⟨33533333170717476042182051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22355555447144984028121367 33533333170717476042182051)
            ·
              refine ⟨50299999756076214063273077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33533333170717476042182051 50299999756076214063273077)
              ·
                refine ⟨4715624977132145068431851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50299999756076214063273077 4715624977132145068431851)
                ·
                  refine ⟨7073437465698217602647777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715624977132145068431851 7073437465698217602647777)
                  ·
                    refine ⟨5305078099273663201985833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7073437465698217602647777 5305078099273663201985833)
                    ·
                      refine ⟨3978808574455247401489375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5305078099273663201985833 3978808574455247401489375)
                      ·
                        rfl

theorem cell23_7748702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_7748702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748702 prefixEnd_7748702 := by exact prefixLift 7748702
  have htrace : WordTrace (prefixWord ++ tailWord_7748702) baseStart_7748702 baseEnd_7748702 := by
    simpa [prefixWord, tailWord_7748702, baseEnd_7748702] using wordTrace_append hprefix tailTrace_7748702
  have hstable : (prefixWord ++ tailWord_7748702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748702).length < 2 ^ (prefixWord ++ tailWord_7748702).sum := by decide
  have hdescent : baseEnd_7748702 < baseStart_7748702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748711 : List Nat := [1, 1, 5, 1, 1, 4, 1, 3, 1, 3, 2]
def baseStart_7748711 : Nat := 118140960795 + 7748711 * 2 ^ 59
def prefixEnd_7748711 : Nat := 4983230072969 + 3 ^ 40 * 7748711 * 2
def baseEnd_7748711 : Nat := 3978813195781137866276833

theorem tailTrace_7748711 : CollatzResearch.WordTrace tailWord_7748711 prefixEnd_7748711 3978813195781137866276833 := by
  unfold tailWord_7748711
  simp only [CollatzResearch.WordTrace]
  refine ⟨282618708230750896324685987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188412472153833930883123991 282618708230750896324685987)
  ·
    refine ⟨423928062346126344487028981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282618708230750896324685987 423928062346126344487028981)
    ·
      refine ⟨39743255844949344795658967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 423928062346126344487028981 39743255844949344795658967)
      ·
        refine ⟨59614883767424017193488451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39743255844949344795658967 59614883767424017193488451)
        ·
          refine ⟨89422325651136025790232677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59614883767424017193488451 89422325651136025790232677)
          ·
            refine ⟨16766686059588004835668627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89422325651136025790232677 16766686059588004835668627)
            ·
              refine ⟨25150029089382007253502941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16766686059588004835668627 25150029089382007253502941)
              ·
                refine ⟨9431260908518252720063603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25150029089382007253502941 9431260908518252720063603)
                ·
                  refine ⟨14146891362777379080095405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9431260908518252720063603 14146891362777379080095405)
                  ·
                    refine ⟨5305084261041517155035777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14146891362777379080095405 5305084261041517155035777)
                    ·
                      refine ⟨3978813195781137866276833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5305084261041517155035777 3978813195781137866276833)
                      ·
                        rfl

theorem cell23_7748711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_7748711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748711 prefixEnd_7748711 := by exact prefixLift 7748711
  have htrace : WordTrace (prefixWord ++ tailWord_7748711) baseStart_7748711 baseEnd_7748711 := by
    simpa [prefixWord, tailWord_7748711, baseEnd_7748711] using wordTrace_append hprefix tailTrace_7748711
  have hstable : (prefixWord ++ tailWord_7748711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748711).length < 2 ^ (prefixWord ++ tailWord_7748711).sum := by decide
  have hdescent : baseEnd_7748711 < baseStart_7748711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748717 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 2, 6]
def baseStart_7748717 : Nat := 118140960795 + 7748717 * 2 ^ 59
def prefixEnd_7748717 : Nat := 4983230072969 + 3 ^ 40 * 7748717 * 2
def baseEnd_7748717 : Nat := 1326272092221688280933935

theorem tailTrace_7748717 : CollatzResearch.WordTrace tailWord_7748717 prefixEnd_7748717 1326272092221688280933935 := by
  unfold tailWord_7748717
  simp only [CollatzResearch.WordTrace]
  refine ⟨282618927068729159349404405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188412618045819439566269603 282618927068729159349404405)
  ·
    refine ⟨26495524412693358689006663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 282618927068729159349404405 26495524412693358689006663)
    ·
      refine ⟨39743286619040038033509995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26495524412693358689006663 39743286619040038033509995)
      ·
        refine ⟨59614929928560057050264993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39743286619040038033509995 59614929928560057050264993)
        ·
          refine ⟨44711197446420042787698745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59614929928560057050264993 44711197446420042787698745)
          ·
            refine ⟨33533398084815032090774059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44711197446420042787698745 33533398084815032090774059)
            ·
              refine ⟨50300097127222548136161089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33533398084815032090774059 50300097127222548136161089)
              ·
                refine ⟨37725072845416911102120817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50300097127222548136161089 37725072845416911102120817)
                ·
                  refine ⟨28293804634062683326590613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37725072845416911102120817 28293804634062683326590613)
                  ·
                    refine ⟨1326272092221688280933935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28293804634062683326590613 1326272092221688280933935)
                    ·
                      rfl

theorem cell23_7748717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_7748717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748717 prefixEnd_7748717 := by exact prefixLift 7748717
  have htrace : WordTrace (prefixWord ++ tailWord_7748717) baseStart_7748717 baseEnd_7748717 := by
    simpa [prefixWord, tailWord_7748717, baseEnd_7748717] using wordTrace_append hprefix tailTrace_7748717
  have hstable : (prefixWord ++ tailWord_7748717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748717).length < 2 ^ (prefixWord ++ tailWord_7748717).sum := by decide
  have hdescent : baseEnd_7748717 < baseStart_7748717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748718 : List Nat := [4, 1, 2, 2, 1, 4, 1, 2, 2, 1, 3]
def baseStart_7748718 : Nat := 118140960795 + 7748718 * 2 ^ 59
def prefixEnd_7748718 : Nat := 4983230072969 + 3 ^ 40 * 7748718 * 2
def baseEnd_7748718 : Nat := 3978816790145719338889301

theorem tailTrace_7748718 : CollatzResearch.WordTrace tailWord_7748718 prefixEnd_7748718 3978816790145719338889301 := by
  unfold tailWord_7748718
  simp only [CollatzResearch.WordTrace]
  refine ⟨35327370442715692065023851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188412642361150357680127205 35327370442715692065023851)
  ·
    refine ⟨52991055664073538097535777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35327370442715692065023851 52991055664073538097535777)
    ·
      refine ⟨39743291748055153573151833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52991055664073538097535777 39743291748055153573151833)
      ·
        refine ⟨29807468811041365179863875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39743291748055153573151833 29807468811041365179863875)
        ·
          refine ⟨44711203216562047769795813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29807468811041365179863875 44711203216562047769795813)
          ·
            refine ⟨8383350603105383956836715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44711203216562047769795813 8383350603105383956836715)
            ·
              refine ⟨12575025904658075935255073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8383350603105383956836715 12575025904658075935255073)
              ·
                refine ⟨9431269428493556951441305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12575025904658075935255073 9431269428493556951441305)
                ·
                  refine ⟨7073452071370167713580979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9431269428493556951441305 7073452071370167713580979)
                  ·
                    refine ⟨10610178107055251570371469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7073452071370167713580979 10610178107055251570371469)
                    ·
                      refine ⟨3978816790145719338889301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10610178107055251570371469 3978816790145719338889301)
                      ·
                        rfl

theorem cell23_7748718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_7748718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748718 prefixEnd_7748718 := by exact prefixLift 7748718
  have htrace : WordTrace (prefixWord ++ tailWord_7748718) baseStart_7748718 baseEnd_7748718 := by
    simpa [prefixWord, tailWord_7748718, baseEnd_7748718] using wordTrace_append hprefix tailTrace_7748718
  have hstable : (prefixWord ++ tailWord_7748718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748718).length < 2 ^ (prefixWord ++ tailWord_7748718).sum := by decide
  have hdescent : baseEnd_7748718 < baseStart_7748718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748757 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 4, 3, 3]
def baseStart_7748757 : Nat := 118140960795 + 7748757 * 2 ^ 59
def prefixEnd_7748757 : Nat := 4983230072969 + 3 ^ 40 * 7748757 * 2
def baseEnd_7748757 : Nat := 3978836815891244686301621

theorem tailTrace_7748757 : CollatzResearch.WordTrace tailWord_7748757 prefixEnd_7748757 3978836815891244686301621 := by
  unfold tailWord_7748757
  simp only [CollatzResearch.WordTrace]
  refine ⟨282620385988584246180860525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188413590659056164120573683 282620385988584246180860525)
  ·
    refine ⟨105982644745719092317822697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282620385988584246180860525 105982644745719092317822697)
    ·
      refine ⟨79486983559289319238367023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105982644745719092317822697 79486983559289319238367023)
      ·
        refine ⟨119230475338933978857550535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79486983559289319238367023 119230475338933978857550535)
        ·
          refine ⟨178845713008400968286325803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119230475338933978857550535 178845713008400968286325803)
          ·
            refine ⟨268268569512601452429488705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178845713008400968286325803 268268569512601452429488705)
            ·
              refine ⟨201201427134451089322116529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268268569512601452429488705 201201427134451089322116529)
              ·
                refine ⟨150901070350838316991587397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201201427134451089322116529 150901070350838316991587397)
                ·
                  refine ⟨28293950690782184435922637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150901070350838316991587397 28293950690782184435922637)
                  ·
                    refine ⟨10610231509043319163470989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28293950690782184435922637 10610231509043319163470989)
                    ·
                      refine ⟨3978836815891244686301621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10610231509043319163470989 3978836815891244686301621)
                      ·
                        rfl

theorem cell23_7748757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_7748757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748757 prefixEnd_7748757 := by exact prefixLift 7748757
  have htrace : WordTrace (prefixWord ++ tailWord_7748757) baseStart_7748757 baseEnd_7748757 := by
    simpa [prefixWord, tailWord_7748757, baseEnd_7748757] using wordTrace_append hprefix tailTrace_7748757
  have hstable : (prefixWord ++ tailWord_7748757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748757).length < 2 ^ (prefixWord ++ tailWord_7748757).sum := by decide
  have hdescent : baseEnd_7748757 < baseStart_7748757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748781 : List Nat := [1, 5, 2, 1, 3, 2, 1, 1, 7]
def baseStart_7748781 : Nat := 118140960795 + 7748781 * 2 ^ 59
def prefixEnd_7748781 : Nat := 4983230072969 + 3 ^ 40 * 7748781 * 2
def baseEnd_7748781 : Nat := 442094348825216954711279

theorem tailTrace_7748781 : CollatzResearch.WordTrace tailWord_7748781 prefixEnd_7748781 442094348825216954711279 := by
  unfold tailWord_7748781
  simp only [CollatzResearch.WordTrace]
  refine ⟨282621261340497298279734197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188414174226998198853156131 282621261340497298279734197)
  ·
    refine ⟨26495743250671621713725081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 282621261340497298279734197 26495743250671621713725081)
    ·
      refine ⟨19871807438003716285293811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26495743250671621713725081 19871807438003716285293811)
      ·
        refine ⟨29807711157005574427940717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19871807438003716285293811 29807711157005574427940717)
        ·
          refine ⟨11177891683877090410477769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29807711157005574427940717 11177891683877090410477769)
          ·
            refine ⟨8383418762907817807858327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11177891683877090410477769 8383418762907817807858327)
            ·
              refine ⟨12575128144361726711787491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8383418762907817807858327 12575128144361726711787491)
              ·
                refine ⟨18862692216542590067681237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12575128144361726711787491 18862692216542590067681237)
                ·
                  refine ⟨442094348825216954711279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18862692216542590067681237 442094348825216954711279)
                  ·
                    rfl

theorem cell23_7748781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_7748781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748781 prefixEnd_7748781 := by exact prefixLift 7748781
  have htrace : WordTrace (prefixWord ++ tailWord_7748781) baseStart_7748781 baseEnd_7748781 := by
    simpa [prefixWord, tailWord_7748781, baseEnd_7748781] using wordTrace_append hprefix tailTrace_7748781
  have hstable : (prefixWord ++ tailWord_7748781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748781).length < 2 ^ (prefixWord ++ tailWord_7748781).sum := by decide
  have hdescent : baseEnd_7748781 < baseStart_7748781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748797 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 3, 3, 4]
def baseStart_7748797 : Nat := 118140960795 + 7748797 * 2 ^ 59
def prefixEnd_7748797 : Nat := 4983230072969 + 3 ^ 40 * 7748797 * 2
def baseEnd_7748797 : Nat := 3978857355117424529801437

theorem tailTrace_7748797 : CollatzResearch.WordTrace tailWord_7748797 prefixEnd_7748797 3978857355117424529801437 := by
  unfold tailWord_7748797
  simp only [CollatzResearch.WordTrace]
  refine ⟨282621844908439333012316645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188414563272292888674877763 282621844908439333012316645)
  ·
    refine ⟨52991595920332374939809371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282621844908439333012316645 52991595920332374939809371)
    ·
      refine ⟨79487393880498562409714057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52991595920332374939809371 79487393880498562409714057)
      ·
        refine ⟨59615545410373921807285543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79487393880498562409714057 59615545410373921807285543)
        ·
          refine ⟨89423318115560882710928315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59615545410373921807285543 89423318115560882710928315)
          ·
            refine ⟨134134977173341324066392473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89423318115560882710928315 134134977173341324066392473)
            ·
              refine ⟨100601232880005993049794355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134134977173341324066392473 100601232880005993049794355)
              ·
                refine ⟨150901849320008989574691533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100601232880005993049794355 150901849320008989574691533)
                ·
                  refine ⟨56588193495003371090509325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150901849320008989574691533 56588193495003371090509325)
                  ·
                    refine ⟨21220572560626264158940997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56588193495003371090509325 21220572560626264158940997)
                    ·
                      refine ⟨3978857355117424529801437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21220572560626264158940997 3978857355117424529801437)
                      ·
                        rfl

theorem cell23_7748797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_7748797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748797 prefixEnd_7748797 := by exact prefixLift 7748797
  have htrace : WordTrace (prefixWord ++ tailWord_7748797) baseStart_7748797 baseEnd_7748797 := by
    simpa [prefixWord, tailWord_7748797, baseEnd_7748797] using wordTrace_append hprefix tailTrace_7748797
  have hstable : (prefixWord ++ tailWord_7748797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748797).length < 2 ^ (prefixWord ++ tailWord_7748797).sum := by decide
  have hdescent : baseEnd_7748797 < baseStart_7748797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748868 : List Nat := [2, 3, 2, 2, 2, 3, 1, 1, 2, 2, 3]
def baseStart_7748868 : Nat := 118140960795 + 7748868 * 2 ^ 59
def prefixEnd_7748868 : Nat := 4983230072969 + 3 ^ 40 * 7748868 * 2
def baseEnd_7748868 : Nat := 3978893812243893752013611

theorem tailTrace_7748868 : CollatzResearch.WordTrace tailWord_7748868 prefixEnd_7748868 3978893812243893752013611 := by
  unfold tailWord_7748868
  simp only [CollatzResearch.WordTrace]
  refine ⟨141312217245591056069075629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188416289660788074758767505 141312217245591056069075629)
  ·
    refine ⟨52992081467096646025903361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141312217245591056069075629 52992081467096646025903361)
    ·
      refine ⟨39744061100322484519427521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52992081467096646025903361 39744061100322484519427521)
      ·
        refine ⟨29808045825241863389570641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39744061100322484519427521 29808045825241863389570641)
        ·
          refine ⟨22356034368931397542177981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29808045825241863389570641 22356034368931397542177981)
          ·
            refine ⟨8383512888349274078316743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22356034368931397542177981 8383512888349274078316743)
            ·
              refine ⟨12575269332523911117475115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8383512888349274078316743 12575269332523911117475115)
              ·
                refine ⟨18862903998785866676212673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12575269332523911117475115 18862903998785866676212673)
                ·
                  refine ⟨14147177999089400007159505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18862903998785866676212673 14147177999089400007159505)
                  ·
                    refine ⟨10610383499317050005369629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14147177999089400007159505 10610383499317050005369629)
                    ·
                      refine ⟨3978893812243893752013611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10610383499317050005369629 3978893812243893752013611)
                      ·
                        rfl

theorem cell23_7748868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_7748868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748868 prefixEnd_7748868 := by exact prefixLift 7748868
  have htrace : WordTrace (prefixWord ++ tailWord_7748868) baseStart_7748868 baseEnd_7748868 := by
    simpa [prefixWord, tailWord_7748868, baseEnd_7748868] using wordTrace_append hprefix tailTrace_7748868
  have hstable : (prefixWord ++ tailWord_7748868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748868).length < 2 ^ (prefixWord ++ tailWord_7748868).sum := by decide
  have hdescent : baseEnd_7748868 < baseStart_7748868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7748932 : List Nat := [2, 3, 4, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_7748932 : Nat := 118140960795 + 7748932 * 2 ^ 59
def prefixEnd_7748932 : Nat := 4983230072969 + 3 ^ 40 * 7748932 * 2
def baseEnd_7748932 : Nat := 3978926675005781501613317

theorem tailTrace_7748932 : CollatzResearch.WordTrace tailWord_7748932 prefixEnd_7748932 3978926675005781501613317 := by
  unfold tailWord_7748932
  simp only [CollatzResearch.WordTrace]
  refine ⟨141313384381475125534240525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188417845841966834045654033 141313384381475125534240525)
  ·
    refine ⟨52992519143053172075340197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141313384381475125534240525 52992519143053172075340197)
    ·
      refine ⟨9936097339322469764126287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52992519143053172075340197 9936097339322469764126287)
      ·
        refine ⟨14904146008983704646189431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9936097339322469764126287 14904146008983704646189431)
        ·
          refine ⟨22356219013475556969284147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14904146008983704646189431 22356219013475556969284147)
          ·
            refine ⟨33534328520213335453926221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22356219013475556969284147 33534328520213335453926221)
            ·
              refine ⟨12575373195080000795222333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33534328520213335453926221 12575373195080000795222333)
              ·
                refine ⟨4715764948155000298208375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12575373195080000795222333 4715764948155000298208375)
                ·
                  refine ⟨7073647422232500447312563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715764948155000298208375 7073647422232500447312563)
                  ·
                    refine ⟨10610471133348750670968845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7073647422232500447312563 10610471133348750670968845)
                    ·
                      refine ⟨3978926675005781501613317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10610471133348750670968845 3978926675005781501613317)
                      ·
                        rfl

theorem cell23_7748932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_7748932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7748932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7748932 prefixEnd_7748932 := by exact prefixLift 7748932
  have htrace : WordTrace (prefixWord ++ tailWord_7748932) baseStart_7748932 baseEnd_7748932 := by
    simpa [prefixWord, tailWord_7748932, baseEnd_7748932] using wordTrace_append hprefix tailTrace_7748932
  have hstable : (prefixWord ++ tailWord_7748932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7748932).length < 2 ^ (prefixWord ++ tailWord_7748932).sum := by decide
  have hdescent : baseEnd_7748932 < baseStart_7748932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7748932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749004 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 2, 6]
def baseStart_7749004 : Nat := 118140960795 + 7749004 * 2 ^ 59
def prefixEnd_7749004 : Nat := 4983230072969 + 3 ^ 40 * 7749004 * 2
def baseEnd_7749004 : Nat := 1326321215204301739970995

theorem tailTrace_7749004 : CollatzResearch.WordTrace tailWord_7749004 prefixEnd_7749004 1326321215204301739970995 := by
  unfold tailWord_7749004
  simp only [CollatzResearch.WordTrace]
  refine ⟨141314697409344703682551033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188419596545792938243401377 141314697409344703682551033)
  ·
    refine ⟨105986023057008527761913275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141314697409344703682551033 105986023057008527761913275)
    ·
      refine ⟨158979034585512791642869913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105986023057008527761913275 158979034585512791642869913)
      ·
        refine ⟨119234275939134593732152435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158979034585512791642869913 119234275939134593732152435)
        ·
          refine ⟨178851413908701890598228653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119234275939134593732152435 178851413908701890598228653)
          ·
            refine ⟨67069280215763208974335745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178851413908701890598228653 67069280215763208974335745)
            ·
              refine ⟨50301960161822406730751809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67069280215763208974335745 50301960161822406730751809)
              ·
                refine ⟨37726470121366805048063857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50301960161822406730751809 37726470121366805048063857)
                ·
                  refine ⟨28294852591025103786047893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37726470121366805048063857 28294852591025103786047893)
                  ·
                    refine ⟨1326321215204301739970995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28294852591025103786047893 1326321215204301739970995)
                    ·
                      rfl

theorem cell23_7749004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_7749004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749004 prefixEnd_7749004 := by exact prefixLift 7749004
  have htrace : WordTrace (prefixWord ++ tailWord_7749004) baseStart_7749004 baseEnd_7749004 := by
    simpa [prefixWord, tailWord_7749004, baseEnd_7749004] using wordTrace_append hprefix tailTrace_7749004
  have hstable : (prefixWord ++ tailWord_7749004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749004).length < 2 ^ (prefixWord ++ tailWord_7749004).sum := by decide
  have hdescent : baseEnd_7749004 < baseStart_7749004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749006 : List Nat := [4, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2]
def baseStart_7749006 : Nat := 118140960795 + 7749006 * 2 ^ 59
def prefixEnd_7749006 : Nat := 4983230072969 + 3 ^ 40 * 7749006 * 2
def baseEnd_7749006 : Nat := 3978964672574214212087977

theorem tailTrace_7749006 : CollatzResearch.WordTrace tailWord_7749006 prefixEnd_7749006 3978964672574214212087977 := by
  unfold tailWord_7749006
  simp only [CollatzResearch.WordTrace]
  refine ⟨35328683470585270213334359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188419645176454774471116581 35328683470585270213334359)
  ·
    refine ⟨52993025205877905320001539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35328683470585270213334359 52993025205877905320001539)
    ·
      refine ⟨79489537808816857980002309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52993025205877905320001539 79489537808816857980002309)
      ·
        refine ⟨14904288339153160871250433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79489537808816857980002309 14904288339153160871250433)
        ·
          refine ⟨11178216254364870653437825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14904288339153160871250433 11178216254364870653437825)
          ·
            refine ⟨8383662190773652990078369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11178216254364870653437825 8383662190773652990078369)
            ·
              refine ⟨6287746643080239742558777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8383662190773652990078369 6287746643080239742558777)
              ·
                refine ⟨4715809982310179806919083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6287746643080239742558777 4715809982310179806919083)
                ·
                  refine ⟨7073714973465269710378625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715809982310179806919083 7073714973465269710378625)
                  ·
                    refine ⟨5305286230098952282783969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7073714973465269710378625 5305286230098952282783969)
                    ·
                      refine ⟨3978964672574214212087977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5305286230098952282783969 3978964672574214212087977)
                      ·
                        rfl

theorem cell23_7749006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_7749006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749006 prefixEnd_7749006 := by exact prefixLift 7749006
  have htrace : WordTrace (prefixWord ++ tailWord_7749006) baseStart_7749006 baseEnd_7749006 := by
    simpa [prefixWord, tailWord_7749006, baseEnd_7749006] using wordTrace_append hprefix tailTrace_7749006
  have hstable : (prefixWord ++ tailWord_7749006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749006).length < 2 ^ (prefixWord ++ tailWord_7749006).sum := by decide
  have hdescent : baseEnd_7749006 < baseStart_7749006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749021 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 2, 6]
def baseStart_7749021 : Nat := 118140960795 + 7749021 * 2 ^ 59
def prefixEnd_7749021 : Nat := 4983230072969 + 3 ^ 40 * 7749021 * 2
def baseEnd_7749021 : Nat := 1326324124928010551133469

theorem tailTrace_7749021 : CollatzResearch.WordTrace tailWord_7749021 prefixEnd_7749021 1326324124928010551133469 := by
  unfold tailWord_7749021
  simp only [CollatzResearch.WordTrace]
  refine ⟨282630014859627819268470917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188420009906418546178980611 282630014859627819268470917)
  ·
    refine ⟨52993127786180216112838297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282630014859627819268470917 52993127786180216112838297)
    ·
      refine ⟨39744845839635162084628723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52993127786180216112838297 39744845839635162084628723)
      ·
        refine ⟨59617268759452743126943085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39744845839635162084628723 59617268759452743126943085)
        ·
          refine ⟨22356475784794778672603657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59617268759452743126943085 22356475784794778672603657)
          ·
            refine ⟨16767356838596084004452743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22356475784794778672603657 16767356838596084004452743)
            ·
              refine ⟨25151035257894126006679115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16767356838596084004452743 25151035257894126006679115)
              ·
                refine ⟨37726552886841189010018673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25151035257894126006679115 37726552886841189010018673)
                ·
                  refine ⟨28294914665130891757514005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37726552886841189010018673 28294914665130891757514005)
                  ·
                    refine ⟨1326324124928010551133469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28294914665130891757514005 1326324124928010551133469)
                    ·
                      rfl

theorem cell23_7749021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_7749021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749021 prefixEnd_7749021 := by exact prefixLift 7749021
  have htrace : WordTrace (prefixWord ++ tailWord_7749021) baseStart_7749021 baseEnd_7749021 := by
    simpa [prefixWord, tailWord_7749021, baseEnd_7749021] using wordTrace_append hprefix tailTrace_7749021
  have hstable : (prefixWord ++ tailWord_7749021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749021).length < 2 ^ (prefixWord ++ tailWord_7749021).sum := by decide
  have hdescent : baseEnd_7749021 < baseStart_7749021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749028 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 6, 2, 2]
def baseStart_7749028 : Nat := 118140960795 + 7749028 * 2 ^ 59
def prefixEnd_7749028 : Nat := 4983230072969 + 3 ^ 40 * 7749028 * 2
def baseEnd_7749028 : Nat := 3978975969148613126012875

theorem tailTrace_7749028 : CollatzResearch.WordTrace tailWord_7749028 prefixEnd_7749028 3978975969148613126012875 := by
  unfold tailWord_7749028
  simp only [CollatzResearch.WordTrace]
  refine ⟨141315135085301229731987869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188420180113734972975983825 141315135085301229731987869)
  ·
    refine ⟨52993175656987961149495451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141315135085301229731987869 52993175656987961149495451)
    ·
      refine ⟨79489763485481941724243177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52993175656987961149495451 79489763485481941724243177)
      ·
        refine ⟨59617322614111456293182383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79489763485481941724243177 59617322614111456293182383)
        ·
          refine ⟨89425983921167184439773575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59617322614111456293182383 89425983921167184439773575)
          ·
            refine ⟨134138975881750776659660363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89425983921167184439773575 134138975881750776659660363)
            ·
              refine ⟨201208463822626164989490545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134138975881750776659660363 201208463822626164989490545)
              ·
                refine ⟨150906347866969623742117909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201208463822626164989490545 150906347866969623742117909)
                ·
                  refine ⟨7073735056264201112911777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150906347866969623742117909 7073735056264201112911777)
                  ·
                    refine ⟨5305301292198150834683833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7073735056264201112911777 5305301292198150834683833)
                    ·
                      refine ⟨3978975969148613126012875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5305301292198150834683833 3978975969148613126012875)
                      ·
                        rfl

theorem cell23_7749028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_7749028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749028 prefixEnd_7749028 := by exact prefixLift 7749028
  have htrace : WordTrace (prefixWord ++ tailWord_7749028) baseStart_7749028 baseEnd_7749028 := by
    simpa [prefixWord, tailWord_7749028, baseEnd_7749028] using wordTrace_append hprefix tailTrace_7749028
  have hstable : (prefixWord ++ tailWord_7749028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749028).length < 2 ^ (prefixWord ++ tailWord_7749028).sum := by decide
  have hdescent : baseEnd_7749028 < baseStart_7749028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749031 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_7749031 : Nat := 118140960795 + 7749031 * 2 ^ 59
def prefixEnd_7749031 : Nat := 4983230072969 + 3 ^ 40 * 7749031 * 2
def baseEnd_7749031 : Nat := 3978977509590576614275361

theorem tailTrace_7749031 : CollatzResearch.WordTrace tailWord_7749031 prefixEnd_7749031 3978977509590576614275361 := by
  unfold tailWord_7749031
  simp only [CollatzResearch.WordTrace]
  refine ⟨282630379589591590976334947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188420253059727727317556631 282630379589591590976334947)
  ·
    refine ⟨423945569384387386464502421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282630379589591590976334947 423945569384387386464502421)
    ·
      refine ⟨19872448564893158740523551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 423945569384387386464502421 19872448564893158740523551)
      ·
        refine ⟨29808672847339738110785327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19872448564893158740523551 29808672847339738110785327)
        ·
          refine ⟨44713009271009607166177991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29808672847339738110785327 44713009271009607166177991)
          ·
            refine ⟨67069513906514410749266987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44713009271009607166177991 67069513906514410749266987)
            ·
              refine ⟨100604270859771616123900481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67069513906514410749266987 100604270859771616123900481)
              ·
                refine ⟨75453203144828712092925361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100604270859771616123900481 75453203144828712092925361)
                ·
                  refine ⟨56589902358621534069694021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75453203144828712092925361 56589902358621534069694021)
                  ·
                    refine ⟨10610606692241537638067629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56589902358621534069694021 10610606692241537638067629)
                    ·
                      refine ⟨3978977509590576614275361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10610606692241537638067629 3978977509590576614275361)
                      ·
                        rfl

theorem cell23_7749031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_7749031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749031 prefixEnd_7749031 := by exact prefixLift 7749031
  have htrace : WordTrace (prefixWord ++ tailWord_7749031) baseStart_7749031 baseEnd_7749031 := by
    simpa [prefixWord, tailWord_7749031, baseEnd_7749031] using wordTrace_append hprefix tailTrace_7749031
  have hstable : (prefixWord ++ tailWord_7749031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749031).length < 2 ^ (prefixWord ++ tailWord_7749031).sum := by decide
  have hdescent : baseEnd_7749031 < baseStart_7749031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749049 : List Nat := [1, 2, 1, 4, 5, 1, 2, 1, 1, 3, 2]
def baseStart_7749049 : Nat := 118140960795 + 7749049 * 2 ^ 59
def prefixEnd_7749049 : Nat := 4983230072969 + 3 ^ 40 * 7749049 * 2
def baseEnd_7749049 : Nat := 3978986752242357543850279

theorem tailTrace_7749049 : CollatzResearch.WordTrace tailWord_7749049 prefixEnd_7749049 3978986752242357543850279 := by
  unfold tailWord_7749049
  simp only [CollatzResearch.WordTrace]
  refine ⟨282631036103526380050490201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188420690735684253366993467 282631036103526380050490201)
  ·
    refine ⟨211973277077644785037867651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282631036103526380050490201 211973277077644785037867651)
    ·
      refine ⟨317959915616467177556801477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211973277077644785037867651 317959915616467177556801477)
      ·
        refine ⟨59617484178087595791900277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317959915616467177556801477 59617484178087595791900277)
        ·
          refine ⟨5589139141695712105490651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59617484178087595791900277 5589139141695712105490651)
          ·
            refine ⟨8383708712543568158235977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5589139141695712105490651 8383708712543568158235977)
            ·
              refine ⟨6287781534407676118676983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8383708712543568158235977 6287781534407676118676983)
              ·
                refine ⟨9431672301611514178015475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6287781534407676118676983 9431672301611514178015475)
                ·
                  refine ⟨14147508452417271267023213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9431672301611514178015475 14147508452417271267023213)
                  ·
                    refine ⟨5305315669656476725133705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14147508452417271267023213 5305315669656476725133705)
                    ·
                      refine ⟨3978986752242357543850279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5305315669656476725133705 3978986752242357543850279)
                      ·
                        rfl

theorem cell23_7749049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_7749049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749049 prefixEnd_7749049 := by exact prefixLift 7749049
  have htrace : WordTrace (prefixWord ++ tailWord_7749049) baseStart_7749049 baseEnd_7749049 := by
    simpa [prefixWord, tailWord_7749049, baseEnd_7749049] using wordTrace_append hprefix tailTrace_7749049
  have hstable : (prefixWord ++ tailWord_7749049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749049).length < 2 ^ (prefixWord ++ tailWord_7749049).sum := by decide
  have hdescent : baseEnd_7749049 < baseStart_7749049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749068 : List Nat := [2, 2, 1, 4, 2, 1, 2, 4, 5]
def baseStart_7749068 : Nat := 118140960795 + 7749068 * 2 ^ 59
def prefixEnd_7749068 : Nat := 4983230072969 + 3 ^ 40 * 7749068 * 2
def baseEnd_7749068 : Nat := 442110723152754774390299

theorem tailTrace_7749068 : CollatzResearch.WordTrace tailWord_7749068 prefixEnd_7749068 442110723152754774390299 := by
  unfold tailWord_7749068
  simp only [CollatzResearch.WordTrace]
  refine ⟨141315864545228773147715929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188421152726971697530287905 141315864545228773147715929)
  ·
    refine ⟨105986898408921579860786947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141315864545228773147715929 105986898408921579860786947)
    ·
      refine ⟨158980347613382369791180421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105986898408921579860786947 158980347613382369791180421)
      ·
        refine ⟨29808815177509194335846329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158980347613382369791180421 29808815177509194335846329)
        ·
          refine ⟨22356611383131895751884747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29808815177509194335846329 22356611383131895751884747)
          ·
            refine ⟨33534917074697843627827121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22356611383131895751884747 33534917074697843627827121)
            ·
              refine ⟨25151187806023382720870341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33534917074697843627827121 25151187806023382720870341)
              ·
                refine ⟨4715847713629384260163189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25151187806023382720870341 4715847713629384260163189)
                ·
                  refine ⟨442110723152754774390299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4715847713629384260163189 442110723152754774390299)
                  ·
                    rfl

theorem cell23_7749068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 5].length) (baseStart_7749068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749068 prefixEnd_7749068 := by exact prefixLift 7749068
  have htrace : WordTrace (prefixWord ++ tailWord_7749068) baseStart_7749068 baseEnd_7749068 := by
    simpa [prefixWord, tailWord_7749068, baseEnd_7749068] using wordTrace_append hprefix tailTrace_7749068
  have hstable : (prefixWord ++ tailWord_7749068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749068).length < 2 ^ (prefixWord ++ tailWord_7749068).sum := by decide
  have hdescent : baseEnd_7749068 < baseStart_7749068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749071 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 1, 7, 2]
def baseStart_7749071 : Nat := 118140960795 + 7749071 * 2 ^ 59
def prefixEnd_7749071 : Nat := 4983230072969 + 3 ^ 40 * 7749071 * 2
def baseEnd_7749071 : Nat := 3978998048816756457775177

theorem tailTrace_7749071 : CollatzResearch.WordTrace tailWord_7749071 prefixEnd_7749071 3978998048816756457775177 := by
  unfold tailWord_7749071
  simp only [CollatzResearch.WordTrace]
  refine ⟨282631838509446677807791067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188421225672964451871860711 282631838509446677807791067)
  ·
    refine ⟨423947757764170016711686601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282631838509446677807791067 423947757764170016711686601)
    ·
      refine ⟨317960818323127512533764951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423947757764170016711686601 317960818323127512533764951)
      ·
        refine ⟨476941227484691268800647427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317960818323127512533764951 476941227484691268800647427)
        ·
          refine ⟨715411841227036903200971141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476941227484691268800647427 715411841227036903200971141)
          ·
            refine ⟨134139720230069419350182089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 715411841227036903200971141 134139720230069419350182089)
            ·
              refine ⟨100604790172552064512636567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134139720230069419350182089 100604790172552064512636567)
              ·
                refine ⟨150907185258828096768954851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100604790172552064512636567 150907185258828096768954851)
                ·
                  refine ⟨226360777888242145153432277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150907185258828096768954851 226360777888242145153432277)
                  ·
                    refine ⟨5305330731755675277033569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 226360777888242145153432277 5305330731755675277033569)
                    ·
                      refine ⟨3978998048816756457775177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5305330731755675277033569 3978998048816756457775177)
                      ·
                        rfl

theorem cell23_7749071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 7, 2].length) (baseStart_7749071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749071 prefixEnd_7749071 := by exact prefixLift 7749071
  have htrace : WordTrace (prefixWord ++ tailWord_7749071) baseStart_7749071 baseEnd_7749071 := by
    simpa [prefixWord, tailWord_7749071, baseEnd_7749071] using wordTrace_append hprefix tailTrace_7749071
  have hstable : (prefixWord ++ tailWord_7749071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749071).length < 2 ^ (prefixWord ++ tailWord_7749071).sum := by decide
  have hdescent : baseEnd_7749071 < baseStart_7749071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749128 : List Nat := [2, 1, 3, 2, 1, 1, 5, 1, 3, 4]
def baseStart_7749128 : Nat := 118140960795 + 7749128 * 2 ^ 59
def prefixEnd_7749128 : Nat := 4983230072969 + 3 ^ 40 * 7749128 * 2
def baseEnd_7749128 : Nat := 1326342439071354244920805

theorem tailTrace_7749128 : CollatzResearch.WordTrace tailWord_7749128 prefixEnd_7749128 1326342439071354244920805 := by
  unfold tailWord_7749128
  simp only [CollatzResearch.WordTrace]
  refine ⟨141316958735120088271308019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188422611646826784361744025 141316958735120088271308019)
  ·
    refine ⟨211975438102680132406962029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141316958735120088271308019 211975438102680132406962029)
    ·
      refine ⟨79490789288505049652610761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211975438102680132406962029 79490789288505049652610761)
      ·
        refine ⟨59618091966378787239458071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79490789288505049652610761 59618091966378787239458071)
        ·
          refine ⟨89427137949568180859187107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59618091966378787239458071 89427137949568180859187107)
          ·
            refine ⟨134140706924352271288780661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89427137949568180859187107 134140706924352271288780661)
            ·
              refine ⟨12575691274158025433323187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134140706924352271288780661 12575691274158025433323187)
              ·
                refine ⟨18863536911237038149984781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12575691274158025433323187 18863536911237038149984781)
                ·
                  refine ⟨7073826341713889306244293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18863536911237038149984781 7073826341713889306244293)
                  ·
                    refine ⟨1326342439071354244920805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7073826341713889306244293 1326342439071354244920805)
                    ·
                      rfl

theorem cell23_7749128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_7749128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749128 prefixEnd_7749128 := by exact prefixLift 7749128
  have htrace : WordTrace (prefixWord ++ tailWord_7749128) baseStart_7749128 baseEnd_7749128 := by
    simpa [prefixWord, tailWord_7749128, baseEnd_7749128] using wordTrace_append hprefix tailTrace_7749128
  have hstable : (prefixWord ++ tailWord_7749128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749128).length < 2 ^ (prefixWord ++ tailWord_7749128).sum := by decide
  have hdescent : baseEnd_7749128 < baseStart_7749128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749151 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 3]
def baseStart_7749151 : Nat := 118140960795 + 7749151 * 2 ^ 59
def prefixEnd_7749151 : Nat := 4983230072969 + 3 ^ 40 * 7749151 * 2
def baseEnd_7749151 : Nat := 3979039127269116144774809

theorem tailTrace_7749151 : CollatzResearch.WordTrace tailWord_7749151 prefixEnd_7749151 3979039127269116144774809 := by
  unfold tailWord_7749151
  simp only [CollatzResearch.WordTrace]
  refine ⟨282634756349156851470703307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188423170899437900980468871 282634756349156851470703307)
  ·
    refine ⟨423952134523735277206054961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282634756349156851470703307 423952134523735277206054961)
    ·
      refine ⟨317964100892801457904541221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423952134523735277206054961 317964100892801457904541221)
      ·
        refine ⟨59618268917400273357101479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317964100892801457904541221 59618268917400273357101479)
        ·
          refine ⟨89427403376100410035652219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59618268917400273357101479 89427403376100410035652219)
          ·
            refine ⟨134141105064150615053478329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89427403376100410035652219 134141105064150615053478329)
            ·
              refine ⟨100605828798112961290108747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134141105064150615053478329 100605828798112961290108747)
              ·
                refine ⟨150908743197169441935163121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100605828798112961290108747 150908743197169441935163121)
                ·
                  refine ⟨113181557397877081451372341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150908743197169441935163121 113181557397877081451372341)
                  ·
                    refine ⟨10610771006050976386066157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113181557397877081451372341 10610771006050976386066157)
                    ·
                      refine ⟨3979039127269116144774809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10610771006050976386066157 3979039127269116144774809)
                      ·
                        rfl

theorem cell23_7749151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_7749151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749151 prefixEnd_7749151 := by exact prefixLift 7749151
  have htrace : WordTrace (prefixWord ++ tailWord_7749151) baseStart_7749151 baseEnd_7749151 := by
    simpa [prefixWord, tailWord_7749151, baseEnd_7749151] using wordTrace_append hprefix tailTrace_7749151
  have hstable : (prefixWord ++ tailWord_7749151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749151).length < 2 ^ (prefixWord ++ tailWord_7749151).sum := by decide
  have hdescent : baseEnd_7749151 < baseStart_7749151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749155 : List Nat := [1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 3]
def baseStart_7749155 : Nat := 118140960795 + 7749155 * 2 ^ 59
def prefixEnd_7749155 : Nat := 4983230072969 + 3 ^ 40 * 7749155 * 2
def baseEnd_7749155 : Nat := 3979041181191734129124791

theorem tailTrace_7749155 : CollatzResearch.WordTrace tailWord_7749155 prefixEnd_7749155 3979041181191734129124791 := by
  unfold tailWord_7749155
  simp only [CollatzResearch.WordTrace]
  refine ⟨282634902241142360153848919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188423268160761573435899279 282634902241142360153848919)
  ·
    refine ⟨423952353361713540230773379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282634902241142360153848919 423952353361713540230773379)
    ·
      refine ⟨635928530042570310346160069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423952353361713540230773379 635928530042570310346160069)
      ·
        refine ⟨119236599382981933189905013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 635928530042570310346160069 119236599382981933189905013)
        ·
          refine ⟨11178431192154556236553595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119236599382981933189905013 11178431192154556236553595)
          ·
            refine ⟨16767646788231834354830393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11178431192154556236553595 16767646788231834354830393)
            ·
              refine ⟨12575735091173875766122795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16767646788231834354830393 12575735091173875766122795)
              ·
                refine ⟨18863602636760813649184193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12575735091173875766122795 18863602636760813649184193)
                ·
                  refine ⟨14147701977570610236888145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18863602636760813649184193 14147701977570610236888145)
                  ·
                    refine ⟨10610776483177957677666109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14147701977570610236888145 10610776483177957677666109)
                    ·
                      refine ⟨3979041181191734129124791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10610776483177957677666109 3979041181191734129124791)
                      ·
                        rfl

theorem cell23_7749155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_7749155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749155 prefixEnd_7749155 := by exact prefixLift 7749155
  have htrace : WordTrace (prefixWord ++ tailWord_7749155) baseStart_7749155 baseEnd_7749155 := by
    simpa [prefixWord, tailWord_7749155, baseEnd_7749155] using wordTrace_append hprefix tailTrace_7749155
  have hstable : (prefixWord ++ tailWord_7749155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749155).length < 2 ^ (prefixWord ++ tailWord_7749155).sum := by decide
  have hdescent : baseEnd_7749155 < baseStart_7749155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749185 : List Nat := [1, 2, 5, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_7749185 : Nat := 118140960795 + 7749185 * 2 ^ 59
def prefixEnd_7749185 : Nat := 4983230072969 + 3 ^ 40 * 7749185 * 2
def baseEnd_7749185 : Nat := 3979056585611369011749653

theorem tailTrace_7749185 : CollatzResearch.WordTrace tailWord_7749185 prefixEnd_7749185 3979056585611369011749653 := by
  unfold tailWord_7749185
  simp only [CollatzResearch.WordTrace]
  refine ⟨282635996431033675277441009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188423997620689116851627339 282635996431033675277441009)
  ·
    refine ⟨211976997323275256458080757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282635996431033675277441009 211976997323275256458080757)
    ·
      refine ⟨19872843499057055292945071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211976997323275256458080757 19872843499057055292945071)
      ·
        refine ⟨29809265248585582939417607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19872843499057055292945071 29809265248585582939417607)
        ·
          refine ⟨44713897872878374409126411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29809265248585582939417607 44713897872878374409126411)
          ·
            refine ⟨67070846809317561613689617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44713897872878374409126411 67070846809317561613689617)
            ·
              refine ⟨50303135106988171210267213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67070846809317561613689617 50303135106988171210267213)
              ·
                refine ⟨18863675665120564203850205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50303135106988171210267213 18863675665120564203850205)
                ·
                  refine ⟨7073878374420211576443827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18863675665120564203850205 7073878374420211576443827)
                  ·
                    refine ⟨10610817561630317364665741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7073878374420211576443827 10610817561630317364665741)
                    ·
                      refine ⟨3979056585611369011749653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10610817561630317364665741 3979056585611369011749653)
                      ·
                        rfl

theorem cell23_7749185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_7749185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749185 prefixEnd_7749185 := by exact prefixLift 7749185
  have htrace : WordTrace (prefixWord ++ tailWord_7749185) baseStart_7749185 baseEnd_7749185 := by
    simpa [prefixWord, tailWord_7749185, baseEnd_7749185] using wordTrace_append hprefix tailTrace_7749185
  have hstable : (prefixWord ++ tailWord_7749185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749185).length < 2 ^ (prefixWord ++ tailWord_7749185).sum := by decide
  have hdescent : baseEnd_7749185 < baseStart_7749185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749206 : List Nat := [5, 2, 2, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_7749206 : Nat := 118140960795 + 7749206 * 2 ^ 59
def prefixEnd_7749206 : Nat := 4983230072969 + 3 ^ 40 * 7749206 * 2
def baseEnd_7749206 : Nat := 3979067368705113429587057

theorem tailTrace_7749206 : CollatzResearch.WordTrace tailWord_7749206 prefixEnd_7749206 3979067368705113429587057 := by
  unfold tailWord_7749206
  simp only [CollatzResearch.WordTrace]
  refine ⟨17664797647747349741497217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188424508242638397242636981 17664797647747349741497217)
  ·
    refine ⟨13248598235810512306122913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17664797647747349741497217 13248598235810512306122913)
    ·
      refine ⟨9936448676857884229592185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13248598235810512306122913 9936448676857884229592185)
      ·
        refine ⟨7452336507643413172194139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9936448676857884229592185 7452336507643413172194139)
        ·
          refine ⟨11178504761465119758291209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7452336507643413172194139 11178504761465119758291209)
          ·
            refine ⟨8383878571098839818718407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11178504761465119758291209 8383878571098839818718407)
            ·
              refine ⟨12575817856648259728077611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8383878571098839818718407 12575817856648259728077611)
              ·
                refine ⟨18863726784972389592116417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12575817856648259728077611 18863726784972389592116417)
                ·
                  refine ⟨14147795088729292194087313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18863726784972389592116417 14147795088729292194087313)
                  ·
                    refine ⟨10610846316546969145565485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14147795088729292194087313 10610846316546969145565485)
                    ·
                      refine ⟨3979067368705113429587057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10610846316546969145565485 3979067368705113429587057)
                      ·
                        rfl

theorem cell23_7749206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_7749206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749206 prefixEnd_7749206 := by exact prefixLift 7749206
  have htrace : WordTrace (prefixWord ++ tailWord_7749206) baseStart_7749206 baseEnd_7749206 := by
    simpa [prefixWord, tailWord_7749206, baseEnd_7749206] using wordTrace_append hprefix tailTrace_7749206
  have hstable : (prefixWord ++ tailWord_7749206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749206).length < 2 ^ (prefixWord ++ tailWord_7749206).sum := by decide
  have hdescent : baseEnd_7749206 < baseStart_7749206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749208 : List Nat := [2, 1, 2, 2, 1, 2, 1, 6, 1, 1, 4]
def baseStart_7749208 : Nat := 118140960795 + 7749208 * 2 ^ 59
def prefixEnd_7749208 : Nat := 4983230072969 + 3 ^ 40 * 7749208 * 2
def baseEnd_7749208 : Nat := 3979068395666422421762047

theorem tailTrace_7749208 : CollatzResearch.WordTrace tailWord_7749208 prefixEnd_7749208 3979068395666422421762047 := by
  unfold tailWord_7749208
  simp only [CollatzResearch.WordTrace]
  refine ⟨141318417654975175102764139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188424556873300233470352185 141318417654975175102764139)
  ·
    refine ⟨211977626482462762654146209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141318417654975175102764139 211977626482462762654146209)
    ·
      refine ⟨158983219861847071990609657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211977626482462762654146209 158983219861847071990609657)
      ·
        refine ⟨119237414896385303992957243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158983219861847071990609657 119237414896385303992957243)
        ·
          refine ⟨178856122344577955989435865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119237414896385303992957243 178856122344577955989435865)
          ·
            refine ⟨134142091758433466992076899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178856122344577955989435865 134142091758433466992076899)
            ·
              refine ⟨201213137637650200488115349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134142091758433466992076899 201213137637650200488115349)
              ·
                refine ⟨9431865826764853147880407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 201213137637650200488115349 9431865826764853147880407)
                ·
                  refine ⟨14147798740147279721820611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9431865826764853147880407 14147798740147279721820611)
                  ·
                    refine ⟨21221698110220919582730917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14147798740147279721820611 21221698110220919582730917)
                    ·
                      refine ⟨3979068395666422421762047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21221698110220919582730917 3979068395666422421762047)
                      ·
                        rfl

theorem cell23_7749208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_7749208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749208 prefixEnd_7749208 := by exact prefixLift 7749208
  have htrace : WordTrace (prefixWord ++ tailWord_7749208) baseStart_7749208 baseEnd_7749208 := by
    simpa [prefixWord, tailWord_7749208, baseEnd_7749208] using wordTrace_append hprefix tailTrace_7749208
  have hstable : (prefixWord ++ tailWord_7749208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749208).length < 2 ^ (prefixWord ++ tailWord_7749208).sum := by decide
  have hdescent : baseEnd_7749208 < baseStart_7749208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749212 : List Nat := [2, 2, 4, 1, 2, 1, 3, 1, 2, 3, 2]
def baseStart_7749212 : Nat := 118140960795 + 7749212 * 2 ^ 59
def prefixEnd_7749212 : Nat := 4983230072969 + 3 ^ 40 * 7749212 * 2
def baseEnd_7749212 : Nat := 3979070449589040406112029

theorem tailTrace_7749212 : CollatzResearch.WordTrace tailWord_7749212 prefixEnd_7749212 3979070449589040406112029 := by
  unfold tailWord_7749212
  simp only [CollatzResearch.WordTrace]
  refine ⟨141318490600967929444336945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188424654134623905925782593 141318490600967929444336945)
  ·
    refine ⟨105988867950725947083252709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141318490600967929444336945 105988867950725947083252709)
    ·
      refine ⟨19872912740761115078109883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105988867950725947083252709 19872912740761115078109883)
      ·
        refine ⟨29809369111141672617164825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19872912740761115078109883 29809369111141672617164825)
        ·
          refine ⟨22357026833356254462873619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29809369111141672617164825 22357026833356254462873619)
          ·
            refine ⟨33535540250034381694310429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22357026833356254462873619 33535540250034381694310429)
            ·
              refine ⟨12575827593762893135366411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33535540250034381694310429 12575827593762893135366411)
              ·
                refine ⟨18863741390644339703049617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12575827593762893135366411 18863741390644339703049617)
                ·
                  refine ⟨14147806042983254777287213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18863741390644339703049617 14147806042983254777287213)
                  ·
                    refine ⟨5305427266118720541482705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14147806042983254777287213 5305427266118720541482705)
                    ·
                      refine ⟨3979070449589040406112029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5305427266118720541482705 3979070449589040406112029)
                      ·
                        rfl

theorem cell23_7749212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_7749212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749212 prefixEnd_7749212 := by exact prefixLift 7749212
  have htrace : WordTrace (prefixWord ++ tailWord_7749212) baseStart_7749212 baseEnd_7749212 := by
    simpa [prefixWord, tailWord_7749212, baseEnd_7749212] using wordTrace_append hprefix tailTrace_7749212
  have hstable : (prefixWord ++ tailWord_7749212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749212).length < 2 ^ (prefixWord ++ tailWord_7749212).sum := by decide
  have hdescent : baseEnd_7749212 < baseStart_7749212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749225 : List Nat := [1, 2, 1, 1, 1, 4, 6, 1, 1, 1, 4]
def baseStart_7749225 : Nat := 118140960795 + 7749225 * 2 ^ 59
def prefixEnd_7749225 : Nat := 4983230072969 + 3 ^ 40 * 7749225 * 2
def baseEnd_7749225 : Nat := 3979077124837548855249469

theorem tailTrace_7749225 : CollatzResearch.WordTrace tailWord_7749225 prefixEnd_7749225 3979077124837548855249469 := by
  unfold tailWord_7749225
  simp only [CollatzResearch.WordTrace]
  refine ⟨282637455350888762108897129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188424970233925841405931419 282637455350888762108897129)
  ·
    refine ⟨211978091513166571581672847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282637455350888762108897129 211978091513166571581672847)
    ·
      refine ⟨317967137269749857372509271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211978091513166571581672847 317967137269749857372509271)
      ·
        refine ⟨476950705904624786058763907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317967137269749857372509271 476950705904624786058763907)
        ·
          refine ⟨715426058856937179088145861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476950705904624786058763907 715426058856937179088145861)
          ·
            refine ⟨134142386035675721079027349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 715426058856937179088145861 134142386035675721079027349)
            ·
              refine ⟨6287924345422299425579407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134142386035675721079027349 6287924345422299425579407)
              ·
                refine ⟨9431886518133449138369111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6287924345422299425579407 9431886518133449138369111)
                ·
                  refine ⟨14147829777200173707553667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9431886518133449138369111 14147829777200173707553667)
                  ·
                    refine ⟨21221744665800260561330501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14147829777200173707553667 21221744665800260561330501)
                    ·
                      refine ⟨3979077124837548855249469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21221744665800260561330501 3979077124837548855249469)
                      ·
                        rfl

theorem cell23_7749225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 1, 1, 4].length) (baseStart_7749225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749225 prefixEnd_7749225 := by exact prefixLift 7749225
  have htrace : WordTrace (prefixWord ++ tailWord_7749225) baseStart_7749225 baseEnd_7749225 := by
    simpa [prefixWord, tailWord_7749225, baseEnd_7749225] using wordTrace_append hprefix tailTrace_7749225
  have hstable : (prefixWord ++ tailWord_7749225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749225).length < 2 ^ (prefixWord ++ tailWord_7749225).sum := by decide
  have hdescent : baseEnd_7749225 < baseStart_7749225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749252 : List Nat := [2, 3, 2, 1, 5, 1, 1, 1, 1, 6]
def baseStart_7749252 : Nat := 118140960795 + 7749252 * 2 ^ 59
def prefixEnd_7749252 : Nat := 4983230072969 + 3 ^ 40 * 7749252 * 2
def baseEnd_7749252 : Nat := 1326363662938406749870615

theorem tailTrace_7749252 : CollatzResearch.WordTrace tailWord_7749252 prefixEnd_7749252 1326363662938406749870615 := by
  unfold tailWord_7749252
  simp only [CollatzResearch.WordTrace]
  refine ⟨141319220060895472860065005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188425626747860630480086673 141319220060895472860065005)
  ·
    refine ⟨52994707522835802322524377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141319220060895472860065005 52994707522835802322524377)
    ·
      refine ⟨39746030642126851741893283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52994707522835802322524377 39746030642126851741893283)
      ·
        refine ⟨59619045963190277612839925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39746030642126851741893283 59619045963190277612839925)
        ·
          refine ⟨5589285559049088526203743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59619045963190277612839925 5589285559049088526203743)
          ·
            refine ⟨8383928338573632789305615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5589285559049088526203743 8383928338573632789305615)
            ·
              refine ⟨12575892507860449183958423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8383928338573632789305615 12575892507860449183958423)
              ·
                refine ⟨18863838761790673775937635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12575892507860449183958423 18863838761790673775937635)
                ·
                  refine ⟨28295758142686010663906453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18863838761790673775937635 28295758142686010663906453)
                  ·
                    refine ⟨1326363662938406749870615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28295758142686010663906453 1326363662938406749870615)
                    ·
                      rfl

theorem cell23_7749252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_7749252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749252 prefixEnd_7749252 := by exact prefixLift 7749252
  have htrace : WordTrace (prefixWord ++ tailWord_7749252) baseStart_7749252 baseEnd_7749252 := by
    simpa [prefixWord, tailWord_7749252, baseEnd_7749252] using wordTrace_append hprefix tailTrace_7749252
  have hstable : (prefixWord ++ tailWord_7749252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749252).length < 2 ^ (prefixWord ++ tailWord_7749252).sum := by decide
  have hdescent : baseEnd_7749252 < baseStart_7749252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749255 : List Nat := [1, 1, 4, 2, 1, 5, 1, 1, 1, 2, 4]
def baseStart_7749255 : Nat := 118140960795 + 7749255 * 2 ^ 59
def prefixEnd_7749255 : Nat := 4983230072969 + 3 ^ 40 * 7749255 * 2
def baseEnd_7749255 : Nat := 3979092529257183737874331

theorem tailTrace_7749255 : CollatzResearch.WordTrace tailWord_7749255 prefixEnd_7749255 3979092529257183737874331 := by
  unfold tailWord_7749255
  simp only [CollatzResearch.WordTrace]
  refine ⟨282638549540780077232489219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188425699693853384821659479 282638549540780077232489219)
  ·
    refine ⟨423957824311170115848733829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282638549540780077232489219 423957824311170115848733829)
    ·
      refine ⟨79492092058344396721637593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 423957824311170115848733829 79492092058344396721637593)
      ·
        refine ⟨59619069043758297541228195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79492092058344396721637593 59619069043758297541228195)
        ·
          refine ⟨89428603565637446311842293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59619069043758297541228195 89428603565637446311842293)
          ·
            refine ⟨8383931584278510591735215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89428603565637446311842293 8383931584278510591735215)
            ·
              refine ⟨12575897376417765887602823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8383931584278510591735215 12575897376417765887602823)
              ·
                refine ⟨18863846064626648831404235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12575897376417765887602823 18863846064626648831404235)
                ·
                  refine ⟨28295769096939973247106353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18863846064626648831404235 28295769096939973247106353)
                  ·
                    refine ⟨21221826822704979935329765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28295769096939973247106353 21221826822704979935329765)
                    ·
                      refine ⟨3979092529257183737874331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21221826822704979935329765 3979092529257183737874331)
                      ·
                        rfl

theorem cell23_7749255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_7749255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749255 prefixEnd_7749255 := by exact prefixLift 7749255
  have htrace : WordTrace (prefixWord ++ tailWord_7749255) baseStart_7749255 baseEnd_7749255 := by
    simpa [prefixWord, tailWord_7749255, baseEnd_7749255] using wordTrace_append hprefix tailTrace_7749255
  have hstable : (prefixWord ++ tailWord_7749255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749255).length < 2 ^ (prefixWord ++ tailWord_7749255).sum := by decide
  have hdescent : baseEnd_7749255 < baseStart_7749255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749262 : List Nat := [4, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3]
def baseStart_7749262 : Nat := 118140960795 + 7749262 * 2 ^ 59
def prefixEnd_7749262 : Nat := 4983230072969 + 3 ^ 40 * 7749262 * 2
def baseEnd_7749262 : Nat := 3979096123621765210486799

theorem tailTrace_7749262 : CollatzResearch.WordTrace tailWord_7749262 prefixEnd_7749262 3979096123621765210486799 := by
  unfold tailWord_7749262
  simp only [CollatzResearch.WordTrace]
  refine ⟨35329850606469339678499255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188425869901169811618662693 35329850606469339678499255)
  ·
    refine ⟨52994775909704009517748883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35329850606469339678499255 52994775909704009517748883)
    ·
      refine ⟨79492163864556014276623325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52994775909704009517748883 79492163864556014276623325)
      ·
        refine ⟨29809561449208505353733747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79492163864556014276623325 29809561449208505353733747)
        ·
          refine ⟨44714342173812758030600621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29809561449208505353733747 44714342173812758030600621)
          ·
            refine ⟨16767878315179784261475233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44714342173812758030600621 16767878315179784261475233)
            ·
              refine ⟨12575908736384838196106425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16767878315179784261475233 12575908736384838196106425)
              ·
                refine ⟨9431931552288628647079819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12575908736384838196106425 9431931552288628647079819)
                ·
                  refine ⟨14147897328432942970619729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9431931552288628647079819 14147897328432942970619729)
                  ·
                    refine ⟨10610922996324707227964797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14147897328432942970619729 10610922996324707227964797)
                    ·
                      refine ⟨3979096123621765210486799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10610922996324707227964797 3979096123621765210486799)
                      ·
                        rfl

theorem cell23_7749262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_7749262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749262 prefixEnd_7749262 := by exact prefixLift 7749262
  have htrace : WordTrace (prefixWord ++ tailWord_7749262) baseStart_7749262 baseEnd_7749262 := by
    simpa [prefixWord, tailWord_7749262, baseEnd_7749262] using wordTrace_append hprefix tailTrace_7749262
  have hstable : (prefixWord ++ tailWord_7749262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749262).length < 2 ^ (prefixWord ++ tailWord_7749262).sum := by decide
  have hdescent : baseEnd_7749262 < baseStart_7749262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749282 : List Nat := [3, 3, 1, 4, 2, 1, 9]
def baseStart_7749282 : Nat := 118140960795 + 7749282 * 2 ^ 59
def prefixEnd_7749282 : Nat := 4983230072969 + 3 ^ 40 * 7749282 * 2
def baseEnd_7749282 : Nat := 49124770286850063360947

theorem tailTrace_7749282 : CollatzResearch.WordTrace tailWord_7749282 prefixEnd_7749282 49124770286850063360947 := by
  unfold tailWord_7749282
  simp only [CollatzResearch.WordTrace]
  refine ⟨70659883577920565210930525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188426356207788173895814733 70659883577920565210930525)
  ·
    refine ⟨26497456341720211954098947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70659883577920565210930525 26497456341720211954098947)
    ·
      refine ⟨39746184512580317931148421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26497456341720211954098947 39746184512580317931148421)
      ·
        refine ⟨7452409596108809612090329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39746184512580317931148421 7452409596108809612090329)
        ·
          refine ⟨5589307197081607209067747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7452409596108809612090329 5589307197081607209067747)
          ·
            refine ⟨8383960795622410813601621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5589307197081607209067747 8383960795622410813601621)
            ·
              refine ⟨49124770286850063360947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8383960795622410813601621 49124770286850063360947)
              ·
                rfl

theorem cell23_7749282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 9].length) (baseStart_7749282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749282 prefixEnd_7749282 := by exact prefixLift 7749282
  have htrace : WordTrace (prefixWord ++ tailWord_7749282) baseStart_7749282 baseEnd_7749282 := by
    simpa [prefixWord, tailWord_7749282, baseEnd_7749282] using wordTrace_append hprefix tailTrace_7749282
  have hstable : (prefixWord ++ tailWord_7749282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749282).length < 2 ^ (prefixWord ++ tailWord_7749282).sum := by decide
  have hdescent : baseEnd_7749282 < baseStart_7749282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749331 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 9]
def baseStart_7749331 : Nat := 118140960795 + 7749331 * 2 ^ 59
def prefixEnd_7749331 : Nat := 4983230072969 + 3 ^ 40 * 7749331 * 2
def baseEnd_7749331 : Nat := 3979131553786925440523981

theorem tailTrace_7749331 : CollatzResearch.WordTrace tailWord_7749331 prefixEnd_7749331 3979131553786925440523981 := by
  unfold tailWord_7749331
  simp only [CollatzResearch.WordTrace]
  refine ⟨282641321488504742212255847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188427547659003161474837231 282641321488504742212255847)
  ·
    refine ⟨423961982232757113318383771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282641321488504742212255847 423961982232757113318383771)
    ·
      refine ⟨635942973349135669977575657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423961982232757113318383771 635942973349135669977575657)
      ·
        refine ⟨476957230011851752483181743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635942973349135669977575657 476957230011851752483181743)
        ·
          refine ⟨715435845017777628724772615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476957230011851752483181743 715435845017777628724772615)
          ·
            refine ⟨1073153767526666443087158923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715435845017777628724772615 1073153767526666443087158923)
            ·
              refine ⟨1609730651289999664630738385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1073153767526666443087158923 1609730651289999664630738385)
              ·
                refine ⟨1207297988467499748473053789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1609730651289999664630738385 1207297988467499748473053789)
                ·
                  refine ⟨452736745675312405677395171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1207297988467499748473053789 452736745675312405677395171)
                  ·
                    refine ⟨679105118512968608516092757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 452736745675312405677395171 679105118512968608516092757)
                    ·
                      refine ⟨3979131553786925440523981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 679105118512968608516092757 3979131553786925440523981)
                      ·
                        rfl

theorem cell23_7749331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_7749331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749331 prefixEnd_7749331 := by exact prefixLift 7749331
  have htrace : WordTrace (prefixWord ++ tailWord_7749331) baseStart_7749331 baseEnd_7749331 := by
    simpa [prefixWord, tailWord_7749331, baseEnd_7749331] using wordTrace_append hprefix tailTrace_7749331
  have hstable : (prefixWord ++ tailWord_7749331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749331).length < 2 ^ (prefixWord ++ tailWord_7749331).sum := by decide
  have hdescent : baseEnd_7749331 < baseStart_7749331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749332 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 3, 4, 2]
def baseStart_7749332 : Nat := 118140960795 + 7749332 * 2 ^ 59
def prefixEnd_7749332 : Nat := 4983230072969 + 3 ^ 40 * 7749332 * 2
def baseEnd_7749332 : Nat := 3979132067267579936611477

theorem tailTrace_7749332 : CollatzResearch.WordTrace tailWord_7749332 prefixEnd_7749332 3979132067267579936611477 := by
  unfold tailWord_7749332
  simp only [CollatzResearch.WordTrace]
  refine ⟨141320678980750559691521125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188427571974334079588694833 141320678980750559691521125)
  ·
    refine ⟨26497627308890729942160211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141320678980750559691521125 26497627308890729942160211)
    ·
      refine ⟨39746440963336094913240317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26497627308890729942160211 39746440963336094913240317)
      ·
        refine ⟨14904915361251035592465119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39746440963336094913240317 14904915361251035592465119)
        ·
          refine ⟨22357373041876553388697679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14904915361251035592465119 22357373041876553388697679)
          ·
            refine ⟨33536059562814830083046519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22357373041876553388697679 33536059562814830083046519)
            ·
              refine ⟨50304089344222245124569779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33536059562814830083046519 50304089344222245124569779)
              ·
                refine ⟨75456134016333367686854669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50304089344222245124569779 75456134016333367686854669)
                ·
                  refine ⟨28296050256125012882570501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75456134016333367686854669 28296050256125012882570501)
                  ·
                    refine ⟨5305509423023439915481969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28296050256125012882570501 5305509423023439915481969)
                    ·
                      refine ⟨3979132067267579936611477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5305509423023439915481969 3979132067267579936611477)
                      ·
                        rfl

theorem cell23_7749332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_7749332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749332 prefixEnd_7749332 := by exact prefixLift 7749332
  have htrace : WordTrace (prefixWord ++ tailWord_7749332) baseStart_7749332 baseEnd_7749332 := by
    simpa [prefixWord, tailWord_7749332, baseEnd_7749332] using wordTrace_append hprefix tailTrace_7749332
  have hstable : (prefixWord ++ tailWord_7749332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749332).length < 2 ^ (prefixWord ++ tailWord_7749332).sum := by decide
  have hdescent : baseEnd_7749332 < baseStart_7749332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749349 : List Nat := [1, 3, 1, 4, 1, 1, 4, 2, 2, 2, 2]
def baseStart_7749349 : Nat := 118140960795 + 7749349 * 2 ^ 59
def prefixEnd_7749349 : Nat := 4983230072969 + 3 ^ 40 * 7749349 * 2
def baseEnd_7749349 : Nat := 3979140796438706370098899

theorem tailTrace_7749349 : CollatzResearch.WordTrace tailWord_7749349 prefixEnd_7749349 3979140796438706370098899 := by
  unfold tailWord_7749349
  simp only [CollatzResearch.WordTrace]
  refine ⟨282641978002439531286411101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188427985334959687524274067 282641978002439531286411101)
  ·
    refine ⟨105990741750914824232404163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282641978002439531286411101 105990741750914824232404163)
    ·
      refine ⟨158986112626372236348606245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105990741750914824232404163 158986112626372236348606245)
      ·
        refine ⟨29809896117444794315363671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158986112626372236348606245 29809896117444794315363671)
        ·
          refine ⟨44714844176167191473045507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29809896117444794315363671 44714844176167191473045507)
          ·
            refine ⟨67072266264250787209568261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44714844176167191473045507 67072266264250787209568261)
            ·
              refine ⟨12576049924547022601794049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67072266264250787209568261 12576049924547022601794049)
              ·
                refine ⟨9432037443410266951345537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12576049924547022601794049 9432037443410266951345537)
                ·
                  refine ⟨7074028082557700213509153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9432037443410266951345537 7074028082557700213509153)
                  ·
                    refine ⟨5305521061918275160131865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7074028082557700213509153 5305521061918275160131865)
                    ·
                      refine ⟨3979140796438706370098899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5305521061918275160131865 3979140796438706370098899)
                      ·
                        rfl

theorem cell23_7749349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_7749349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749349 prefixEnd_7749349 := by exact prefixLift 7749349
  have htrace : WordTrace (prefixWord ++ tailWord_7749349) baseStart_7749349 baseEnd_7749349 := by
    simpa [prefixWord, tailWord_7749349, baseEnd_7749349] using wordTrace_append hprefix tailTrace_7749349
  have hstable : (prefixWord ++ tailWord_7749349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749349).length < 2 ^ (prefixWord ++ tailWord_7749349).sum := by decide
  have hdescent : baseEnd_7749349 < baseStart_7749349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749425 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 1, 4, 3]
def baseStart_7749425 : Nat := 118140960795 + 7749425 * 2 ^ 59
def prefixEnd_7749425 : Nat := 4983230072969 + 3 ^ 40 * 7749425 * 2
def baseEnd_7749425 : Nat := 3979179820968448072748549

theorem tailTrace_7749425 : CollatzResearch.WordTrace tailWord_7749425 prefixEnd_7749425 3979179820968448072748549 := by
  unfold tailWord_7749425
  simp only [CollatzResearch.WordTrace]
  refine ⟨282644749950164196266177729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188429833300109464177451819 282644749950164196266177729)
  ·
    refine ⟨211983562462623147199633297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282644749950164196266177729 211983562462623147199633297)
    ·
      refine ⟨158987671846967360399724973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211983562462623147199633297 158987671846967360399724973)
      ·
        refine ⟨59620376942612760149896865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158987671846967360399724973 59620376942612760149896865)
        ·
          refine ⟨44715282706959570112422649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59620376942612760149896865 44715282706959570112422649)
          ·
            refine ⟨33536462030219677584316987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44715282706959570112422649 33536462030219677584316987)
            ·
              refine ⟨50304693045329516376475481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33536462030219677584316987 50304693045329516376475481)
              ·
                refine ⟨37728519783997137282356611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50304693045329516376475481 37728519783997137282356611)
                ·
                  refine ⟨56592779675995705923534917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37728519783997137282356611 56592779675995705923534917)
                  ·
                    refine ⟨10611146189249194860662797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56592779675995705923534917 10611146189249194860662797)
                    ·
                      refine ⟨3979179820968448072748549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10611146189249194860662797 3979179820968448072748549)
                      ·
                        rfl

theorem cell23_7749425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_7749425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749425 prefixEnd_7749425 := by exact prefixLift 7749425
  have htrace : WordTrace (prefixWord ++ tailWord_7749425) baseStart_7749425 baseEnd_7749425 := by
    simpa [prefixWord, tailWord_7749425, baseEnd_7749425] using wordTrace_append hprefix tailTrace_7749425
  have hstable : (prefixWord ++ tailWord_7749425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749425).length < 2 ^ (prefixWord ++ tailWord_7749425).sum := by decide
  have hdescent : baseEnd_7749425 < baseStart_7749425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749525 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 3, 2, 4]
def baseStart_7749525 : Nat := 118140960795 + 7749525 * 2 ^ 59
def prefixEnd_7749525 : Nat := 4983230072969 + 3 ^ 40 * 7749525 * 2
def baseEnd_7749525 : Nat := 3979231169033897681498089

theorem tailTrace_7749525 : CollatzResearch.WordTrace tailWord_7749525 prefixEnd_7749525 3979231169033897681498089 := by
  unfold tailWord_7749525
  simp only [CollatzResearch.WordTrace]
  refine ⟨282648397249801913344818029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188432264833201275563212019 282648397249801913344818029)
  ·
    refine ⟨105993148968675717504306761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282648397249801913344818029 105993148968675717504306761)
    ·
      refine ⟨79494861726506788128230071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105993148968675717504306761 79494861726506788128230071)
      ·
        refine ⟨119242292589760182192345107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79494861726506788128230071 119242292589760182192345107)
        ·
          refine ⟨178863438884640273288517661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119242292589760182192345107 178863438884640273288517661)
          ·
            refine ⟨67073789581740102483194123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178863438884640273288517661 67073789581740102483194123)
            ·
              refine ⟨100610684372610153724791185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67073789581740102483194123 100610684372610153724791185)
              ·
                refine ⟨75458013279457615293593389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100610684372610153724791185 75458013279457615293593389)
                ·
                  refine ⟨28296754979796605735097521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75458013279457615293593389 28296754979796605735097521)
                  ·
                    refine ⟨21222566234847454301323141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28296754979796605735097521 21222566234847454301323141)
                    ·
                      refine ⟨3979231169033897681498089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21222566234847454301323141 3979231169033897681498089)
                      ·
                        rfl

theorem cell23_7749525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_7749525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749525 prefixEnd_7749525 := by exact prefixLift 7749525
  have htrace : WordTrace (prefixWord ++ tailWord_7749525) baseStart_7749525 baseEnd_7749525 := by
    simpa [prefixWord, tailWord_7749525, baseEnd_7749525] using wordTrace_append hprefix tailTrace_7749525
  have hstable : (prefixWord ++ tailWord_7749525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749525).length < 2 ^ (prefixWord ++ tailWord_7749525).sum := by decide
  have hdescent : baseEnd_7749525 < baseStart_7749525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749566 : List Nat := [4, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3]
def baseStart_7749566 : Nat := 118140960795 + 7749566 * 2 ^ 59
def prefixEnd_7749566 : Nat := 4983230072969 + 3 ^ 40 * 7749566 * 2
def baseEnd_7749566 : Nat := 3979252221740732021085401

theorem tailTrace_7749566 : CollatzResearch.WordTrace tailWord_7749566 prefixEnd_7749566 3979252221740732021085401 := by
  unfold tailWord_7749566
  simp only [CollatzResearch.WordTrace]
  refine ⟨35331236580331672168382569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188433261761768918231373701 35331236580331672168382569)
  ·
    refine ⟨26498427435248754126286927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35331236580331672168382569 26498427435248754126286927)
    ·
      refine ⟨39747641152873131189430391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26498427435248754126286927 39747641152873131189430391)
      ·
        refine ⟨59621461729309696784145587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39747641152873131189430391 59621461729309696784145587)
        ·
          refine ⟨89432192593964545176218381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59621461729309696784145587 89432192593964545176218381)
          ·
            refine ⟨33537072222736704441081893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89432192593964545176218381 33537072222736704441081893)
            ·
              refine ⟨6288201041763132082702855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33537072222736704441081893 6288201041763132082702855)
              ·
                refine ⟨9432301562644698124054283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6288201041763132082702855 9432301562644698124054283)
                ·
                  refine ⟨14148452343967047186081425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9432301562644698124054283 14148452343967047186081425)
                  ·
                    refine ⟨10611339257975285389561069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14148452343967047186081425 10611339257975285389561069)
                    ·
                      refine ⟨3979252221740732021085401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10611339257975285389561069 3979252221740732021085401)
                      ·
                        rfl

theorem cell23_7749566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_7749566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749566 prefixEnd_7749566 := by exact prefixLift 7749566
  have htrace : WordTrace (prefixWord ++ tailWord_7749566) baseStart_7749566 baseEnd_7749566 := by
    simpa [prefixWord, tailWord_7749566, baseEnd_7749566] using wordTrace_append hprefix tailTrace_7749566
  have hstable : (prefixWord ++ tailWord_7749566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749566).length < 2 ^ (prefixWord ++ tailWord_7749566).sum := by decide
  have hdescent : baseEnd_7749566 < baseStart_7749566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749585 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 2, 3, 4]
def baseStart_7749585 : Nat := 118140960795 + 7749585 * 2 ^ 59
def prefixEnd_7749585 : Nat := 4983230072969 + 3 ^ 40 * 7749585 * 2
def baseEnd_7749585 : Nat := 3979261977873167446747813

theorem tailTrace_7749585 : CollatzResearch.WordTrace tailWord_7749585 prefixEnd_7749585 3979261977873167446747813 := by
  unfold tailWord_7749585
  simp only [CollatzResearch.WordTrace]
  refine ⟨282650585629584543592002209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188433723753056362394668139 282650585629584543592002209)
  ·
    refine ⟨211987939222188407694001657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282650585629584543592002209 211987939222188407694001657)
    ·
      refine ⟨158990954416641305770501243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211987939222188407694001657 158990954416641305770501243)
      ·
        refine ⟨238486431624961958655751865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158990954416641305770501243 238486431624961958655751865)
        ·
          refine ⟨178864823718721468991813899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238486431624961958655751865 178864823718721468991813899)
          ·
            refine ⟨268297235578082203487720849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178864823718721468991813899 268297235578082203487720849)
            ·
              refine ⟨201222926683561652615790637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268297235578082203487720849 201222926683561652615790637)
              ·
                refine ⟨75458597506335619730921489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201222926683561652615790637 75458597506335619730921489)
                ·
                  refine ⟨56593948129751714798191117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75458597506335619730921489 56593948129751714798191117)
                  ·
                    refine ⟨21222730548656893049321669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56593948129751714798191117 21222730548656893049321669)
                    ·
                      refine ⟨3979261977873167446747813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21222730548656893049321669 3979261977873167446747813)
                      ·
                        rfl

theorem cell23_7749585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_7749585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749585 prefixEnd_7749585 := by exact prefixLift 7749585
  have htrace : WordTrace (prefixWord ++ tailWord_7749585) baseStart_7749585 baseEnd_7749585 := by
    simpa [prefixWord, tailWord_7749585, baseEnd_7749585] using wordTrace_append hprefix tailTrace_7749585
  have hstable : (prefixWord ++ tailWord_7749585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749585).length < 2 ^ (prefixWord ++ tailWord_7749585).sum := by decide
  have hdescent : baseEnd_7749585 < baseStart_7749585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749653 : List Nat := [1, 3, 2, 1, 5, 1, 1, 3, 2, 2, 2]
def baseStart_7749653 : Nat := 118140960795 + 7749653 * 2 ^ 59
def prefixEnd_7749653 : Nat := 4983230072969 + 3 ^ 40 * 7749653 * 2
def baseEnd_7749653 : Nat := 3979296894557673180697501

theorem tailTrace_7749653 : CollatzResearch.WordTrace tailWord_7749653 prefixEnd_7749653 3979296894557673180697501 := by
  unfold tailWord_7749653
  simp only [CollatzResearch.WordTrace]
  refine ⟨282653065793338191205477613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188435377195558794136985075 282653065793338191205477613)
  ·
    refine ⟨105994899672501821702054105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282653065793338191205477613 105994899672501821702054105)
    ·
      refine ⟨79496174754376366276540579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105994899672501821702054105 79496174754376366276540579)
      ·
        refine ⟨119244262131564549414810869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79496174754376366276540579 119244262131564549414810869)
        ·
          refine ⟨11179149574834176507638519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119244262131564549414810869 11179149574834176507638519)
          ·
            refine ⟨16768724362251264761457779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11179149574834176507638519 16768724362251264761457779)
            ·
              refine ⟨25153086543376897142186669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16768724362251264761457779 25153086543376897142186669)
              ·
                refine ⟨9432407453766336428320001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25153086543376897142186669 9432407453766336428320001)
                ·
                  refine ⟨7074305590324752321240001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9432407453766336428320001 7074305590324752321240001)
                  ·
                    refine ⟨5305729192743564240930001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7074305590324752321240001 5305729192743564240930001)
                    ·
                      refine ⟨3979296894557673180697501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5305729192743564240930001 3979296894557673180697501)
                      ·
                        rfl

theorem cell23_7749653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 2, 2].length) (baseStart_7749653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749653 prefixEnd_7749653 := by exact prefixLift 7749653
  have htrace : WordTrace (prefixWord ++ tailWord_7749653) baseStart_7749653 baseEnd_7749653 := by
    simpa [prefixWord, tailWord_7749653, baseEnd_7749653] using wordTrace_append hprefix tailTrace_7749653
  have hstable : (prefixWord ++ tailWord_7749653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749653).length < 2 ^ (prefixWord ++ tailWord_7749653).sum := by decide
  have hdescent : baseEnd_7749653 < baseStart_7749653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749682 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5]
def baseStart_7749682 : Nat := 118140960795 + 7749682 * 2 ^ 59
def prefixEnd_7749682 : Nat := 4983230072969 + 3 ^ 40 * 7749682 * 2
def baseEnd_7749682 : Nat := 3979311785496653567234867

theorem tailTrace_7749682 : CollatzResearch.WordTrace tailWord_7749682 prefixEnd_7749682 3979311785496653567234867 := by
  unfold tailWord_7749682
  simp only [CollatzResearch.WordTrace]
  refine ⟨70663530877558282289570825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188436082340155419438855533 70663530877558282289570825)
  ·
    refine ⟨52997648158168711717178119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70663530877558282289570825 52997648158168711717178119)
    ·
      refine ⟨79496472237253067575767179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52997648158168711717178119 79496472237253067575767179)
      ·
        refine ⟨119244708355879601363650769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79496472237253067575767179 119244708355879601363650769)
        ·
          refine ⟨89433531266909701022738077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119244708355879601363650769 89433531266909701022738077)
          ·
            refine ⟨33537574225091137883526779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89433531266909701022738077 33537574225091137883526779)
            ·
              refine ⟨50306361337636706825290169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33537574225091137883526779 50306361337636706825290169)
              ·
                refine ⟨37729771003227530118967627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50306361337636706825290169 37729771003227530118967627)
                ·
                  refine ⟨56594656504841295178451441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37729771003227530118967627 56594656504841295178451441)
                  ·
                    refine ⟨42445992378630971383838581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56594656504841295178451441 42445992378630971383838581)
                    ·
                      refine ⟨3979311785496653567234867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42445992378630971383838581 3979311785496653567234867)
                      ·
                        rfl

theorem cell23_7749682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_7749682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749682 prefixEnd_7749682 := by exact prefixLift 7749682
  have htrace : WordTrace (prefixWord ++ tailWord_7749682) baseStart_7749682 baseEnd_7749682 := by
    simpa [prefixWord, tailWord_7749682, baseEnd_7749682] using wordTrace_append hprefix tailTrace_7749682
  have hstable : (prefixWord ++ tailWord_7749682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749682).length < 2 ^ (prefixWord ++ tailWord_7749682).sum := by decide
  have hdescent : baseEnd_7749682 < baseStart_7749682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749709 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_7749709 : Nat := 118140960795 + 7749709 * 2 ^ 59
def prefixEnd_7749709 : Nat := 4983230072969 + 3 ^ 40 * 7749709 * 2
def baseEnd_7749709 : Nat := 3979325649474324961597243

theorem tailTrace_7749709 : CollatzResearch.WordTrace tailWord_7749709 prefixEnd_7749709 3979325649474324961597243 := by
  unfold tailWord_7749709
  simp only [CollatzResearch.WordTrace]
  refine ⟨282655108281135312769516181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188436738854090208513010787 282655108281135312769516181)
  ·
    refine ⟨13249458200678217786071071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 282655108281135312769516181 13249458200678217786071071)
    ·
      refine ⟨19874187301017326679106607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13249458200678217786071071 19874187301017326679106607)
      ·
        refine ⟨29811280951525990018659911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19874187301017326679106607 29811280951525990018659911)
        ·
          refine ⟨44716921427288985027989867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29811280951525990018659911 44716921427288985027989867)
          ·
            refine ⟨67075382140933477541984801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44716921427288985027989867 67075382140933477541984801)
            ·
              refine ⟨50306536605700108156488601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67075382140933477541984801 50306536605700108156488601)
              ·
                refine ⟨37729902454275081117366451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50306536605700108156488601 37729902454275081117366451)
                ·
                  refine ⟨56594853681412621676049677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37729902454275081117366451 56594853681412621676049677)
                  ·
                    refine ⟨21223070130529733128518629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56594853681412621676049677 21223070130529733128518629)
                    ·
                      refine ⟨3979325649474324961597243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21223070130529733128518629 3979325649474324961597243)
                      ·
                        rfl

theorem cell23_7749709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_7749709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749709 prefixEnd_7749709 := by exact prefixLift 7749709
  have htrace : WordTrace (prefixWord ++ tailWord_7749709) baseStart_7749709 baseEnd_7749709 := by
    simpa [prefixWord, tailWord_7749709, baseEnd_7749709] using wordTrace_append hprefix tailTrace_7749709
  have hstable : (prefixWord ++ tailWord_7749709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749709).length < 2 ^ (prefixWord ++ tailWord_7749709).sum := by decide
  have hdescent : baseEnd_7749709 < baseStart_7749709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749769 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 3, 5, 2]
def baseStart_7749769 : Nat := 118140960795 + 7749769 * 2 ^ 59
def prefixEnd_7749769 : Nat := 4983230072969 + 3 ^ 40 * 7749769 * 2
def baseEnd_7749769 : Nat := 3979356458313594726846967

theorem tailTrace_7749769 : CollatzResearch.WordTrace tailWord_7749769 prefixEnd_7749769 3979356458313594726846967 := by
  unfold tailWord_7749769
  simp only [CollatzResearch.WordTrace]
  refine ⟨282657296660917943016700361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188438197773945295344466907 282657296660917943016700361)
  ·
    refine ⟨211992972495688457262525271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282657296660917943016700361 211992972495688457262525271)
    ·
      refine ⟨317989458743532685893787907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211992972495688457262525271 317989458743532685893787907)
      ·
        refine ⟨476984188115299028840681861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317989458743532685893787907 476984188115299028840681861)
        ·
          refine ⟨89434535271618567907627849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 476984188115299028840681861 89434535271618567907627849)
          ·
            refine ⟨67075901453713925930720887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89434535271618567907627849 67075901453713925930720887)
            ·
              refine ⟨100613852180570888896081331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67075901453713925930720887 100613852180570888896081331)
              ·
                refine ⟨150920778270856333344121997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100613852180570888896081331 150920778270856333344121997)
                ·
                  refine ⟨56595291851571125004045749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150920778270856333344121997 56595291851571125004045749)
                  ·
                    refine ⟨5305808611084792969129289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56595291851571125004045749 5305808611084792969129289)
                    ·
                      refine ⟨3979356458313594726846967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5305808611084792969129289 3979356458313594726846967)
                      ·
                        rfl

theorem cell23_7749769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 5, 2].length) (baseStart_7749769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749769 prefixEnd_7749769 := by exact prefixLift 7749769
  have htrace : WordTrace (prefixWord ++ tailWord_7749769) baseStart_7749769 baseEnd_7749769 := by
    simpa [prefixWord, tailWord_7749769, baseEnd_7749769] using wordTrace_append hprefix tailTrace_7749769
  have hstable : (prefixWord ++ tailWord_7749769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749769).length < 2 ^ (prefixWord ++ tailWord_7749769).sum := by decide
  have hdescent : baseEnd_7749769 < baseStart_7749769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749810 : List Nat := [3, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3]
def baseStart_7749810 : Nat := 118140960795 + 7749810 * 2 ^ 59
def prefixEnd_7749810 : Nat := 4983230072969 + 3 ^ 40 * 7749810 * 2
def baseEnd_7749810 : Nat := 3979377511020429066434279

theorem tailTrace_7749810 : CollatzResearch.WordTrace tailWord_7749810 prefixEnd_7749810 3979377511020429066434279 := by
  unfold tailWord_7749810
  simp only [CollatzResearch.WordTrace]
  refine ⟨70664698013442351754735721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188439194702512938012628589 70664698013442351754735721)
  ·
    refine ⟨52998523510081763816051791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70664698013442351754735721 52998523510081763816051791)
    ·
      refine ⟨79497785265122645724077687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52998523510081763816051791 79497785265122645724077687)
      ·
        refine ⟨119246677897683968586116531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79497785265122645724077687 119246677897683968586116531)
        ·
          refine ⟨178870016846525952879174797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119246677897683968586116531 178870016846525952879174797)
          ·
            refine ⟨67076256317447232329690549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178870016846525952879174797 67076256317447232329690549)
            ·
              refine ⟨6288399029760678030908489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67076256317447232329690549 6288399029760678030908489)
              ·
                refine ⟨4716299272320508523181367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6288399029760678030908489 4716299272320508523181367)
                ·
                  refine ⟨7074448908480762784772051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4716299272320508523181367 7074448908480762784772051)
                  ·
                    refine ⟨10611673362721144177158077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7074448908480762784772051 10611673362721144177158077)
                    ·
                      refine ⟨3979377511020429066434279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10611673362721144177158077 3979377511020429066434279)
                      ·
                        rfl

theorem cell23_7749810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3].length) (baseStart_7749810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749810 prefixEnd_7749810 := by exact prefixLift 7749810
  have htrace : WordTrace (prefixWord ++ tailWord_7749810) baseStart_7749810 baseEnd_7749810 := by
    simpa [prefixWord, tailWord_7749810, baseEnd_7749810] using wordTrace_append hprefix tailTrace_7749810
  have hstable : (prefixWord ++ tailWord_7749810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749810).length < 2 ^ (prefixWord ++ tailWord_7749810).sum := by decide
  have hdescent : baseEnd_7749810 < baseStart_7749810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749819 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 3]
def baseStart_7749819 : Nat := 118140960795 + 7749819 * 2 ^ 59
def prefixEnd_7749819 : Nat := 4983230072969 + 3 ^ 40 * 7749819 * 2
def baseEnd_7749819 : Nat := 3979382132346319531221737

theorem tailTrace_7749819 : CollatzResearch.WordTrace tailWord_7749819 prefixEnd_7749819 3979382132346319531221737 := by
  unfold tailWord_7749819
  simp only [CollatzResearch.WordTrace]
  refine ⟨282659120310736801556020511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188439413540491201037347007 282659120310736801556020511)
  ·
    refine ⟨423988680466105202334030767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282659120310736801556020511 423988680466105202334030767)
    ·
      refine ⟨635983020699157803501046151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423988680466105202334030767 635983020699157803501046151)
      ·
        refine ⟨953974531048736705251569227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635983020699157803501046151 953974531048736705251569227)
        ·
          refine ⟨1430961796573105057877353841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953974531048736705251569227 1430961796573105057877353841)
          ·
            refine ⟨1073221347429828793408015381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1430961796573105057877353841 1073221347429828793408015381)
            ·
              refine ⟨50307250660773224691000721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1073221347429828793408015381 50307250660773224691000721)
              ·
                refine ⟨37730437995579918518250541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50307250660773224691000721 37730437995579918518250541)
                ·
                  refine ⟨14148914248342469444343953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37730437995579918518250541 14148914248342469444343953)
                  ·
                    refine ⟨10611685686256852083257965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14148914248342469444343953 10611685686256852083257965)
                    ·
                      refine ⟨3979382132346319531221737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10611685686256852083257965 3979382132346319531221737)
                      ·
                        rfl

theorem cell23_7749819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 3].length) (baseStart_7749819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749819 prefixEnd_7749819 := by exact prefixLift 7749819
  have htrace : WordTrace (prefixWord ++ tailWord_7749819) baseStart_7749819 baseEnd_7749819 := by
    simpa [prefixWord, tailWord_7749819, baseEnd_7749819] using wordTrace_append hprefix tailTrace_7749819
  have hstable : (prefixWord ++ tailWord_7749819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749819).length < 2 ^ (prefixWord ++ tailWord_7749819).sum := by decide
  have hdescent : baseEnd_7749819 < baseStart_7749819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749849 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 3, 3, 3]
def baseStart_7749849 : Nat := 118140960795 + 7749849 * 2 ^ 59
def prefixEnd_7749849 : Nat := 4983230072969 + 3 ^ 40 * 7749849 * 2
def baseEnd_7749849 : Nat := 3979397536765954413846599

theorem tailTrace_7749849 : CollatzResearch.WordTrace tailWord_7749849 prefixEnd_7749849 3979397536765954413846599 := by
  unfold tailWord_7749849
  simp only [CollatzResearch.WordTrace]
  refine ⟨282660214500628116679612601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188440143000418744453075067 282660214500628116679612601)
  ·
    refine ⟨211995160875471087509709451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282660214500628116679612601 211995160875471087509709451)
    ·
      refine ⟨317992741313206631264564177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211995160875471087509709451 317992741313206631264564177)
      ·
        refine ⟨238494555984904973448423133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317992741313206631264564177 238494555984904973448423133)
        ·
          refine ⟨89435458494339365043158675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238494555984904973448423133 89435458494339365043158675)
          ·
            refine ⟨134153187741509047564738013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89435458494339365043158675 134153187741509047564738013)
            ·
              refine ⟨50307445403065892836776755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134153187741509047564738013 50307445403065892836776755)
              ·
                refine ⟨75461168104598839255165133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50307445403065892836776755 75461168104598839255165133)
                ·
                  refine ⟨28297938039224564720686925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75461168104598839255165133 28297938039224564720686925)
                  ·
                    refine ⟨10611726764709211770257597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28297938039224564720686925 10611726764709211770257597)
                    ·
                      refine ⟨3979397536765954413846599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10611726764709211770257597 3979397536765954413846599)
                      ·
                        rfl

theorem cell23_7749849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 3, 3].length) (baseStart_7749849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749849 prefixEnd_7749849 := by exact prefixLift 7749849
  have htrace : WordTrace (prefixWord ++ tailWord_7749849) baseStart_7749849 baseEnd_7749849 := by
    simpa [prefixWord, tailWord_7749849, baseEnd_7749849] using wordTrace_append hprefix tailTrace_7749849
  have hstable : (prefixWord ++ tailWord_7749849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749849).length < 2 ^ (prefixWord ++ tailWord_7749849).sum := by decide
  have hdescent : baseEnd_7749849 < baseStart_7749849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749853 : List Nat := [1, 4, 3, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_7749853 : Nat := 118140960795 + 7749853 * 2 ^ 59
def prefixEnd_7749853 : Nat := 4983230072969 + 3 ^ 40 * 7749853 * 2
def baseEnd_7749853 : Nat := 3979399590688572398196581

theorem tailTrace_7749853 : CollatzResearch.WordTrace tailWord_7749853 prefixEnd_7749853 3979399590688572398196581 := by
  unfold tailWord_7749853
  simp only [CollatzResearch.WordTrace]
  refine ⟨282660360392613625362758213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188440240261742416908505475 282660360392613625362758213)
  ·
    refine ⟨52998817573615054755517165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282660360392613625362758213 52998817573615054755517165)
    ·
      refine ⟨19874556590105645533318937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52998817573615054755517165 19874556590105645533318937)
      ·
        refine ⟨14905917442579234149989203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19874556590105645533318937 14905917442579234149989203)
        ·
          refine ⟨22358876163868851224983805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14905917442579234149989203 22358876163868851224983805)
          ·
            refine ⟨8384578561450819209368927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22358876163868851224983805 8384578561450819209368927)
            ·
              refine ⟨12576867842176228814053391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8384578561450819209368927 12576867842176228814053391)
              ·
                refine ⟨18865301763264343221080087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12576867842176228814053391 18865301763264343221080087)
                ·
                  refine ⟨28297952644896514831620131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18865301763264343221080087 28297952644896514831620131)
                  ·
                    refine ⟨42446928967344772247430197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28297952644896514831620131 42446928967344772247430197)
                    ·
                      refine ⟨3979399590688572398196581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42446928967344772247430197 3979399590688572398196581)
                      ·
                        rfl

theorem cell23_7749853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_7749853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749853 prefixEnd_7749853 := by exact prefixLift 7749853
  have htrace : WordTrace (prefixWord ++ tailWord_7749853) baseStart_7749853 baseEnd_7749853 := by
    simpa [prefixWord, tailWord_7749853, baseEnd_7749853] using wordTrace_append hprefix tailTrace_7749853
  have hstable : (prefixWord ++ tailWord_7749853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749853).length < 2 ^ (prefixWord ++ tailWord_7749853).sum := by decide
  have hdescent : baseEnd_7749853 < baseStart_7749853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749889 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_7749889 : Nat := 118140960795 + 7749889 * 2 ^ 59
def prefixEnd_7749889 : Nat := 4983230072969 + 3 ^ 40 * 7749889 * 2
def baseEnd_7749889 : Nat := 3979418075992134257346415

theorem tailTrace_7749889 : CollatzResearch.WordTrace tailWord_7749889 prefixEnd_7749889 3979418075992134257346415 := by
  unfold tailWord_7749889
  simp only [CollatzResearch.WordTrace]
  refine ⟨282661673420483203511068721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188441115613655469007379147 282661673420483203511068721)
  ·
    refine ⟨211996255065362402633301541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282661673420483203511068721 211996255065362402633301541)
    ·
      refine ⟨39749297824755450493744039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211996255065362402633301541 39749297824755450493744039)
      ·
        refine ⟨59623946737133175740616059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39749297824755450493744039 59623946737133175740616059)
        ·
          refine ⟨89435920105699763610924089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59623946737133175740616059 89435920105699763610924089)
          ·
            refine ⟨67076940079274822708193067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89435920105699763610924089 67076940079274822708193067)
            ·
              refine ⟨100615410118912234062289601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67076940079274822708193067 100615410118912234062289601)
              ·
                refine ⟨75461557589184175546717201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100615410118912234062289601 75461557589184175546717201)
                ·
                  refine ⟨56596168191888131660037901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75461557589184175546717201 56596168191888131660037901)
                  ·
                    refine ⟨21223563071958049372514213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56596168191888131660037901 21223563071958049372514213)
                    ·
                      refine ⟨3979418075992134257346415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21223563071958049372514213 3979418075992134257346415)
                      ·
                        rfl

theorem cell23_7749889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_7749889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749889 prefixEnd_7749889 := by exact prefixLift 7749889
  have htrace : WordTrace (prefixWord ++ tailWord_7749889) baseStart_7749889 baseEnd_7749889 := by
    simpa [prefixWord, tailWord_7749889, baseEnd_7749889] using wordTrace_append hprefix tailTrace_7749889
  have hstable : (prefixWord ++ tailWord_7749889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749889).length < 2 ^ (prefixWord ++ tailWord_7749889).sum := by decide
  have hdescent : baseEnd_7749889 < baseStart_7749889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749909 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 2, 1, 5]
def baseStart_7749909 : Nat := 118140960795 + 7749909 * 2 ^ 59
def prefixEnd_7749909 : Nat := 4983230072969 + 3 ^ 40 * 7749909 * 2
def baseEnd_7749909 : Nat := 3979428345605224179096323

theorem tailTrace_7749909 : CollatzResearch.WordTrace tailWord_7749909 prefixEnd_7749909 3979428345605224179096323 := by
  unfold tailWord_7749909
  simp only [CollatzResearch.WordTrace]
  refine ⟨282662402880410746926796781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188441601920273831284531187 282662402880410746926796781)
  ·
    refine ⟨105998401080154030097548793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282662402880410746926796781 105998401080154030097548793)
    ·
      refine ⟨79498800810115522573161595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105998401080154030097548793 79498800810115522573161595)
      ·
        refine ⟨119248201215173283859742393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79498800810115522573161595 119248201215173283859742393)
        ·
          refine ⟨89436150911379962894806795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119248201215173283859742393 89436150911379962894806795)
          ·
            refine ⟨134154226367069944342210193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89436150911379962894806795 134154226367069944342210193)
            ·
              refine ⟨100615669775302458256657645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134154226367069944342210193 100615669775302458256657645)
              ·
                refine ⟨37730876165738421846246617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100615669775302458256657645 37730876165738421846246617)
                ·
                  refine ⟨28298157124303816384684963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37730876165738421846246617 28298157124303816384684963)
                  ·
                    refine ⟨42447235686455724577027445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28298157124303816384684963 42447235686455724577027445)
                    ·
                      refine ⟨3979428345605224179096323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42447235686455724577027445 3979428345605224179096323)
                      ·
                        rfl

theorem cell23_7749909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_7749909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749909 prefixEnd_7749909 := by exact prefixLift 7749909
  have htrace : WordTrace (prefixWord ++ tailWord_7749909) baseStart_7749909 baseEnd_7749909 := by
    simpa [prefixWord, tailWord_7749909, baseEnd_7749909] using wordTrace_append hprefix tailTrace_7749909
  have hstable : (prefixWord ++ tailWord_7749909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749909).length < 2 ^ (prefixWord ++ tailWord_7749909).sum := by decide
  have hdescent : baseEnd_7749909 < baseStart_7749909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749917 : List Nat := [1, 4, 2, 3, 2, 2, 1, 2, 2, 1, 3]
def baseStart_7749917 : Nat := 118140960795 + 7749917 * 2 ^ 59
def prefixEnd_7749917 : Nat := 4983230072969 + 3 ^ 40 * 7749917 * 2
def baseEnd_7749917 : Nat := 3979432453450460147796287

theorem tailTrace_7749917 : CollatzResearch.WordTrace tailWord_7749917 prefixEnd_7749917 3979432453450460147796287 := by
  unfold tailWord_7749917
  simp only [CollatzResearch.WordTrace]
  refine ⟨282662694664381764293088005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188441796442921176195392003 282662694664381764293088005)
  ·
    refine ⟨52999255249571580804954001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282662694664381764293088005 52999255249571580804954001)
    ·
      refine ⟨39749441437178685603715501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52999255249571580804954001 39749441437178685603715501)
      ·
        refine ⟨14906040538942007101393313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39749441437178685603715501 14906040538942007101393313)
        ·
          refine ⟨11179530404206505326044985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14906040538942007101393313 11179530404206505326044985)
          ·
            refine ⟨8384647803154878994533739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11179530404206505326044985 8384647803154878994533739)
            ·
              refine ⟨12576971704732318491800609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8384647803154878994533739 12576971704732318491800609)
              ·
                refine ⟨9432728778549238868850457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12576971704732318491800609 9432728778549238868850457)
                ·
                  refine ⟨7074546583911929151637843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9432728778549238868850457 7074546583911929151637843)
                  ·
                    refine ⟨10611819875867893727456765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7074546583911929151637843 10611819875867893727456765)
                    ·
                      refine ⟨3979432453450460147796287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10611819875867893727456765 3979432453450460147796287)
                      ·
                        rfl

theorem cell23_7749917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_7749917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749917 prefixEnd_7749917 := by exact prefixLift 7749917
  have htrace : WordTrace (prefixWord ++ tailWord_7749917) baseStart_7749917 baseEnd_7749917 := by
    simpa [prefixWord, tailWord_7749917, baseEnd_7749917] using wordTrace_append hprefix tailTrace_7749917
  have hstable : (prefixWord ++ tailWord_7749917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749917).length < 2 ^ (prefixWord ++ tailWord_7749917).sum := by decide
  have hdescent : baseEnd_7749917 < baseStart_7749917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749923 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 4, 2, 2]
def baseStart_7749923 : Nat := 118140960795 + 7749923 * 2 ^ 59
def prefixEnd_7749923 : Nat := 4983230072969 + 3 ^ 40 * 7749923 * 2
def baseEnd_7749923 : Nat := 3979435534334387124321259

theorem tailTrace_7749923 : CollatzResearch.WordTrace tailWord_7749923 prefixEnd_7749923 3979435534334387124321259 := by
  unfold tailWord_7749923
  simp only [CollatzResearch.WordTrace]
  refine ⟨282662913502360027317806423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188441942334906684878537615 282662913502360027317806423)
  ·
    refine ⟨423994370253540040976709635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282662913502360027317806423 423994370253540040976709635)
    ·
      refine ⟨635991555380310061465064453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423994370253540040976709635 635991555380310061465064453)
      ·
        refine ⟨119248416633808136524699585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 635991555380310061465064453 119248416633808136524699585)
        ·
          refine ⟨89436312475356102393524689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119248416633808136524699585 89436312475356102393524689)
          ·
            refine ⟨67077234356517076795143517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89436312475356102393524689 67077234356517076795143517)
            ·
              refine ⟨25153962883693903798178819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67077234356517076795143517 25153962883693903798178819)
              ·
                refine ⟨37730944325540855697268229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25153962883693903798178819 37730944325540855697268229)
                ·
                  refine ⟨7074552061038910443237793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37730944325540855697268229 7074552061038910443237793)
                  ·
                    refine ⟨5305914045779182832428345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7074552061038910443237793 5305914045779182832428345)
                    ·
                      refine ⟨3979435534334387124321259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5305914045779182832428345 3979435534334387124321259)
                      ·
                        rfl

theorem cell23_7749923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 2, 2].length) (baseStart_7749923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749923 prefixEnd_7749923 := by exact prefixLift 7749923
  have htrace : WordTrace (prefixWord ++ tailWord_7749923) baseStart_7749923 baseEnd_7749923 := by
    simpa [prefixWord, tailWord_7749923, baseEnd_7749923] using wordTrace_append hprefix tailTrace_7749923
  have hstable : (prefixWord ++ tailWord_7749923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749923).length < 2 ^ (prefixWord ++ tailWord_7749923).sum := by decide
  have hdescent : baseEnd_7749923 < baseStart_7749923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749934 : List Nat := [4, 1, 3, 3, 1, 1, 3, 1, 2, 1, 3]
def baseStart_7749934 : Nat := 118140960795 + 7749934 * 2 ^ 59
def prefixEnd_7749934 : Nat := 4983230072969 + 3 ^ 40 * 7749934 * 2
def baseEnd_7749934 : Nat := 3979441182621586581283709

theorem tailTrace_7749934 : CollatzResearch.WordTrace tailWord_7749934 prefixEnd_7749934 3979441182621586581283709 := by
  unfold tailWord_7749934
  simp only [CollatzResearch.WordTrace]
  refine ⟨35332914338165022024557107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188442209803546784130971237 35332914338165022024557107)
  ·
    refine ⟨52999371507247533036835661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35332914338165022024557107 52999371507247533036835661)
    ·
      refine ⟨19874764315217824888813373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52999371507247533036835661 19874764315217824888813373)
      ·
        refine ⟨7453036618206684333305015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19874764315217824888813373 7453036618206684333305015)
        ·
          refine ⟨11179554927310026499957523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7453036618206684333305015 11179554927310026499957523)
          ·
            refine ⟨16769332390965039749936285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11179554927310026499957523 16769332390965039749936285)
            ·
              refine ⟨6288499646611889906226107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16769332390965039749936285 6288499646611889906226107)
              ·
                refine ⟨9432749469917834859339161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6288499646611889906226107 9432749469917834859339161)
                ·
                  refine ⟨7074562102438376144504371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9432749469917834859339161 7074562102438376144504371)
                  ·
                    refine ⟨10611843153657564216756557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7074562102438376144504371 10611843153657564216756557)
                    ·
                      refine ⟨3979441182621586581283709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10611843153657564216756557 3979441182621586581283709)
                      ·
                        rfl

theorem cell23_7749934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_7749934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749934 prefixEnd_7749934 := by exact prefixLift 7749934
  have htrace : WordTrace (prefixWord ++ tailWord_7749934) baseStart_7749934 baseEnd_7749934 := by
    simpa [prefixWord, tailWord_7749934, baseEnd_7749934] using wordTrace_append hprefix tailTrace_7749934
  have hstable : (prefixWord ++ tailWord_7749934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749934).length < 2 ^ (prefixWord ++ tailWord_7749934).sum := by decide
  have hdescent : baseEnd_7749934 < baseStart_7749934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749940 : List Nat := [2, 5, 1, 1, 1, 2, 3, 1, 1, 4, 2]
def baseStart_7749940 : Nat := 118140960795 + 7749940 * 2 ^ 59
def prefixEnd_7749940 : Nat := 4983230072969 + 3 ^ 40 * 7749940 * 2
def baseEnd_7749940 : Nat := 3979444263505513557808681

theorem tailTrace_7749940 : CollatzResearch.WordTrace tailWord_7749940 prefixEnd_7749940 3979444263505513557808681 := by
  unfold tailWord_7749940
  simp only [CollatzResearch.WordTrace]
  refine ⟨141331766771649219610587637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188442355695532292814116849 141331766771649219610587637)
  ·
    refine ⟨13249853134842114338492591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141331766771649219610587637 13249853134842114338492591)
    ·
      refine ⟨19874779702263171507738887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13249853134842114338492591 19874779702263171507738887)
      ·
        refine ⟨29812169553394757261608331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19874779702263171507738887 29812169553394757261608331)
        ·
          refine ⟨44718254330092135892412497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29812169553394757261608331 44718254330092135892412497)
          ·
            refine ⟨33538690747569101919309373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44718254330092135892412497 33538690747569101919309373)
            ·
              refine ⟨12577009030338413219741015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33538690747569101919309373 12577009030338413219741015)
              ·
                refine ⟨18865513545507619829611523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12577009030338413219741015 18865513545507619829611523)
                ·
                  refine ⟨28298270318261429744417285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18865513545507619829611523 28298270318261429744417285)
                  ·
                    refine ⟨5305925684674018077078241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28298270318261429744417285 5305925684674018077078241)
                    ·
                      refine ⟨3979444263505513557808681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5305925684674018077078241 3979444263505513557808681)
                      ·
                        rfl

theorem cell23_7749940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_7749940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749940 prefixEnd_7749940 := by exact prefixLift 7749940
  have htrace : WordTrace (prefixWord ++ tailWord_7749940) baseStart_7749940 baseEnd_7749940 := by
    simpa [prefixWord, tailWord_7749940, baseEnd_7749940] using wordTrace_append hprefix tailTrace_7749940
  have hstable : (prefixWord ++ tailWord_7749940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749940).length < 2 ^ (prefixWord ++ tailWord_7749940).sum := by decide
  have hdescent : baseEnd_7749940 < baseStart_7749940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749959 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 1, 7]
def baseStart_7749959 : Nat := 118140960795 + 7749959 * 2 ^ 59
def prefixEnd_7749959 : Nat := 4983230072969 + 3 ^ 40 * 7749959 * 2
def baseEnd_7749959 : Nat := 1326484673212649661157031

theorem tailTrace_7749959 : CollatzResearch.WordTrace tailWord_7749959 prefixEnd_7749959 1326484673212649661157031 := by
  unfold tailWord_7749959
  simp only [CollatzResearch.WordTrace]
  refine ⟨282664226530229605466116931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188442817686819736977411287 282664226530229605466116931)
  ·
    refine ⟨423996339795344408199175397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282664226530229605466116931 423996339795344408199175397)
    ·
      refine ⟨79499313711627076537345387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 423996339795344408199175397 79499313711627076537345387)
      ·
        refine ⟨119248970567440614806018081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79499313711627076537345387 119248970567440614806018081)
        ·
          refine ⟨89436727925580461104513561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119248970567440614806018081 89436727925580461104513561)
          ·
            refine ⟨67077545944185345828385171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89436727925580461104513561 67077545944185345828385171)
            ·
              refine ⟨100616318916278018742577757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67077545944185345828385171 100616318916278018742577757)
              ·
                refine ⟨37731119593604257028466659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100616318916278018742577757 37731119593604257028466659)
                ·
                  refine ⟨56596679390406385542699989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37731119593604257028466659 56596679390406385542699989)
                  ·
                    refine ⟨1326484673212649661157031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56596679390406385542699989 1326484673212649661157031)
                    ·
                      rfl

theorem cell23_7749959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_7749959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749959 prefixEnd_7749959 := by exact prefixLift 7749959
  have htrace : WordTrace (prefixWord ++ tailWord_7749959) baseStart_7749959 baseEnd_7749959 := by
    simpa [prefixWord, tailWord_7749959, baseEnd_7749959] using wordTrace_append hprefix tailTrace_7749959
  have hstable : (prefixWord ++ tailWord_7749959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749959).length < 2 ^ (prefixWord ++ tailWord_7749959).sum := by decide
  have hdescent : baseEnd_7749959 < baseStart_7749959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749980 : List Nat := [2, 2, 4, 3, 1, 2, 1, 1, 7]
def baseStart_7749980 : Nat := 118140960795 + 7749980 * 2 ^ 59
def prefixEnd_7749980 : Nat := 4983230072969 + 3 ^ 40 * 7749980 * 2
def baseEnd_7749980 : Nat := 442162755859077044589833

theorem tailTrace_7749980 : CollatzResearch.WordTrace tailWord_7749980 prefixEnd_7749980 442162755859077044589833 := by
  unfold tailWord_7749980
  simp only [CollatzResearch.WordTrace]
  refine ⟨141332496231576763026315697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188443328308769017368420929 141332496231576763026315697)
  ·
    refine ⟨105999372173682572269736773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141332496231576763026315697 105999372173682572269736773)
    ·
      refine ⟨19874882282565482300575645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105999372173682572269736773 19874882282565482300575645)
      ·
        refine ⟨7453080855962055862715867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19874882282565482300575645 7453080855962055862715867)
        ·
          refine ⟨11179621283943083794073801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7453080855962055862715867 11179621283943083794073801)
          ·
            refine ⟨8384715962957312845555351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11179621283943083794073801 8384715962957312845555351)
            ·
              refine ⟨12577073944435969268333027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8384715962957312845555351 12577073944435969268333027)
              ·
                refine ⟨18865610916653953902499541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12577073944435969268333027 18865610916653953902499541)
                ·
                  refine ⟨442162755859077044589833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18865610916653953902499541 442162755859077044589833)
                  ·
                    rfl

theorem cell23_7749980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 7].length) (baseStart_7749980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749980 prefixEnd_7749980 := by exact prefixLift 7749980
  have htrace : WordTrace (prefixWord ++ tailWord_7749980) baseStart_7749980 baseEnd_7749980 := by
    simpa [prefixWord, tailWord_7749980, baseEnd_7749980] using wordTrace_append hprefix tailTrace_7749980
  have hstable : (prefixWord ++ tailWord_7749980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749980).length < 2 ^ (prefixWord ++ tailWord_7749980).sum := by decide
  have hdescent : baseEnd_7749980 < baseStart_7749980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749986 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_7749986 : Nat := 118140960795 + 7749986 * 2 ^ 59
def prefixEnd_7749986 : Nat := 4983230072969 + 3 ^ 40 * 7749986 * 2
def baseEnd_7749986 : Nat := 3979467883615620377833469

theorem tailTrace_7749986 : CollatzResearch.WordTrace tailWord_7749986 prefixEnd_7749986 3979467883615620377833469 := by
  unfold tailWord_7749986
  simp only [CollatzResearch.WordTrace]
  refine ⟨70666302825282947269337453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188443474200754526051566541 70666302825282947269337453)
  ·
    refine ⟨26499863559481105226001545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70666302825282947269337453 26499863559481105226001545)
    ·
      refine ⟨19874897669610828919501159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26499863559481105226001545 19874897669610828919501159)
      ·
        refine ⟨29812346504416243379251739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19874897669610828919501159 29812346504416243379251739)
        ·
          refine ⟨44718519756624365068877609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29812346504416243379251739 44718519756624365068877609)
          ·
            refine ⟨33538889817468273801658207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44718519756624365068877609 33538889817468273801658207)
            ·
              refine ⟨50308334726202410702487311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33538889817468273801658207 50308334726202410702487311)
              ·
                refine ⟨75462502089303616053730967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50308334726202410702487311 75462502089303616053730967)
                ·
                  refine ⟨113193753133955424080596451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75462502089303616053730967 113193753133955424080596451)
                  ·
                    refine ⟨169790629700933136120894677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113193753133955424080596451 169790629700933136120894677)
                    ·
                      refine ⟨3979467883615620377833469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169790629700933136120894677 3979467883615620377833469)
                      ·
                        rfl

theorem cell23_7749986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_7749986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749986 prefixEnd_7749986 := by exact prefixLift 7749986
  have htrace : WordTrace (prefixWord ++ tailWord_7749986) baseStart_7749986 baseEnd_7749986 := by
    simpa [prefixWord, tailWord_7749986, baseEnd_7749986] using wordTrace_append hprefix tailTrace_7749986
  have hstable : (prefixWord ++ tailWord_7749986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749986).length < 2 ^ (prefixWord ++ tailWord_7749986).sum := by decide
  have hdescent : baseEnd_7749986 < baseStart_7749986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750009 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 1, 3, 6]
def baseStart_7750009 : Nat := 118140960795 + 7750009 * 2 ^ 59
def prefixEnd_7750009 : Nat := 4983230072969 + 3 ^ 40 * 7750009 * 2
def baseEnd_7750009 : Nat := 3979479693670673787845863

theorem tailTrace_7750009 : CollatzResearch.WordTrace tailWord_7750009 prefixEnd_7750009 3979479693670673787845863 := by
  unfold tailWord_7750009
  simp only [CollatzResearch.WordTrace]
  refine ⟨282666050180048464005437081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188444033453365642670291387 282666050180048464005437081)
  ·
    refine ⟨211999537635036348004077811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282666050180048464005437081 211999537635036348004077811)
    ·
      refine ⟨317999306452554522006116717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211999537635036348004077811 317999306452554522006116717)
      ·
        refine ⟨119249739919707945752293769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317999306452554522006116717 119249739919707945752293769)
        ·
          refine ⟨89437304939780959314220327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119249739919707945752293769 89437304939780959314220327)
          ·
            refine ⟨134155957409671438971330491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89437304939780959314220327 134155957409671438971330491)
            ·
              refine ⟨201233936114507158456995737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134155957409671438971330491 201233936114507158456995737)
              ·
                refine ⟨150925452085880368842746803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201233936114507158456995737 150925452085880368842746803)
                ·
                  refine ⟨226388178128820553264120205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150925452085880368842746803 226388178128820553264120205)
                  ·
                    refine ⟨84895566798307707474045077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 226388178128820553264120205 84895566798307707474045077)
                    ·
                      refine ⟨3979479693670673787845863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84895566798307707474045077 3979479693670673787845863)
                      ·
                        rfl

theorem cell23_7750009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_7750009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750009 prefixEnd_7750009 := by exact prefixLift 7750009
  have htrace : WordTrace (prefixWord ++ tailWord_7750009) baseStart_7750009 baseEnd_7750009 := by
    simpa [prefixWord, tailWord_7750009, baseEnd_7750009] using wordTrace_append hprefix tailTrace_7750009
  have hstable : (prefixWord ++ tailWord_7750009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750009).length < 2 ^ (prefixWord ++ tailWord_7750009).sum := by decide
  have hdescent : baseEnd_7750009 < baseStart_7750009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750013 : List Nat := [1, 4, 1, 1, 2, 4, 2, 1, 2, 1, 4]
def baseStart_7750013 : Nat := 118140960795 + 7750013 * 2 ^ 59
def prefixEnd_7750013 : Nat := 4983230072969 + 3 ^ 40 * 7750013 * 2
def baseEnd_7750013 : Nat := 3979481747593291772195845

theorem tailTrace_7750013 : CollatzResearch.WordTrace tailWord_7750013 prefixEnd_7750013 3979481747593291772195845 := by
  unfold tailWord_7750013
  simp only [CollatzResearch.WordTrace]
  refine ⟨282666196072033972688582693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188444130714689315125721795 282666196072033972688582693)
  ·
    refine ⟨52999911763506369879109255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282666196072033972688582693 52999911763506369879109255)
    ·
      refine ⟨79499867645259554818663883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52999911763506369879109255 79499867645259554818663883)
      ·
        refine ⟨119249801467889332227995825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79499867645259554818663883 119249801467889332227995825)
        ·
          refine ⟨89437351100916999170996869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119249801467889332227995825 89437351100916999170996869)
          ·
            refine ⟨16769503331421937344561913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89437351100916999170996869 16769503331421937344561913)
            ·
              refine ⟨12577127498566453008421435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16769503331421937344561913 12577127498566453008421435)
              ·
                refine ⟨18865691247849679512632153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12577127498566453008421435 18865691247849679512632153)
                ·
                  refine ⟨14149268435887259634474115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18865691247849679512632153 14149268435887259634474115)
                  ·
                    refine ⟨21223902653830889451711173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14149268435887259634474115 21223902653830889451711173)
                    ·
                      refine ⟨3979481747593291772195845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21223902653830889451711173 3979481747593291772195845)
                      ·
                        rfl

theorem cell23_7750013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_7750013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750013 prefixEnd_7750013 := by exact prefixLift 7750013
  have htrace : WordTrace (prefixWord ++ tailWord_7750013) baseStart_7750013 baseEnd_7750013 := by
    simpa [prefixWord, tailWord_7750013, baseEnd_7750013] using wordTrace_append hprefix tailTrace_7750013
  have hstable : (prefixWord ++ tailWord_7750013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750013).length < 2 ^ (prefixWord ++ tailWord_7750013).sum := by decide
  have hdescent : baseEnd_7750013 < baseStart_7750013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750066 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 3, 5]
def baseStart_7750066 : Nat := 118140960795 + 7750066 * 2 ^ 59
def prefixEnd_7750066 : Nat := 4983230072969 + 3 ^ 40 * 7750066 * 2
def baseEnd_7750066 : Nat := 1326502987355993354944367

theorem tailTrace_7750066 : CollatzResearch.WordTrace tailWord_7750066 prefixEnd_7750066 1326502987355993354944367 := by
  unfold tailWord_7750066
  simp only [CollatzResearch.WordTrace]
  refine ⟨70667032285210490685065513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188445419427227975160174701 70667032285210490685065513)
  ·
    refine ⟨53000274213907868013799135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70667032285210490685065513 53000274213907868013799135)
    ·
      refine ⟨79500411320861802020698703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53000274213907868013799135 79500411320861802020698703)
      ·
        refine ⟨119250616981292703031048055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79500411320861802020698703 119250616981292703031048055)
        ·
          refine ⟨178875925471939054546572083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119250616981292703031048055 178875925471939054546572083)
          ·
            refine ⟨268313888207908581819858125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178875925471939054546572083 268313888207908581819858125)
            ·
              refine ⟨100617708077965718182446797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268313888207908581819858125 100617708077965718182446797)
              ·
                refine ⟨37731640529237144318417549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100617708077965718182446797 37731640529237144318417549)
                ·
                  refine ⟨14149365198463929119406581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37731640529237144318417549 14149365198463929119406581)
                  ·
                    refine ⟨1326502987355993354944367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14149365198463929119406581 1326502987355993354944367)
                    ·
                      rfl

theorem cell23_7750066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_7750066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750066 prefixEnd_7750066 := by exact prefixLift 7750066
  have htrace : WordTrace (prefixWord ++ tailWord_7750066) baseStart_7750066 baseEnd_7750066 := by
    simpa [prefixWord, tailWord_7750066, baseEnd_7750066] using wordTrace_append hprefix tailTrace_7750066
  have hstable : (prefixWord ++ tailWord_7750066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750066).length < 2 ^ (prefixWord ++ tailWord_7750066).sum := by decide
  have hdescent : baseEnd_7750066 < baseStart_7750066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750120 : List Nat := [2, 1, 4, 1, 1, 4, 2, 2, 1, 1, 4]
def baseStart_7750120 : Nat := 118140960795 + 7750120 * 2 ^ 59
def prefixEnd_7750120 : Nat := 4983230072969 + 3 ^ 40 * 7750120 * 2
def baseEnd_7750120 : Nat := 3979536690023322853557853

theorem tailTrace_7750120 : CollatzResearch.WordTrace tailWord_7750120 prefixEnd_7750120 3979536690023322853557853 := by
  unfold tailWord_7750120
  simp only [CollatzResearch.WordTrace]
  refine ⟨141335049341323164981363907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188446732455097553308485209 141335049341323164981363907)
  ·
    refine ⟨212002574011984747472045861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141335049341323164981363907 212002574011984747472045861)
    ·
      refine ⟨39750482627247140151008599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212002574011984747472045861 39750482627247140151008599)
      ·
        refine ⟨59625723940870710226512899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39750482627247140151008599 59625723940870710226512899)
        ·
          refine ⟨89438585911306065339769349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59625723940870710226512899 89438585911306065339769349)
          ·
            refine ⟨16769734858369887251206753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89438585911306065339769349 16769734858369887251206753)
            ·
              refine ⟨12577301143777415438405065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16769734858369887251206753 12577301143777415438405065)
              ·
                refine ⟨9432975857833061578803799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12577301143777415438405065 9432975857833061578803799)
                ·
                  refine ⟨14149463786749592368205699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9432975857833061578803799 14149463786749592368205699)
                  ·
                    refine ⟨21224195680124388552308549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14149463786749592368205699 21224195680124388552308549)
                    ·
                      refine ⟨3979536690023322853557853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21224195680124388552308549 3979536690023322853557853)
                      ·
                        rfl

theorem cell23_7750120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_7750120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750120 prefixEnd_7750120 := by exact prefixLift 7750120
  have htrace : WordTrace (prefixWord ++ tailWord_7750120) baseStart_7750120 baseEnd_7750120 := by
    simpa [prefixWord, tailWord_7750120, baseEnd_7750120] using wordTrace_append hprefix tailTrace_7750120
  have hstable : (prefixWord ++ tailWord_7750120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750120).length < 2 ^ (prefixWord ++ tailWord_7750120).sum := by decide
  have hdescent : baseEnd_7750120 < baseStart_7750120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750157 : List Nat := [1, 7, 1, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_7750157 : Nat := 118140960795 + 7750157 * 2 ^ 59
def prefixEnd_7750157 : Nat := 4983230072969 + 3 ^ 40 * 7750157 * 2
def baseEnd_7750157 : Nat := 3979555688807539208795183

theorem tailTrace_7750157 : CollatzResearch.WordTrace tailWord_7750157 prefixEnd_7750157 3979555688807539208795183 := by
  unfold tailWord_7750157
  simp only [CollatzResearch.WordTrace]
  refine ⟨282671448183512285281824725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188447632122341523521216483 282671448183512285281824725)
  ·
    refine ⟨6625112066801069186292767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 282671448183512285281824725 6625112066801069186292767)
    ·
      refine ⟨9937668100201603779439151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6625112066801069186292767 9937668100201603779439151)
      ·
        refine ⟨14906502150302405669158727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9937668100201603779439151 14906502150302405669158727)
        ·
          refine ⟨22359753225453608503738091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14906502150302405669158727 22359753225453608503738091)
          ·
            refine ⟨33539629838180412755607137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22359753225453608503738091 33539629838180412755607137)
            ·
              refine ⟨25154722378635309566705353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33539629838180412755607137 25154722378635309566705353)
              ·
                refine ⟨18866041783976482175029015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25154722378635309566705353 18866041783976482175029015)
                ·
                  refine ⟨28299062675964723262543523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18866041783976482175029015 28299062675964723262543523)
                  ·
                    refine ⟨42448594013947084893815285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28299062675964723262543523 42448594013947084893815285)
                    ·
                      refine ⟨3979555688807539208795183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42448594013947084893815285 3979555688807539208795183)
                      ·
                        rfl

theorem cell23_7750157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_7750157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750157 prefixEnd_7750157 := by exact prefixLift 7750157
  have htrace : WordTrace (prefixWord ++ tailWord_7750157) baseStart_7750157 baseEnd_7750157 := by
    simpa [prefixWord, tailWord_7750157, baseEnd_7750157] using wordTrace_append hprefix tailTrace_7750157
  have hstable : (prefixWord ++ tailWord_7750157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750157).length < 2 ^ (prefixWord ++ tailWord_7750157).sum := by decide
  have hdescent : baseEnd_7750157 < baseStart_7750157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750164 : List Nat := [2, 4, 3, 1, 1, 1, 4, 1, 2, 4]
def baseStart_7750164 : Nat := 118140960795 + 7750164 * 2 ^ 59
def prefixEnd_7750164 : Nat := 4983230072969 + 3 ^ 40 * 7750164 * 2
def baseEnd_7750164 : Nat := 1326519761057373560469217

theorem tailTrace_7750164 : CollatzResearch.WordTrace tailWord_7750164 prefixEnd_7750164 1326519761057373560469217 := by
  unfold tailWord_7750164
  simp only [CollatzResearch.WordTrace]
  refine ⟨141335851747243462738664773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188447802329657950318219697 141335851747243462738664773)
  ·
    refine ⟨26500472202608149263499645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141335851747243462738664773 26500472202608149263499645)
    ·
      refine ⟨9937677075978055973812367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26500472202608149263499645 9937677075978055973812367)
      ·
        refine ⟨14906515613967083960718551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9937677075978055973812367 14906515613967083960718551)
        ·
          refine ⟨22359773420950625941077827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14906515613967083960718551 22359773420950625941077827)
          ·
            refine ⟨33539660131425938911616741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22359773420950625941077827 33539660131425938911616741)
            ·
              refine ⟨6288686274642363545928139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33539660131425938911616741 6288686274642363545928139)
              ·
                refine ⟨9433029411963545318892209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6288686274642363545928139 9433029411963545318892209)
                ·
                  refine ⟨7074772058972658989169157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9433029411963545318892209 7074772058972658989169157)
                  ·
                    refine ⟨1326519761057373560469217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7074772058972658989169157 1326519761057373560469217)
                    ·
                      rfl

theorem cell23_7750164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_7750164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750164 prefixEnd_7750164 := by exact prefixLift 7750164
  have htrace : WordTrace (prefixWord ++ tailWord_7750164) baseStart_7750164 baseEnd_7750164 := by
    simpa [prefixWord, tailWord_7750164, baseEnd_7750164] using wordTrace_append hprefix tailTrace_7750164
  have hstable : (prefixWord ++ tailWord_7750164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750164).length < 2 ^ (prefixWord ++ tailWord_7750164).sum := by decide
  have hdescent : baseEnd_7750164 < baseStart_7750164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750213 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 2, 4, 3]
def baseStart_7750213 : Nat := 118140960795 + 7750213 * 2 ^ 59
def prefixEnd_7750213 : Nat := 4983230072969 + 3 ^ 40 * 7750213 * 2
def baseEnd_7750213 : Nat := 3979584443724190989694925

theorem tailTrace_7750213 : CollatzResearch.WordTrace tailWord_7750213 prefixEnd_7750213 3979584443724190989694925 := by
  unfold tailWord_7750213
  simp only [CollatzResearch.WordTrace]
  refine ⟨282673490671309406845863293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188448993780872937897242195 282673490671309406845863293)
  ·
    refine ⟨106002559001741027567198735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282673490671309406845863293 106002559001741027567198735)
    ·
      refine ⟨159003838502611541350798103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106002559001741027567198735 159003838502611541350798103)
      ·
        refine ⟨238505757753917312026197155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159003838502611541350798103 238505757753917312026197155)
        ·
          refine ⟨357758636630875968039295733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238505757753917312026197155 357758636630875968039295733)
          ·
            refine ⟨33539872184144622003683975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 357758636630875968039295733 33539872184144622003683975)
            ·
              refine ⟨50309808276216933005525963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33539872184144622003683975 50309808276216933005525963)
              ·
                refine ⟨75464712414325399508288945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50309808276216933005525963 75464712414325399508288945)
                ·
                  refine ⟨56598534310744049631216709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75464712414325399508288945 56598534310744049631216709)
                  ·
                    refine ⟨10612225183264509305853133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56598534310744049631216709 10612225183264509305853133)
                    ·
                      refine ⟨3979584443724190989694925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10612225183264509305853133 3979584443724190989694925)
                      ·
                        rfl

theorem cell23_7750213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 4, 3].length) (baseStart_7750213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750213 prefixEnd_7750213 := by exact prefixLift 7750213
  have htrace : WordTrace (prefixWord ++ tailWord_7750213) baseStart_7750213 baseEnd_7750213 := by
    simpa [prefixWord, tailWord_7750213, baseEnd_7750213] using wordTrace_append hprefix tailTrace_7750213
  have hstable : (prefixWord ++ tailWord_7750213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750213).length < 2 ^ (prefixWord ++ tailWord_7750213).sum := by decide
  have hdescent : baseEnd_7750213 < baseStart_7750213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750214 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2]
def baseStart_7750214 : Nat := 118140960795 + 7750214 * 2 ^ 59
def prefixEnd_7750214 : Nat := 4983230072969 + 3 ^ 40 * 7750214 * 2
def baseEnd_7750214 : Nat := 3979584957204845485782421

theorem tailTrace_7750214 : CollatzResearch.WordTrace tailWord_7750214 prefixEnd_7750214 3979584957204845485782421 := by
  unfold tailWord_7750214
  simp only [CollatzResearch.WordTrace]
  refine ⟨8833547723259555750520303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 188449018096203856011099797 8833547723259555750520303)
  ·
    refine ⟨13250321584889333625780455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8833547723259555750520303 13250321584889333625780455)
    ·
      refine ⟨19875482377334000438670683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13250321584889333625780455 19875482377334000438670683)
      ·
        refine ⟨29813223566001000658006025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19875482377334000438670683 29813223566001000658006025)
        ·
          refine ⟨22359917674500750493504519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29813223566001000658006025 22359917674500750493504519)
          ·
            refine ⟨33539876511751125740256779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22359917674500750493504519 33539876511751125740256779)
            ·
              refine ⟨50309814767626688610385169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33539876511751125740256779 50309814767626688610385169)
              ·
                refine ⟨37732361075720016457788877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50309814767626688610385169 37732361075720016457788877)
                ·
                  refine ⟨14149635403395006171670829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37732361075720016457788877 14149635403395006171670829)
                  ·
                    refine ⟨5306113276273127314376561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14149635403395006171670829 5306113276273127314376561)
                    ·
                      refine ⟨3979584957204845485782421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5306113276273127314376561 3979584957204845485782421)
                      ·
                        rfl

theorem cell23_7750214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_7750214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750214 prefixEnd_7750214 := by exact prefixLift 7750214
  have htrace : WordTrace (prefixWord ++ tailWord_7750214) baseStart_7750214 baseEnd_7750214 := by
    simpa [prefixWord, tailWord_7750214, baseEnd_7750214] using wordTrace_append hprefix tailTrace_7750214
  have hstable : (prefixWord ++ tailWord_7750214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750214).length < 2 ^ (prefixWord ++ tailWord_7750214).sum := by decide
  have hdescent : baseEnd_7750214 < baseStart_7750214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750216 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 11]
def baseStart_7750216 : Nat := 118140960795 + 7750216 * 2 ^ 59
def prefixEnd_7750216 : Nat := 4983230072969 + 3 ^ 40 * 7750216 * 2
def baseEnd_7750216 : Nat := 442176220462906053106379

theorem tailTrace_7750216 : CollatzResearch.WordTrace tailWord_7750216 prefixEnd_7750216 442176220462906053106379 := by
  unfold tailWord_7750216
  simp only [CollatzResearch.WordTrace]
  refine ⟨141336800045149269179111251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188449066726865692238815001 141336800045149269179111251)
  ·
    refine ⟨212005200067723903768666877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141336800045149269179111251 212005200067723903768666877)
    ·
      refine ⟨79501950025396463913250079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212005200067723903768666877 79501950025396463913250079)
      ·
        refine ⟨119252925038094695869875119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79501950025396463913250079 119252925038094695869875119)
        ·
          refine ⟨178879387557142043804812679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119252925038094695869875119 178879387557142043804812679)
          ·
            refine ⟨268319081335713065707219019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178879387557142043804812679 268319081335713065707219019)
            ·
              refine ⟨402478622003569598560828529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268319081335713065707219019 402478622003569598560828529)
              ·
                refine ⟨301858966502677198920621397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402478622003569598560828529 301858966502677198920621397)
                ·
                  refine ⟨442176220462906053106379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 301858966502677198920621397 442176220462906053106379)
                  ·
                    rfl

theorem cell23_7750216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 11].length) (baseStart_7750216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750216 prefixEnd_7750216 := by exact prefixLift 7750216
  have htrace : WordTrace (prefixWord ++ tailWord_7750216) baseStart_7750216 baseEnd_7750216 := by
    simpa [prefixWord, tailWord_7750216, baseEnd_7750216] using wordTrace_append hprefix tailTrace_7750216
  have hstable : (prefixWord ++ tailWord_7750216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750216).length < 2 ^ (prefixWord ++ tailWord_7750216).sum := by decide
  have hdescent : baseEnd_7750216 < baseStart_7750216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750243 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 3]
def baseStart_7750243 : Nat := 118140960795 + 7750243 * 2 ^ 59
def prefixEnd_7750243 : Nat := 4983230072969 + 3 ^ 40 * 7750243 * 2
def baseEnd_7750243 : Nat := 3979599848143825872319787

theorem tailTrace_7750243 : CollatzResearch.WordTrace tailWord_7750243 prefixEnd_7750243 3979599848143825872319787 := by
  unfold tailWord_7750243
  simp only [CollatzResearch.WordTrace]
  refine ⟨282674584861200721969455383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188449723240800481312970255 282674584861200721969455383)
  ·
    refine ⟨424011877291801082954183075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282674584861200721969455383 424011877291801082954183075)
    ·
      refine ⟨636017815937701624431274613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424011877291801082954183075 636017815937701624431274613)
      ·
        refine ⟨59626670244159527290431995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 636017815937701624431274613 59626670244159527290431995)
        ·
          refine ⟨89440005366239290935647993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59626670244159527290431995 89440005366239290935647993)
          ·
            refine ⟨67080004024679468201735995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89440005366239290935647993 67080004024679468201735995)
            ·
              refine ⟨100620006037019202302603993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67080004024679468201735995 100620006037019202302603993)
              ·
                refine ⟨75465004527764401726952995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100620006037019202302603993 75465004527764401726952995)
                ·
                  refine ⟨113197506791646602590429493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75465004527764401726952995 113197506791646602590429493)
                  ·
                    refine ⟨10612266261716868992852765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113197506791646602590429493 10612266261716868992852765)
                    ·
                      refine ⟨3979599848143825872319787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10612266261716868992852765 3979599848143825872319787)
                      ·
                        rfl

theorem cell23_7750243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_7750243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750243 prefixEnd_7750243 := by exact prefixLift 7750243
  have htrace : WordTrace (prefixWord ++ tailWord_7750243) baseStart_7750243 baseEnd_7750243 := by
    simpa [prefixWord, tailWord_7750243, baseEnd_7750243] using wordTrace_append hprefix tailTrace_7750243
  have hstable : (prefixWord ++ tailWord_7750243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750243).length < 2 ^ (prefixWord ++ tailWord_7750243).sum := by decide
  have hdescent : baseEnd_7750243 < baseStart_7750243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750248 : List Nat := [2, 1, 4, 3, 3, 1, 2, 1, 1, 3, 2]
def baseStart_7750248 : Nat := 118140960795 + 7750248 * 2 ^ 59
def prefixEnd_7750248 : Nat := 4983230072969 + 3 ^ 40 * 7750248 * 2
def baseEnd_7750248 : Nat := 3979602415547098352757265

theorem tailTrace_7750248 : CollatzResearch.WordTrace tailWord_7750248 prefixEnd_7750248 3979602415547098352757265 := by
  unfold tailWord_7750248
  simp only [CollatzResearch.WordTrace]
  refine ⟨141337383613091303911693699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188449844817455071882258265 141337383613091303911693699)
  ·
    refine ⟨212006075419636955867540549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141337383613091303911693699 212006075419636955867540549)
    ·
      refine ⟨39751139141181929225163853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212006075419636955867540549 39751139141181929225163853)
      ·
        refine ⟨14906677177943223459436445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39751139141181929225163853 14906677177943223459436445)
        ·
          refine ⟨5590003941728708797288667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14906677177943223459436445 5590003941728708797288667)
          ·
            refine ⟨8385005912593063195933001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5590003941728708797288667 8385005912593063195933001)
            ·
              refine ⟨6288754434444797396949751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8385005912593063195933001 6288754434444797396949751)
              ·
                refine ⟨9433131651667196095424627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6288754434444797396949751 9433131651667196095424627)
                ·
                  refine ⟨14149697477500794143136941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9433131651667196095424627 14149697477500794143136941)
                  ·
                    refine ⟨5306136554062797803676353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14149697477500794143136941 5306136554062797803676353)
                    ·
                      refine ⟨3979602415547098352757265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5306136554062797803676353 3979602415547098352757265)
                      ·
                        rfl

theorem cell23_7750248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_7750248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750248 prefixEnd_7750248 := by exact prefixLift 7750248
  have htrace : WordTrace (prefixWord ++ tailWord_7750248) baseStart_7750248 baseEnd_7750248 := by
    simpa [prefixWord, tailWord_7750248, baseEnd_7750248] using wordTrace_append hprefix tailTrace_7750248
  have hstable : (prefixWord ++ tailWord_7750248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750248).length < 2 ^ (prefixWord ++ tailWord_7750248).sum := by decide
  have hdescent : baseEnd_7750248 < baseStart_7750248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750263 : List Nat := [1, 1, 3, 1, 1, 3, 2, 4, 2, 5]
def baseStart_7750263 : Nat := 118140960795 + 7750263 * 2 ^ 59
def prefixEnd_7750263 : Nat := 4983230072969 + 3 ^ 40 * 7750263 * 2
def baseEnd_7750263 : Nat := 1326536705918971931356565

theorem tailTrace_7750263 : CollatzResearch.WordTrace tailWord_7750263 prefixEnd_7750263 1326536705918971931356565 := by
  unfold tailWord_7750263
  simp only [CollatzResearch.WordTrace]
  refine ⟨282675314321128265385183443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188450209547418843590122295 282675314321128265385183443)
  ·
    refine ⟨424012971481692398077775165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282675314321128265385183443 424012971481692398077775165)
    ·
      refine ⟨159004864305634649279165687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424012971481692398077775165 159004864305634649279165687)
      ·
        refine ⟨238507296458451973918748531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159004864305634649279165687 238507296458451973918748531)
        ·
          refine ⟨357760944687677960878122797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238507296458451973918748531 357760944687677960878122797)
          ·
            refine ⟨134160354257879235329296049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357760944687677960878122797 134160354257879235329296049)
            ·
              refine ⟨100620265693409426496972037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134160354257879235329296049 100620265693409426496972037)
              ·
                refine ⟨18866299817514267468182257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100620265693409426496972037 18866299817514267468182257)
                ·
                  refine ⟨14149724863135700601136693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18866299817514267468182257 14149724863135700601136693)
                  ·
                    refine ⟨1326536705918971931356565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14149724863135700601136693 1326536705918971931356565)
                    ·
                      rfl

theorem cell23_7750263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_7750263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750263 prefixEnd_7750263 := by exact prefixLift 7750263
  have htrace : WordTrace (prefixWord ++ tailWord_7750263) baseStart_7750263 baseEnd_7750263 := by
    simpa [prefixWord, tailWord_7750263, baseEnd_7750263] using wordTrace_append hprefix tailTrace_7750263
  have hstable : (prefixWord ++ tailWord_7750263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750263).length < 2 ^ (prefixWord ++ tailWord_7750263).sum := by decide
  have hdescent : baseEnd_7750263 < baseStart_7750263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750273 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_7750273 : Nat := 118140960795 + 7750273 * 2 ^ 59
def prefixEnd_7750273 : Nat := 4983230072969 + 3 ^ 40 * 7750273 * 2
def baseEnd_7750273 : Nat := 3979615252563460754944649

theorem tailTrace_7750273 : CollatzResearch.WordTrace tailWord_7750273 prefixEnd_7750273 3979615252563460754944649 := by
  unfold tailWord_7750273
  simp only [CollatzResearch.WordTrace]
  refine ⟨282675679051092037093047473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188450452700728024728698315 282675679051092037093047473)
  ·
    refine ⟨212006759288319027819785605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282675679051092037093047473 212006759288319027819785605)
    ·
      refine ⟨39751267366559817716209801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212006759288319027819785605 39751267366559817716209801)
      ·
        refine ⟨29813450524919863287157351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39751267366559817716209801 29813450524919863287157351)
        ·
          refine ⟨44720175787379794930736027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29813450524919863287157351 44720175787379794930736027)
          ·
            refine ⟨67080263681069692396104041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44720175787379794930736027 67080263681069692396104041)
            ·
              refine ⟨50310197760802269297078031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67080263681069692396104041 50310197760802269297078031)
              ·
                refine ⟨75465296641203403945617047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50310197760802269297078031 75465296641203403945617047)
                ·
                  refine ⟨113197944961805105918425571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75465296641203403945617047 113197944961805105918425571)
                  ·
                    refine ⟨169796917442707658877638357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113197944961805105918425571 169796917442707658877638357)
                    ·
                      refine ⟨3979615252563460754944649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169796917442707658877638357 3979615252563460754944649)
                      ·
                        rfl

theorem cell23_7750273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_7750273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750273 prefixEnd_7750273 := by exact prefixLift 7750273
  have htrace : WordTrace (prefixWord ++ tailWord_7750273) baseStart_7750273 baseEnd_7750273 := by
    simpa [prefixWord, tailWord_7750273, baseEnd_7750273] using wordTrace_append hprefix tailTrace_7750273
  have hstable : (prefixWord ++ tailWord_7750273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750273).length < 2 ^ (prefixWord ++ tailWord_7750273).sum := by decide
  have hdescent : baseEnd_7750273 < baseStart_7750273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750283 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 4]
def baseStart_7750283 : Nat := 118140960795 + 7750283 * 2 ^ 59
def prefixEnd_7750283 : Nat := 4983230072969 + 3 ^ 40 * 7750283 * 2
def baseEnd_7750283 : Nat := 3979620387370005715819603

theorem tailTrace_7750283 : CollatzResearch.WordTrace tailWord_7750283 prefixEnd_7750283 3979620387370005715819603 := by
  unfold tailWord_7750283
  simp only [CollatzResearch.WordTrace]
  refine ⟨282676043781055808800911503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188450695854037205867274335 282676043781055808800911503)
  ·
    refine ⟨424014065671583713201367255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282676043781055808800911503 424014065671583713201367255)
    ·
      refine ⟨636021098507375569802050883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424014065671583713201367255 636021098507375569802050883)
      ·
        refine ⟨954031647761063354703076325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636021098507375569802050883 954031647761063354703076325)
        ·
          refine ⟨178880933955199379006826811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 954031647761063354703076325 178880933955199379006826811)
          ·
            refine ⟨268321400932799068510240217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178880933955199379006826811 268321400932799068510240217)
            ·
              refine ⟨201241050699599301382680163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268321400932799068510240217 201241050699599301382680163)
              ·
                refine ⟨301861576049398952074020245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201241050699599301382680163 301861576049398952074020245)
                ·
                  refine ⟨14149761377315575878469699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 301861576049398952074020245 14149761377315575878469699)
                  ·
                    refine ⟨21224642065973363817704549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14149761377315575878469699 21224642065973363817704549)
                    ·
                      refine ⟨3979620387370005715819603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21224642065973363817704549 3979620387370005715819603)
                      ·
                        rfl

theorem cell23_7750283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 4].length) (baseStart_7750283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750283 prefixEnd_7750283 := by exact prefixLift 7750283
  have htrace : WordTrace (prefixWord ++ tailWord_7750283) baseStart_7750283 baseEnd_7750283 := by
    simpa [prefixWord, tailWord_7750283, baseEnd_7750283] using wordTrace_append hprefix tailTrace_7750283
  have hstable : (prefixWord ++ tailWord_7750283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750283).length < 2 ^ (prefixWord ++ tailWord_7750283).sum := by decide
  have hdescent : baseEnd_7750283 < baseStart_7750283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750300 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_7750300 : Nat := 118140960795 + 7750300 * 2 ^ 59
def prefixEnd_7750300 : Nat := 4983230072969 + 3 ^ 40 * 7750300 * 2
def baseEnd_7750300 : Nat := 3979629116541132149307025

theorem tailTrace_7750300 : CollatzResearch.WordTrace tailWord_7750300 prefixEnd_7750300 3979629116541132149307025 := by
  unfold tailWord_7750300
  simp only [CollatzResearch.WordTrace]
  refine ⟨141338331910997110352140177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188451109214662813802853569 141338331910997110352140177)
  ·
    refine ⟨106003748933247832764105133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141338331910997110352140177 106003748933247832764105133)
    ·
      refine ⟨39751405849967937286539425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106003748933247832764105133 39751405849967937286539425)
      ·
        refine ⟨29813554387475952964904569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39751405849967937286539425 29813554387475952964904569)
        ·
          refine ⟨22360165790606964723678427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29813554387475952964904569 22360165790606964723678427)
          ·
            refine ⟨33540248685910447085517641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22360165790606964723678427 33540248685910447085517641)
            ·
              refine ⟨25155186514432835314138231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33540248685910447085517641 25155186514432835314138231)
              ·
                refine ⟨37732779771649252971207347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25155186514432835314138231 37732779771649252971207347)
                ·
                  refine ⟨56599169657473879456811021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37732779771649252971207347 56599169657473879456811021)
                  ·
                    refine ⟨21224688621552704796304133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56599169657473879456811021 21224688621552704796304133)
                    ·
                      refine ⟨3979629116541132149307025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21224688621552704796304133 3979629116541132149307025)
                      ·
                        rfl

theorem cell23_7750300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_7750300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750300 prefixEnd_7750300 := by exact prefixLift 7750300
  have htrace : WordTrace (prefixWord ++ tailWord_7750300) baseStart_7750300 baseEnd_7750300 := by
    simpa [prefixWord, tailWord_7750300, baseEnd_7750300] using wordTrace_append hprefix tailTrace_7750300
  have hstable : (prefixWord ++ tailWord_7750300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750300).length < 2 ^ (prefixWord ++ tailWord_7750300).sum := by decide
  have hdescent : baseEnd_7750300 < baseStart_7750300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750314 : List Nat := [3, 1, 5, 2, 1, 1, 1, 2, 2, 5]
def baseStart_7750314 : Nat := 118140960795 + 7750314 * 2 ^ 59
def prefixEnd_7750314 : Nat := 4983230072969 + 3 ^ 40 * 7750314 * 2
def baseEnd_7750314 : Nat := 1326545435090098364843987

theorem tailTrace_7750314 : CollatzResearch.WordTrace tailWord_7750314 prefixEnd_7750314 1326545435090098364843987 := by
  unfold tailWord_7750314
  simp only [CollatzResearch.WordTrace]
  refine ⟨70669293610985875273822499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188451449629295667396859997 70669293610985875273822499)
  ·
    refine ⟨106003940416478812910733749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70669293610985875273822499 106003940416478812910733749)
    ·
      refine ⟨9937869414044888710381289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106003940416478812910733749 9937869414044888710381289)
      ·
        refine ⟨7453402060533666532785967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9937869414044888710381289 7453402060533666532785967)
        ·
          refine ⟨11180103090800499799178951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7453402060533666532785967 11180103090800499799178951)
          ·
            refine ⟨16770154636200749698768427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11180103090800499799178951 16770154636200749698768427)
            ·
              refine ⟨25155231954301124548152641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16770154636200749698768427 25155231954301124548152641)
              ·
                refine ⟨18866423965725843411114481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25155231954301124548152641 18866423965725843411114481)
                ·
                  refine ⟨14149817974294382558335861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18866423965725843411114481 14149817974294382558335861)
                  ·
                    refine ⟨1326545435090098364843987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14149817974294382558335861 1326545435090098364843987)
                    ·
                      rfl

theorem cell23_7750314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_7750314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750314 prefixEnd_7750314 := by exact prefixLift 7750314
  have htrace : WordTrace (prefixWord ++ tailWord_7750314) baseStart_7750314 baseEnd_7750314 := by
    simpa [prefixWord, tailWord_7750314, baseEnd_7750314] using wordTrace_append hprefix tailTrace_7750314
  have hstable : (prefixWord ++ tailWord_7750314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750314).length < 2 ^ (prefixWord ++ tailWord_7750314).sum := by decide
  have hdescent : baseEnd_7750314 < baseStart_7750314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750317 : List Nat := [1, 5, 2, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_7750317 : Nat := 118140960795 + 7750317 * 2 ^ 59
def prefixEnd_7750317 : Nat := 4983230072969 + 3 ^ 40 * 7750317 * 2
def baseEnd_7750317 : Nat := 3979637845712258582794447

theorem tailTrace_7750317 : CollatzResearch.WordTrace tailWord_7750317 prefixEnd_7750317 3979637845712258582794447 := by
  unfold tailWord_7750317
  simp only [CollatzResearch.WordTrace]
  refine ⟨282677283862932632607649205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188451522575288421738432803 282677283862932632607649205)
  ·
    refine ⟨26500995362149934306967113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 282677283862932632607649205 26500995362149934306967113)
    ·
      refine ⟨19875746521612450730225335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26500995362149934306967113 19875746521612450730225335)
      ·
        refine ⟨29813619782418676095338003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19875746521612450730225335 29813619782418676095338003)
        ·
          refine ⟨44720429673628014143007005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29813619782418676095338003 44720429673628014143007005)
          ·
            refine ⟨16770161127610505303627627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44720429673628014143007005 16770161127610505303627627)
            ·
              refine ⟨25155241691415757955441441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16770161127610505303627627 25155241691415757955441441)
              ·
                refine ⟨18866431268561818466581081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25155241691415757955441441 18866431268561818466581081)
                ·
                  refine ⟨14149823451421363849935811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18866431268561818466581081 14149823451421363849935811)
                  ·
                    refine ⟨21224735177132045774903717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14149823451421363849935811 21224735177132045774903717)
                    ·
                      refine ⟨3979637845712258582794447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21224735177132045774903717 3979637845712258582794447)
                      ·
                        rfl

theorem cell23_7750317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_7750317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750317 prefixEnd_7750317 := by exact prefixLift 7750317
  have htrace : WordTrace (prefixWord ++ tailWord_7750317) baseStart_7750317 baseEnd_7750317 := by
    simpa [prefixWord, tailWord_7750317, baseEnd_7750317] using wordTrace_append hprefix tailTrace_7750317
  have hstable : (prefixWord ++ tailWord_7750317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750317).length < 2 ^ (prefixWord ++ tailWord_7750317).sum := by decide
  have hdescent : baseEnd_7750317 < baseStart_7750317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750323 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 8]
def baseStart_7750323 : Nat := 118140960795 + 7750323 * 2 ^ 59
def prefixEnd_7750323 : Nat := 4983230072969 + 3 ^ 40 * 7750323 * 2
def baseEnd_7750323 : Nat := 442182325177353951035491

theorem tailTrace_7750323 : CollatzResearch.WordTrace tailWord_7750323 prefixEnd_7750323 442182325177353951035491 := by
  unfold tailWord_7750323
  simp only [CollatzResearch.WordTrace]
  refine ⟨282677502700910895632367623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188451668467273930421578415 282677502700910895632367623)
  ·
    refine ⟨424016254051366343448551435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282677502700910895632367623 424016254051366343448551435)
    ·
      refine ⟨636024381077049515172827153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424016254051366343448551435 636024381077049515172827153)
      ·
        refine ⟨477018285807787136379620365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 636024381077049515172827153 477018285807787136379620365)
        ·
          refine ⟨178881857177920176142357637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 477018285807787136379620365 178881857177920176142357637)
          ·
            refine ⟨33540348220860033026692057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178881857177920176142357637 33540348220860033026692057)
            ·
              refine ⟨25155261165645024770019043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33540348220860033026692057 25155261165645024770019043)
              ·
                refine ⟨37732891748467537155028565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25155261165645024770019043 37732891748467537155028565)
                ·
                  refine ⟨442182325177353951035491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37732891748467537155028565 442182325177353951035491)
                  ·
                    rfl

theorem cell23_7750323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 8].length) (baseStart_7750323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750323 prefixEnd_7750323 := by exact prefixLift 7750323
  have htrace : WordTrace (prefixWord ++ tailWord_7750323) baseStart_7750323 baseEnd_7750323 := by
    simpa [prefixWord, tailWord_7750323, baseEnd_7750323] using wordTrace_append hprefix tailTrace_7750323
  have hstable : (prefixWord ++ tailWord_7750323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750323).length < 2 ^ (prefixWord ++ tailWord_7750323).sum := by decide
  have hdescent : baseEnd_7750323 < baseStart_7750323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750354 : List Nat := [3, 2, 2, 2, 3, 1, 2, 1, 2, 2, 3]
def baseStart_7750354 : Nat := 118140960795 + 7750354 * 2 ^ 59
def prefixEnd_7750354 : Nat := 4983230072969 + 3 ^ 40 * 7750354 * 2
def baseEnd_7750354 : Nat := 3979656844496474938031777

theorem tailTrace_7750354 : CollatzResearch.WordTrace tailWord_7750354 prefixEnd_7750354 3979656844496474938031777 := by
  unfold tailWord_7750354
  simp only [CollatzResearch.WordTrace]
  refine ⟨70669658340949646981686529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188452422242532391951164077 70669658340949646981686529)
  ·
    refine ⟨53002243755712235236264897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70669658340949646981686529 53002243755712235236264897)
    ·
      refine ⟨39751682816784176427198673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53002243755712235236264897 39751682816784176427198673)
      ·
        refine ⟨29813762112588132320399005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39751682816784176427198673 29813762112588132320399005)
        ·
          refine ⟨11180160792220549620149627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29813762112588132320399005 11180160792220549620149627)
          ·
            refine ⟨16770241188330824430224441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11180160792220549620149627 16770241188330824430224441)
            ·
              refine ⟨12577680891248118322668331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16770241188330824430224441 12577680891248118322668331)
              ·
                refine ⟨18866521336872177484002497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12577680891248118322668331 18866521336872177484002497)
                ·
                  refine ⟨14149891002654133113001873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18866521336872177484002497 14149891002654133113001873)
                  ·
                    refine ⟨10612418251990599834751405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14149891002654133113001873 10612418251990599834751405)
                    ·
                      refine ⟨3979656844496474938031777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10612418251990599834751405 3979656844496474938031777)
                      ·
                        rfl

theorem cell23_7750354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_7750354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750354 prefixEnd_7750354 := by exact prefixLift 7750354
  have htrace : WordTrace (prefixWord ++ tailWord_7750354) baseStart_7750354 baseEnd_7750354 := by
    simpa [prefixWord, tailWord_7750354, baseEnd_7750354] using wordTrace_append hprefix tailTrace_7750354
  have hstable : (prefixWord ++ tailWord_7750354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750354).length < 2 ^ (prefixWord ++ tailWord_7750354).sum := by decide
  have hdescent : baseEnd_7750354 < baseStart_7750354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750377 : List Nat := [1, 2, 1, 1, 1, 2, 6, 2, 2, 3, 2]
def baseStart_7750377 : Nat := 118140960795 + 7750377 * 2 ^ 59
def prefixEnd_7750377 : Nat := 4983230072969 + 3 ^ 40 * 7750377 * 2
def baseEnd_7750377 : Nat := 3979668654551528348044171

theorem tailTrace_7750377 : CollatzResearch.WordTrace tailWord_7750377 prefixEnd_7750377 3979668654551528348044171 := by
  unfold tailWord_7750377
  simp only [CollatzResearch.WordTrace]
  refine ⟨282679472242715262854833385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188452981495143508569888923 282679472242715262854833385)
  ·
    refine ⟨212009604182036447141125039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282679472242715262854833385 212009604182036447141125039)
    ·
      refine ⟨318014406273054670711687559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212009604182036447141125039 318014406273054670711687559)
      ·
        refine ⟨477021609409582006067531339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318014406273054670711687559 477021609409582006067531339)
        ·
          refine ⟨715532414114373009101297009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477021609409582006067531339 715532414114373009101297009)
          ·
            refine ⟨536649310585779756825972757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 715532414114373009101297009 536649310585779756825972757)
            ·
              refine ⟨25155436433708426101217473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 536649310585779756825972757 25155436433708426101217473)
              ·
                refine ⟨18866577325281319575913105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25155436433708426101217473 18866577325281319575913105)
                ·
                  refine ⟨14149932993960989681934829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18866577325281319575913105 14149932993960989681934829)
                  ·
                    refine ⟨5306224872735371130725561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14149932993960989681934829 5306224872735371130725561)
                    ·
                      refine ⟨3979668654551528348044171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5306224872735371130725561 3979668654551528348044171)
                      ·
                        rfl

theorem cell23_7750377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 3, 2].length) (baseStart_7750377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750377 prefixEnd_7750377 := by exact prefixLift 7750377
  have htrace : WordTrace (prefixWord ++ tailWord_7750377) baseStart_7750377 baseEnd_7750377 := by
    simpa [prefixWord, tailWord_7750377, baseEnd_7750377] using wordTrace_append hprefix tailTrace_7750377
  have hstable : (prefixWord ++ tailWord_7750377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750377).length < 2 ^ (prefixWord ++ tailWord_7750377).sum := by decide
  have hdescent : baseEnd_7750377 < baseStart_7750377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750384 : List Nat := [2, 1, 1, 1, 3, 1, 5, 4, 1, 1, 3]
def baseStart_7750384 : Nat := 118140960795 + 7750384 * 2 ^ 59
def prefixEnd_7750384 : Nat := 4983230072969 + 3 ^ 40 * 7750384 * 2
def baseEnd_7750384 : Nat := 3979672248916109820656639

theorem tailTrace_7750384 : CollatzResearch.WordTrace tailWord_7750384 prefixEnd_7750384 3979672248916109820656639 := by
  unfold tailWord_7750384
  simp only [CollatzResearch.WordTrace]
  refine ⟨141339863776844951525169103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188453151702459935366892137 141339863776844951525169103)
  ·
    refine ⟨212009795665267427287753655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141339863776844951525169103 212009795665267427287753655)
    ·
      refine ⟨318014693497901140931630483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212009795665267427287753655 318014693497901140931630483)
      ·
        refine ⟨477022040246851711397445725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318014693497901140931630483 477022040246851711397445725)
        ·
          refine ⟨178883265092569391774042147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 477022040246851711397445725 178883265092569391774042147)
          ·
            refine ⟨268324897638854087661063221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178883265092569391774042147 268324897638854087661063221)
            ·
              refine ⟨25155459153642570718224677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 268324897638854087661063221 25155459153642570718224677)
              ·
                refine ⟨4716648591307982009667127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25155459153642570718224677 4716648591307982009667127)
                ·
                  refine ⟨7074972886961973014500691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4716648591307982009667127 7074972886961973014500691)
                  ·
                    refine ⟨10612459330442959521751037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7074972886961973014500691 10612459330442959521751037)
                    ·
                      refine ⟨3979672248916109820656639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10612459330442959521751037 3979672248916109820656639)
                      ·
                        rfl

theorem cell23_7750384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 1, 1, 3].length) (baseStart_7750384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750384 prefixEnd_7750384 := by exact prefixLift 7750384
  have htrace : WordTrace (prefixWord ++ tailWord_7750384) baseStart_7750384 baseEnd_7750384 := by
    simpa [prefixWord, tailWord_7750384, baseEnd_7750384] using wordTrace_append hprefix tailTrace_7750384
  have hstable : (prefixWord ++ tailWord_7750384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750384).length < 2 ^ (prefixWord ++ tailWord_7750384).sum := by decide
  have hdescent : baseEnd_7750384 < baseStart_7750384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750407 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 4]
def baseStart_7750407 : Nat := 118140960795 + 7750407 * 2 ^ 59
def prefixEnd_7750407 : Nat := 4983230072969 + 3 ^ 40 * 7750407 * 2
def baseEnd_7750407 : Nat := 3979684058971163230669033

theorem tailTrace_7750407 : CollatzResearch.WordTrace tailWord_7750407 prefixEnd_7750407 3979684058971163230669033 := by
  unfold tailWord_7750407
  simp only [CollatzResearch.WordTrace]
  refine ⟨282680566432606577978425475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188453710955071051985616983 282680566432606577978425475)
  ·
    refine ⟨424020849648909866967638213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282680566432606577978425475 424020849648909866967638213)
    ·
      refine ⟨79503909309170600056432165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 424020849648909866967638213 79503909309170600056432165)
      ·
        refine ⟨14906982995469487510581031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79503909309170600056432165 14906982995469487510581031)
        ·
          refine ⟨22360474493204231265871547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14906982995469487510581031 22360474493204231265871547)
          ·
            refine ⟨33540711739806346898807321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22360474493204231265871547 33540711739806346898807321)
            ·
              refine ⟨25155533804854760174105491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33540711739806346898807321 25155533804854760174105491)
              ·
                refine ⟨37733300707282140261158237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25155533804854760174105491 37733300707282140261158237)
                ·
                  refine ⟨14149987765230802597934339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37733300707282140261158237 14149987765230802597934339)
                  ·
                    refine ⟨21224981647846203896901509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14149987765230802597934339 21224981647846203896901509)
                    ·
                      refine ⟨3979684058971163230669033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21224981647846203896901509 3979684058971163230669033)
                      ·
                        rfl

theorem cell23_7750407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_7750407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750407 prefixEnd_7750407 := by exact prefixLift 7750407
  have htrace : WordTrace (prefixWord ++ tailWord_7750407) baseStart_7750407 baseEnd_7750407 := by
    simpa [prefixWord, tailWord_7750407, baseEnd_7750407] using wordTrace_append hprefix tailTrace_7750407
  have hstable : (prefixWord ++ tailWord_7750407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750407).length < 2 ^ (prefixWord ++ tailWord_7750407).sum := by decide
  have hdescent : baseEnd_7750407 < baseStart_7750407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750434 : List Nat := [3, 3, 1, 1, 2, 2, 3, 2, 2, 4]
def baseStart_7750434 : Nat := 118140960795 + 7750434 * 2 ^ 59
def prefixEnd_7750434 : Nat := 4983230072969 + 3 ^ 40 * 7750434 * 2
def baseEnd_7750434 : Nat := 1326565974316278208343803

theorem tailTrace_7750434 : CollatzResearch.WordTrace tailWord_7750434 prefixEnd_7750434 1326565974316278208343803 := by
  unfold tailWord_7750434
  simp only [CollatzResearch.WordTrace]
  refine ⟨70670387800877190397414589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188454367469005841059772237 70670387800877190397414589)
  ·
    refine ⟨26501395425328946399030471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70670387800877190397414589 26501395425328946399030471)
    ·
      refine ⟨39752093137993419598545707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26501395425328946399030471 39752093137993419598545707)
      ·
        refine ⟨59628139706990129397818561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39752093137993419598545707 59628139706990129397818561)
        ·
          refine ⟨44721104780242597048363921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59628139706990129397818561 44721104780242597048363921)
          ·
            refine ⟨33540828585181947786272941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44721104780242597048363921 33540828585181947786272941)
            ·
              refine ⟨12577810719443230419852353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33540828585181947786272941 12577810719443230419852353)
              ·
                refine ⟨9433358039582422814889265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12577810719443230419852353 9433358039582422814889265)
                ·
                  refine ⟨7075018529686817111166949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9433358039582422814889265 7075018529686817111166949)
                  ·
                    refine ⟨1326565974316278208343803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7075018529686817111166949 1326565974316278208343803)
                    ·
                      rfl

theorem cell23_7750434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_7750434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750434 prefixEnd_7750434 := by exact prefixLift 7750434
  have htrace : WordTrace (prefixWord ++ tailWord_7750434) baseStart_7750434 baseEnd_7750434 := by
    simpa [prefixWord, tailWord_7750434, baseEnd_7750434] using wordTrace_append hprefix tailTrace_7750434
  have hstable : (prefixWord ++ tailWord_7750434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750434).length < 2 ^ (prefixWord ++ tailWord_7750434).sum := by decide
  have hdescent : baseEnd_7750434 < baseStart_7750434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750454 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_7750454 : Nat := 118140960795 + 7750454 * 2 ^ 59
def prefixEnd_7750454 : Nat := 4983230072969 + 3 ^ 40 * 7750454 * 2
def baseEnd_7750454 : Nat := 3979708192561924546781317

theorem tailTrace_7750454 : CollatzResearch.WordTrace tailWord_7750454 prefixEnd_7750454 3979708192561924546781317 := by
  unfold tailWord_7750454
  simp only [CollatzResearch.WordTrace]
  refine ⟨17667642541464769062836651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188454853775624203336924277 17667642541464769062836651)
  ·
    refine ⟨26501463812197153594254977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17667642541464769062836651 26501463812197153594254977)
    ·
      refine ⟨19876097859147865195691233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26501463812197153594254977 19876097859147865195691233)
      ·
        refine ⟨14907073394360898896768425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19876097859147865195691233 14907073394360898896768425)
        ·
          refine ⟨11180305045770674172576319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14907073394360898896768425 11180305045770674172576319)
          ·
            refine ⟨16770457568656011258864479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11180305045770674172576319 16770457568656011258864479)
            ·
              refine ⟨25155686352984016888296719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16770457568656011258864479 25155686352984016888296719)
              ·
                refine ⟨37733529529476025332445079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25155686352984016888296719 37733529529476025332445079)
                ·
                  refine ⟨56600294294214037998667619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37733529529476025332445079 56600294294214037998667619)
                  ·
                    refine ⟨84900441441321056998001429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56600294294214037998667619 84900441441321056998001429)
                    ·
                      refine ⟨3979708192561924546781317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84900441441321056998001429 3979708192561924546781317)
                      ·
                        rfl

theorem cell23_7750454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_7750454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750454 prefixEnd_7750454 := by exact prefixLift 7750454
  have htrace : WordTrace (prefixWord ++ tailWord_7750454) baseStart_7750454 baseEnd_7750454 := by
    simpa [prefixWord, tailWord_7750454, baseEnd_7750454] using wordTrace_append hprefix tailTrace_7750454
  have hstable : (prefixWord ++ tailWord_7750454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750454).length < 2 ^ (prefixWord ++ tailWord_7750454).sum := by decide
  have hdescent : baseEnd_7750454 < baseStart_7750454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750461 : List Nat := [1, 4, 1, 4, 2, 1, 2, 2, 1, 2, 3]
def baseStart_7750461 : Nat := 118140960795 + 7750461 * 2 ^ 59
def prefixEnd_7750461 : Nat := 4983230072969 + 3 ^ 40 * 7750461 * 2
def baseEnd_7750461 : Nat := 3979711786926506019393785

theorem tailTrace_7750461 : CollatzResearch.WordTrace tailWord_7750461 prefixEnd_7750461 3979711786926506019393785 := by
  unfold tailWord_7750461
  simp only [CollatzResearch.WordTrace]
  refine ⟨282682535974410945200891237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188455023982940630133927491 282682535974410945200891237)
  ·
    refine ⟨53002975495202052225167107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282682535974410945200891237 53002975495202052225167107)
    ·
      refine ⟨79504463242803078337750661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53002975495202052225167107 79504463242803078337750661)
      ·
        refine ⟨14907086858025577188328249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79504463242803078337750661 14907086858025577188328249)
        ·
          refine ⟨11180315143519182891246187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14907086858025577188328249 11180315143519182891246187)
          ·
            refine ⟨16770472715278774336869281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11180315143519182891246187 16770472715278774336869281)
            ·
              refine ⟨12577854536459080752651961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16770472715278774336869281 12577854536459080752651961)
              ·
                refine ⟨9433390902344310564488971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12577854536459080752651961 9433390902344310564488971)
                ·
                  refine ⟨14150086353516465846733457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9433390902344310564488971 14150086353516465846733457)
                  ·
                    refine ⟨10612564765137349385050093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14150086353516465846733457 10612564765137349385050093)
                    ·
                      refine ⟨3979711786926506019393785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10612564765137349385050093 3979711786926506019393785)
                      ·
                        rfl

theorem cell23_7750461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_7750461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750461 prefixEnd_7750461 := by exact prefixLift 7750461
  have htrace : WordTrace (prefixWord ++ tailWord_7750461) baseStart_7750461 baseEnd_7750461 := by
    simpa [prefixWord, tailWord_7750461, baseEnd_7750461] using wordTrace_append hprefix tailTrace_7750461
  have hstable : (prefixWord ++ tailWord_7750461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750461).length < 2 ^ (prefixWord ++ tailWord_7750461).sum := by decide
  have hdescent : baseEnd_7750461 < baseStart_7750461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750497 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 5, 4, 2]
def baseStart_7750497 : Nat := 118140960795 + 7750497 * 2 ^ 59
def prefixEnd_7750497 : Nat := 4983230072969 + 3 ^ 40 * 7750497 * 2
def baseEnd_7750497 : Nat := 3979730272230067878543619

theorem tailTrace_7750497 : CollatzResearch.WordTrace tailWord_7750497 prefixEnd_7750497 3979730272230067878543619 := by
  unfold tailWord_7750497
  simp only [CollatzResearch.WordTrace]
  refine ⟨282683849002280523349201745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188455899334853682232801163 282683849002280523349201745)
  ·
    refine ⟨212012886751710392511901309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282683849002280523349201745 212012886751710392511901309)
    ·
      refine ⟨79504832531891397191962991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212012886751710392511901309 79504832531891397191962991)
      ·
        refine ⟨119257248797837095787944487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79504832531891397191962991 119257248797837095787944487)
        ·
          refine ⟨178885873196755643681916731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119257248797837095787944487 178885873196755643681916731)
          ·
            refine ⟨268328809795133465522875097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178885873196755643681916731 268328809795133465522875097)
            ·
              refine ⟨201246607346350099142156323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268328809795133465522875097 201246607346350099142156323)
              ·
                refine ⟨301869911019525148713234485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201246607346350099142156323 301869911019525148713234485)
                ·
                  refine ⟨28300304158080482691865733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 301869911019525148713234485 28300304158080482691865733)
                  ·
                    refine ⟨5306307029640090504724825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28300304158080482691865733 5306307029640090504724825)
                    ·
                      refine ⟨3979730272230067878543619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5306307029640090504724825 3979730272230067878543619)
                      ·
                        rfl

theorem cell23_7750497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 4, 2].length) (baseStart_7750497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750497 prefixEnd_7750497 := by exact prefixLift 7750497
  have htrace : WordTrace (prefixWord ++ tailWord_7750497) baseStart_7750497 baseEnd_7750497 := by
    simpa [prefixWord, tailWord_7750497, baseEnd_7750497] using wordTrace_append hprefix tailTrace_7750497
  have hstable : (prefixWord ++ tailWord_7750497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750497).length < 2 ^ (prefixWord ++ tailWord_7750497).sum := by decide
  have hdescent : baseEnd_7750497 < baseStart_7750497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750517 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_7750517 : Nat := 118140960795 + 7750517 * 2 ^ 59
def prefixEnd_7750517 : Nat := 4983230072969 + 3 ^ 40 * 7750517 * 2
def baseEnd_7750517 : Nat := 3979740541843157800293527

theorem tailTrace_7750517 : CollatzResearch.WordTrace tailWord_7750517 prefixEnd_7750517 3979740541843157800293527 := by
  unfold tailWord_7750517
  simp only [CollatzResearch.WordTrace]
  refine ⟨282684578462208066764929805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188456385641472044509953203 282684578462208066764929805)
  ·
    refine ⟨106006716923328025036848677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282684578462208066764929805 106006716923328025036848677)
    ·
      refine ⟨19876259423124004694409127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106006716923328025036848677 19876259423124004694409127)
      ·
        refine ⟨29814389134686007041613691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19876259423124004694409127 29814389134686007041613691)
        ·
          refine ⟨44721583702029010562420537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29814389134686007041613691 44721583702029010562420537)
          ·
            refine ⟨33541187776521757921815403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44721583702029010562420537 33541187776521757921815403)
            ·
              refine ⟨50311781664782636882723105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33541187776521757921815403 50311781664782636882723105)
              ·
                refine ⟨37733836248586977662042329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50311781664782636882723105 37733836248586977662042329)
                ·
                  refine ⟨28300377186440233246531747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37733836248586977662042329 28300377186440233246531747)
                  ·
                    refine ⟨42450565779660349869797621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28300377186440233246531747 42450565779660349869797621)
                    ·
                      refine ⟨3979740541843157800293527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42450565779660349869797621 3979740541843157800293527)
                      ·
                        rfl

theorem cell23_7750517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_7750517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750517 prefixEnd_7750517 := by exact prefixLift 7750517
  have htrace : WordTrace (prefixWord ++ tailWord_7750517) baseStart_7750517 baseEnd_7750517 := by
    simpa [prefixWord, tailWord_7750517, baseEnd_7750517] using wordTrace_append hprefix tailTrace_7750517
  have hstable : (prefixWord ++ tailWord_7750517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750517).length < 2 ^ (prefixWord ++ tailWord_7750517).sum := by decide
  have hdescent : baseEnd_7750517 < baseStart_7750517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750518 : List Nat := [5, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2]
def baseStart_7750518 : Nat := 118140960795 + 7750518 * 2 ^ 59
def prefixEnd_7750518 : Nat := 4983230072969 + 3 ^ 40 * 7750518 * 2
def baseEnd_7750518 : Nat := 3979741055323812296381023

theorem tailTrace_7750518 : CollatzResearch.WordTrace tailWord_7750518 prefixEnd_7750518 3979741055323812296381023 := by
  unfold tailWord_7750518
  simp only [CollatzResearch.WordTrace]
  refine ⟨17667788433450277745982263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188456409956802962623810805 17667788433450277745982263)
  ·
    refine ⟨26501682650175416618973395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17667788433450277745982263 26501682650175416618973395)
    ·
      refine ⟨39752523975263124928460093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26501682650175416618973395 39752523975263124928460093)
      ·
        refine ⟨14907196490723671848172535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39752523975263124928460093 14907196490723671848172535)
        ·
          refine ⟨22360794736085507772258803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14907196490723671848172535 22360794736085507772258803)
          ·
            refine ⟨33541192104128261658388205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22360794736085507772258803 33541192104128261658388205)
            ·
              refine ⟨12577947039048098121895577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33541192104128261658388205 12577947039048098121895577)
              ·
                refine ⟨9433460279286073591421683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12577947039048098121895577 9433460279286073591421683)
                ·
                  refine ⟨14150190418929110387132525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9433460279286073591421683 14150190418929110387132525)
                  ·
                    refine ⟨5306321407098416395174697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14150190418929110387132525 5306321407098416395174697)
                    ·
                      refine ⟨3979741055323812296381023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5306321407098416395174697 3979741055323812296381023)
                      ·
                        rfl

theorem cell23_7750518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_7750518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750518 prefixEnd_7750518 := by exact prefixLift 7750518
  have htrace : WordTrace (prefixWord ++ tailWord_7750518) baseStart_7750518 baseEnd_7750518 := by
    simpa [prefixWord, tailWord_7750518, baseEnd_7750518] using wordTrace_append hprefix tailTrace_7750518
  have hstable : (prefixWord ++ tailWord_7750518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750518).length < 2 ^ (prefixWord ++ tailWord_7750518).sum := by decide
  have hdescent : baseEnd_7750518 < baseStart_7750518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750548 : List Nat := [2, 4, 2, 1, 1, 1, 4, 2, 2, 2, 2]
def baseStart_7750548 : Nat := 118140960795 + 7750548 * 2 ^ 59
def prefixEnd_7750548 : Nat := 4983230072969 + 3 ^ 40 * 7750548 * 2
def baseEnd_7750548 : Nat := 3979756459743447179005885

theorem tailTrace_7750548 : CollatzResearch.WordTrace tailWord_7750548 prefixEnd_7750548 3979756459743447179005885 := by
  unfold tailWord_7750548
  simp only [CollatzResearch.WordTrace]
  refine ⟨141342854562547879529654149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188457139416730506039538865 141342854562547879529654149)
  ·
    refine ⟨26501785230477727411810153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141342854562547879529654149 26501785230477727411810153)
    ·
      refine ⟨19876338922858295558857615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26501785230477727411810153 19876338922858295558857615)
      ·
        refine ⟨29814508384287443338286423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19876338922858295558857615 29814508384287443338286423)
        ·
          refine ⟨44721762576431165007429635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29814508384287443338286423 44721762576431165007429635)
          ·
            refine ⟨67082643864646747511144453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44721762576431165007429635 67082643864646747511144453)
            ·
              refine ⟨12577995724621265158339585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67082643864646747511144453 12577995724621265158339585)
              ·
                refine ⟨9433496793465948868754689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12577995724621265158339585 9433496793465948868754689)
                ·
                  refine ⟨7075122595099461651566017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9433496793465948868754689 7075122595099461651566017)
                  ·
                    refine ⟨5306341946324596238674513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7075122595099461651566017 5306341946324596238674513)
                    ·
                      refine ⟨3979756459743447179005885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5306341946324596238674513 3979756459743447179005885)
                      ·
                        rfl

theorem cell23_7750548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_7750548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750548 prefixEnd_7750548 := by exact prefixLift 7750548
  have htrace : WordTrace (prefixWord ++ tailWord_7750548) baseStart_7750548 baseEnd_7750548 := by
    simpa [prefixWord, tailWord_7750548, baseEnd_7750548] using wordTrace_append hprefix tailTrace_7750548
  have hstable : (prefixWord ++ tailWord_7750548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750548).length < 2 ^ (prefixWord ++ tailWord_7750548).sum := by decide
  have hdescent : baseEnd_7750548 < baseStart_7750548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750584 : List Nat := [2, 1, 2, 1, 2, 6, 1, 1, 2, 5]
def baseStart_7750584 : Nat := 118140960795 + 7750584 * 2 ^ 59
def prefixEnd_7750584 : Nat := 4983230072969 + 3 ^ 40 * 7750584 * 2
def baseEnd_7750584 : Nat := 1326591648349003012718573

theorem tailTrace_7750584 : CollatzResearch.WordTrace tailWord_7750584 prefixEnd_7750584 1326591648349003012718573 := by
  unfold tailWord_7750584
  simp only [CollatzResearch.WordTrace]
  refine ⟨141343511076482668603809403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188458014768643558138412537 141343511076482668603809403)
  ·
    refine ⟨212015266614724002905714105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141343511076482668603809403 212015266614724002905714105)
    ·
      refine ⟨159011449961043002179285579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212015266614724002905714105 159011449961043002179285579)
      ·
        refine ⟨238517174941564503268928369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159011449961043002179285579 238517174941564503268928369)
        ·
          refine ⟨178887881206173377451696277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238517174941564503268928369 178887881206173377451696277)
          ·
            refine ⟨8385369431539377068048263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 178887881206173377451696277 8385369431539377068048263)
            ·
              refine ⟨12578054147309065602072395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8385369431539377068048263 12578054147309065602072395)
              ·
                refine ⟨18867081220963598403108593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12578054147309065602072395 18867081220963598403108593)
                ·
                  refine ⟨14150310915722698802331445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18867081220963598403108593 14150310915722698802331445)
                  ·
                    refine ⟨1326591648349003012718573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14150310915722698802331445 1326591648349003012718573)
                    ·
                      rfl

theorem cell23_7750584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 2, 5].length) (baseStart_7750584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750584 prefixEnd_7750584 := by exact prefixLift 7750584
  have htrace : WordTrace (prefixWord ++ tailWord_7750584) baseStart_7750584 baseEnd_7750584 := by
    simpa [prefixWord, tailWord_7750584, baseEnd_7750584] using wordTrace_append hprefix tailTrace_7750584
  have hstable : (prefixWord ++ tailWord_7750584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750584).length < 2 ^ (prefixWord ++ tailWord_7750584).sum := by decide
  have hdescent : baseEnd_7750584 < baseStart_7750584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750604 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 4, 4, 2]
def baseStart_7750604 : Nat := 118140960795 + 7750604 * 2 ^ 59
def prefixEnd_7750604 : Nat := 4983230072969 + 3 ^ 40 * 7750604 * 2
def baseEnd_7750604 : Nat := 3979785214660098959905627

theorem tailTrace_7750604 : CollatzResearch.WordTrace tailWord_7750604 prefixEnd_7750604 3979785214660098959905627 := by
  unfold tailWord_7750604
  simp only [CollatzResearch.WordTrace]
  refine ⟨141343875806446440311673433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188458501075261920415564577 141343875806446440311673433)
  ·
    refine ⟨106007906854834830233755075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141343875806446440311673433 106007906854834830233755075)
    ·
      refine ⟨159011860282252245350632613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106007906854834830233755075 159011860282252245350632613)
      ·
        refine ⟨29814723802922296003243615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159011860282252245350632613 29814723802922296003243615)
        ·
          refine ⟨44722085704383444004865423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29814723802922296003243615 44722085704383444004865423)
          ·
            refine ⟨67083128556575166007298135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44722085704383444004865423 67083128556575166007298135)
            ·
              refine ⟨100624692834862749010947203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67083128556575166007298135 100624692834862749010947203)
              ·
                refine ⟨150937039252294123516420805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100624692834862749010947203 150937039252294123516420805)
                ·
                  refine ⟨28300694859805148159328901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150937039252294123516420805 28300694859805148159328901)
                  ·
                    refine ⟨5306380286213465279874169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28300694859805148159328901 5306380286213465279874169)
                    ·
                      refine ⟨3979785214660098959905627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5306380286213465279874169 3979785214660098959905627)
                      ·
                        rfl

theorem cell23_7750604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_7750604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750604 prefixEnd_7750604 := by exact prefixLift 7750604
  have htrace : WordTrace (prefixWord ++ tailWord_7750604) baseStart_7750604 baseEnd_7750604 := by
    simpa [prefixWord, tailWord_7750604, baseEnd_7750604] using wordTrace_append hprefix tailTrace_7750604
  have hstable : (prefixWord ++ tailWord_7750604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750604).length < 2 ^ (prefixWord ++ tailWord_7750604).sum := by decide
  have hdescent : baseEnd_7750604 < baseStart_7750604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750621 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 2, 4, 2]
def baseStart_7750621 : Nat := 118140960795 + 7750621 * 2 ^ 59
def prefixEnd_7750621 : Nat := 4983230072969 + 3 ^ 40 * 7750621 * 2
def baseEnd_7750621 : Nat := 3979793943831225393393049

theorem tailTrace_7750621 : CollatzResearch.WordTrace tailWord_7750621 prefixEnd_7750621 3979793943831225393393049 := by
  unfold tailWord_7750621
  simp only [CollatzResearch.WordTrace]
  refine ⟨282688371653831292526715717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188458914435887528351143811 282688371653831292526715717)
  ·
    refine ⟨53004069685093367348759197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282688371653831292526715717 53004069685093367348759197)
    ·
      refine ⟨19876526131910012755784699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53004069685093367348759197 19876526131910012755784699)
      ·
        refine ⟨29814789197865019133677049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19876526131910012755784699 29814789197865019133677049)
        ·
          refine ⟨22361091898398764350257787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29814789197865019133677049 22361091898398764350257787)
          ·
            refine ⟨33541637847598146525386681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22361091898398764350257787 33541637847598146525386681)
            ·
              refine ⟨25156228385698609894040011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33541637847598146525386681 25156228385698609894040011)
              ·
                refine ⟨37734342578547914841060017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25156228385698609894040011 37734342578547914841060017)
                ·
                  refine ⟨28300756933910936130795013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37734342578547914841060017 28300756933910936130795013)
                  ·
                    refine ⟨5306391925108300524524065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28300756933910936130795013 5306391925108300524524065)
                    ·
                      refine ⟨3979793943831225393393049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5306391925108300524524065 3979793943831225393393049)
                      ·
                        rfl

theorem cell23_7750621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_7750621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750621 prefixEnd_7750621 := by exact prefixLift 7750621
  have htrace : WordTrace (prefixWord ++ tailWord_7750621) baseStart_7750621 baseEnd_7750621 := by
    simpa [prefixWord, tailWord_7750621, baseEnd_7750621] using wordTrace_append hprefix tailTrace_7750621
  have hstable : (prefixWord ++ tailWord_7750621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750621).length < 2 ^ (prefixWord ++ tailWord_7750621).sum := by decide
  have hdescent : baseEnd_7750621 < baseStart_7750621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750691 : List Nat := [1, 1, 1, 4, 3, 4, 1, 2, 1, 5]
def baseStart_7750691 : Nat := 118140960795 + 7750691 * 2 ^ 59
def prefixEnd_7750691 : Nat := 4983230072969 + 3 ^ 40 * 7750691 * 2
def baseEnd_7750691 : Nat := 1326609962492346706505909

theorem tailTrace_7750691 : CollatzResearch.WordTrace tailWord_7750691 prefixEnd_7750691 1326609962492346706505909 := by
  unfold tailWord_7750691
  simp only [CollatzResearch.WordTrace]
  refine ⟨282690924763577694481763927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188460616509051796321175951 282690924763577694481763927)
  ·
    refine ⟨424036387145366541722645891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282690924763577694481763927 424036387145366541722645891)
    ·
      refine ⟨636054580718049812583968837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424036387145366541722645891 636054580718049812583968837)
      ·
        refine ⟨119260233884634339859494157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 636054580718049812583968837 119260233884634339859494157)
        ·
          refine ⟨44722587706737877447310309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119260233884634339859494157 44722587706737877447310309)
          ·
            refine ⟨8385485195013352021370683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44722587706737877447310309 8385485195013352021370683)
            ·
              refine ⟨12578227792520028032056025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8385485195013352021370683 12578227792520028032056025)
              ·
                refine ⟨9433670844390021024042019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12578227792520028032056025 9433670844390021024042019)
                ·
                  refine ⟨14150506266585031536063029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9433670844390021024042019 14150506266585031536063029)
                  ·
                    refine ⟨1326609962492346706505909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14150506266585031536063029 1326609962492346706505909)
                    ·
                      rfl

theorem cell23_7750691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 5].length) (baseStart_7750691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750691 prefixEnd_7750691 := by exact prefixLift 7750691
  have htrace : WordTrace (prefixWord ++ tailWord_7750691) baseStart_7750691 baseEnd_7750691 := by
    simpa [prefixWord, tailWord_7750691, baseEnd_7750691] using wordTrace_append hprefix tailTrace_7750691
  have hstable : (prefixWord ++ tailWord_7750691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750691).length < 2 ^ (prefixWord ++ tailWord_7750691).sum := by decide
  have hdescent : baseEnd_7750691 < baseStart_7750691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750714 : List Nat := [3, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5]
def baseStart_7750714 : Nat := 118140960795 + 7750714 * 2 ^ 59
def prefixEnd_7750714 : Nat := 4983230072969 + 3 ^ 40 * 7750714 * 2
def baseEnd_7750714 : Nat := 3979841697532093529530121

theorem tailTrace_7750714 : CollatzResearch.WordTrace tailWord_7750714 prefixEnd_7750714 3979841697532093529530121 := by
  unfold tailWord_7750714
  simp only [CollatzResearch.WordTrace]
  refine ⟨70672940910623592352462799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188461175761662912939900797 70672940910623592352462799)
  ·
    refine ⟨106009411365935388528694199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70672940910623592352462799 106009411365935388528694199)
    ·
      refine ⟨159014117048903082793041299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106009411365935388528694199 159014117048903082793041299)
      ·
        refine ⟨238521175573354624189561949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159014117048903082793041299 238521175573354624189561949)
        ·
          refine ⟨89445440840007984071085731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238521175573354624189561949 89445440840007984071085731)
          ·
            refine ⟨134168161260011976106628597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89445440840007984071085731 134168161260011976106628597)
            ·
              refine ⟨12578265118126122759996431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134168161260011976106628597 12578265118126122759996431)
              ·
                refine ⟨18867397677189184139994647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12578265118126122759996431 18867397677189184139994647)
                ·
                  refine ⟨28301096515783776209991971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18867397677189184139994647 28301096515783776209991971)
                  ·
                    refine ⟨42451644773675664314987957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28301096515783776209991971 42451644773675664314987957)
                    ·
                      refine ⟨3979841697532093529530121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42451644773675664314987957 3979841697532093529530121)
                      ·
                        rfl

theorem cell23_7750714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5].length) (baseStart_7750714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750714 prefixEnd_7750714 := by exact prefixLift 7750714
  have htrace : WordTrace (prefixWord ++ tailWord_7750714) baseStart_7750714 baseEnd_7750714 := by
    simpa [prefixWord, tailWord_7750714, baseEnd_7750714] using wordTrace_append hprefix tailTrace_7750714
  have hstable : (prefixWord ++ tailWord_7750714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750714).length < 2 ^ (prefixWord ++ tailWord_7750714).sum := by decide
  have hdescent : baseEnd_7750714 < baseStart_7750714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750717 : List Nat := [1, 4, 1, 3, 1, 13]
def baseStart_7750717 : Nat := 118140960795 + 7750717 * 2 ^ 59
def prefixEnd_7750717 : Nat := 4983230072969 + 3 ^ 40 * 7750717 * 2
def baseEnd_7750717 : Nat := 16377955711827395134949

theorem tailTrace_7750717 : CollatzResearch.WordTrace tailWord_7750717 prefixEnd_7750717 16377955711827395134949 := by
  unfold tailWord_7750717
  simp only [CollatzResearch.WordTrace]
  refine ⟨282691873061483500922210405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188461248707655667281473603 282691873061483500922210405)
  ·
    refine ⟨53004726199028156422914451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282691873061483500922210405 53004726199028156422914451)
    ·
      refine ⟨79507089298542234634371677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53004726199028156422914451 79507089298542234634371677)
      ·
        refine ⟨29815158486953337987889379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79507089298542234634371677 29815158486953337987889379)
        ·
          refine ⟨44722737730430006981834069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29815158486953337987889379 44722737730430006981834069)
          ·
            refine ⟨16377955711827395134949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 44722737730430006981834069 16377955711827395134949)
            ·
              rfl

theorem cell23_7750717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 13].length) (baseStart_7750717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750717 prefixEnd_7750717 := by exact prefixLift 7750717
  have htrace : WordTrace (prefixWord ++ tailWord_7750717) baseStart_7750717 baseEnd_7750717 := by
    simpa [prefixWord, tailWord_7750717, baseEnd_7750717] using wordTrace_append hprefix tailTrace_7750717
  have hstable : (prefixWord ++ tailWord_7750717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750717).length < 2 ^ (prefixWord ++ tailWord_7750717).sum := by decide
  have hdescent : baseEnd_7750717 < baseStart_7750717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750737 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 2, 2, 6]
def baseStart_7750737 : Nat := 118140960795 + 7750737 * 2 ^ 59
def prefixEnd_7750737 : Nat := 4983230072969 + 3 ^ 40 * 7750737 * 2
def baseEnd_7750737 : Nat := 3979853507587146939542515

theorem tailTrace_7750737 : CollatzResearch.WordTrace tailWord_7750737 prefixEnd_7750737 3979853507587146939542515 := by
  unfold tailWord_7750737
  simp only [CollatzResearch.WordTrace]
  refine ⟨282692602521411044337938465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188461735014274029558625643 282692602521411044337938465)
  ·
    refine ⟨212019451891058283253453849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282692602521411044337938465 212019451891058283253453849)
    ·
      refine ⟨159014588918293712440090387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212019451891058283253453849 159014588918293712440090387)
      ·
        refine ⟨238521883377440568660135581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159014588918293712440090387 238521883377440568660135581)
        ·
          refine ⟨89445706266540213247550843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238521883377440568660135581 89445706266540213247550843)
          ·
            refine ⟨134168559399810319871326265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89445706266540213247550843 134168559399810319871326265)
            ·
              refine ⟨100626419549857739903494699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134168559399810319871326265 100626419549857739903494699)
              ·
                refine ⟨150939629324786609855242049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100626419549857739903494699 150939629324786609855242049)
                ·
                  refine ⟨113204721993589957391431537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150939629324786609855242049 113204721993589957391431537)
                  ·
                    refine ⟨84903541495192468043573653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113204721993589957391431537 84903541495192468043573653)
                    ·
                      refine ⟨3979853507587146939542515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84903541495192468043573653 3979853507587146939542515)
                      ·
                        rfl

theorem cell23_7750737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_7750737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750737 prefixEnd_7750737 := by exact prefixLift 7750737
  have htrace : WordTrace (prefixWord ++ tailWord_7750737) baseStart_7750737 baseEnd_7750737 := by
    simpa [prefixWord, tailWord_7750737, baseEnd_7750737] using wordTrace_append hprefix tailTrace_7750737
  have hstable : (prefixWord ++ tailWord_7750737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750737).length < 2 ^ (prefixWord ++ tailWord_7750737).sum := by decide
  have hdescent : baseEnd_7750737 < baseStart_7750737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750762 : List Nat := [3, 1, 3, 2, 2, 2, 2, 3, 1, 2, 2]
def baseStart_7750762 : Nat := 118140960795 + 7750762 * 2 ^ 59
def prefixEnd_7750762 : Nat := 4983230072969 + 3 ^ 40 * 7750762 * 2
def baseEnd_7750762 : Nat := 3979866344603509341729901

theorem tailTrace_7750762 : CollatzResearch.WordTrace tailWord_7750762 prefixEnd_7750762 3979866344603509341729901 := by
  unfold tailWord_7750762
  simp only [CollatzResearch.WordTrace]
  refine ⟨70673378586580118401899635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188462342897546982405065693 70673378586580118401899635)
  ·
    refine ⟨106010067879870177602849453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70673378586580118401899635 106010067879870177602849453)
    ·
      refine ⟨39753775454951316601068545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106010067879870177602849453 39753775454951316601068545)
      ·
        refine ⟨29815331591213487450801409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39753775454951316601068545 29815331591213487450801409)
        ·
          refine ⟨22361498693410115588101057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29815331591213487450801409 22361498693410115588101057)
          ·
            refine ⟨16771124020057586691075793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22361498693410115588101057 16771124020057586691075793)
            ·
              refine ⟨12578343015043190018306845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16771124020057586691075793 12578343015043190018306845)
              ·
                refine ⟨4716878630641196256865067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12578343015043190018306845 4716878630641196256865067)
                ·
                  refine ⟨7075317945961794385297601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4716878630641196256865067 7075317945961794385297601)
                  ·
                    refine ⟨5306488459471345788973201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7075317945961794385297601 5306488459471345788973201)
                    ·
                      refine ⟨3979866344603509341729901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5306488459471345788973201 3979866344603509341729901)
                      ·
                        rfl

theorem cell23_7750762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_7750762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750762 prefixEnd_7750762 := by exact prefixLift 7750762
  have htrace : WordTrace (prefixWord ++ tailWord_7750762) baseStart_7750762 baseEnd_7750762 := by
    simpa [prefixWord, tailWord_7750762, baseEnd_7750762] using wordTrace_append hprefix tailTrace_7750762
  have hstable : (prefixWord ++ tailWord_7750762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750762).length < 2 ^ (prefixWord ++ tailWord_7750762).sum := by decide
  have hdescent : baseEnd_7750762 < baseStart_7750762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750765 : List Nat := [1, 5, 1, 1, 2, 4, 2, 1, 1, 2, 3]
def baseStart_7750765 : Nat := 118140960795 + 7750765 * 2 ^ 59
def prefixEnd_7750765 : Nat := 4983230072969 + 3 ^ 40 * 7750765 * 2
def baseEnd_7750765 : Nat := 3979867885045472829992387

theorem tailTrace_7750765 : CollatzResearch.WordTrace tailWord_7750765 prefixEnd_7750765 3979867885045472829992387 := by
  unfold tailWord_7750765
  simp only [CollatzResearch.WordTrace]
  refine ⟨282693623765309605119957749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188462415843539736746638499 282693623765309605119957749)
  ·
    refine ⟨26502527227997775479996039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 282693623765309605119957749 26502527227997775479996039)
    ·
      refine ⟨39753790841996663219994059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26502527227997775479996039 39753790841996663219994059)
      ·
        refine ⟨59630686262994994829991089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39753790841996663219994059 59630686262994994829991089)
        ·
          refine ⟨44723014697246246122493317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59630686262994994829991089 44723014697246246122493317)
          ·
            refine ⟨8385565255733671147967497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44723014697246246122493317 8385565255733671147967497)
            ·
              refine ⟨6289173941800253360975623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8385565255733671147967497 6289173941800253360975623)
              ·
                refine ⟨9433760912700380041463435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6289173941800253360975623 9433760912700380041463435)
                ·
                  refine ⟨14150641369050570062195153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9433760912700380041463435 14150641369050570062195153)
                  ·
                    refine ⟨10612981026787927546646365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14150641369050570062195153 10612981026787927546646365)
                    ·
                      refine ⟨3979867885045472829992387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10612981026787927546646365 3979867885045472829992387)
                      ·
                        rfl

theorem cell23_7750765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_7750765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750765 prefixEnd_7750765 := by exact prefixLift 7750765
  have htrace : WordTrace (prefixWord ++ tailWord_7750765) baseStart_7750765 baseEnd_7750765 := by
    simpa [prefixWord, tailWord_7750765, baseEnd_7750765] using wordTrace_append hprefix tailTrace_7750765
  have hstable : (prefixWord ++ tailWord_7750765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750765).length < 2 ^ (prefixWord ++ tailWord_7750765).sum := by decide
  have hdescent : baseEnd_7750765 < baseStart_7750765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750794 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 2, 6]
def baseStart_7750794 : Nat := 118140960795 + 7750794 * 2 ^ 59
def prefixEnd_7750794 : Nat := 4983230072969 + 3 ^ 40 * 7750794 * 2
def baseEnd_7750794 : Nat := 1326627591994817738843251

theorem tailTrace_7750794 : CollatzResearch.WordTrace tailWord_7750794 prefixEnd_7750794 1326627591994817738843251 := by
  unfold tailWord_7750794
  simp only [CollatzResearch.WordTrace]
  refine ⟨70673670370551135768190859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188463120988136362048508957 70673670370551135768190859)
  ·
    refine ⟨106010505555826703652286289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70673670370551135768190859 106010505555826703652286289)
    ·
      refine ⟨79507879166870027739214717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106010505555826703652286289 79507879166870027739214717)
      ·
        refine ⟨29815454687576260402205519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79507879166870027739214717 29815454687576260402205519)
        ·
          refine ⟨44723182031364390603308279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29815454687576260402205519 44723182031364390603308279)
          ·
            refine ⟨67084773047046585904962419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44723182031364390603308279 67084773047046585904962419)
            ·
              refine ⟨100627159570569878857443629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67084773047046585904962419 100627159570569878857443629)
              ·
                refine ⟨37735184838963704571541361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100627159570569878857443629 37735184838963704571541361)
                ·
                  refine ⟨28301388629222778428656021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37735184838963704571541361 28301388629222778428656021)
                  ·
                    refine ⟨1326627591994817738843251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28301388629222778428656021 1326627591994817738843251)
                    ·
                      rfl

theorem cell23_7750794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_7750794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750794 prefixEnd_7750794 := by exact prefixLift 7750794
  have htrace : WordTrace (prefixWord ++ tailWord_7750794) baseStart_7750794 baseEnd_7750794 := by
    simpa [prefixWord, tailWord_7750794, baseEnd_7750794] using wordTrace_append hprefix tailTrace_7750794
  have hstable : (prefixWord ++ tailWord_7750794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750794).length < 2 ^ (prefixWord ++ tailWord_7750794).sum := by decide
  have hdescent : baseEnd_7750794 < baseStart_7750794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750841 : List Nat := [1, 2, 1, 4, 1, 5, 1, 1, 7]
def baseStart_7750841 : Nat := 118140960795 + 7750841 * 2 ^ 59
def prefixEnd_7750841 : Nat := 4983230072969 + 3 ^ 40 * 7750841 * 2
def baseEnd_7750841 : Nat := 442211878841690503626893

theorem tailTrace_7750841 : CollatzResearch.WordTrace tailWord_7750841 prefixEnd_7750841 442211878841690503626893 := by
  unfold tailWord_7750841
  simp only [CollatzResearch.WordTrace]
  refine ⟨282696395713034270099724377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188464263808689513399816251 282696395713034270099724377)
  ·
    refine ⟨212022296784775702574793283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282696395713034270099724377 212022296784775702574793283)
    ·
      refine ⟨318033445177163553862189925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212022296784775702574793283 318033445177163553862189925)
      ·
        refine ⟨59631270970718166349160611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318033445177163553862189925 59631270970718166349160611)
        ·
          refine ⟨89446906456077249523740917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59631270970718166349160611 89446906456077249523740917)
          ·
            refine ⟨8385647480257242142850711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89446906456077249523740917 8385647480257242142850711)
            ·
              refine ⟨12578471220385863214276067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8385647480257242142850711 12578471220385863214276067)
              ·
                refine ⟨18867706830578794821414101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12578471220385863214276067 18867706830578794821414101)
                ·
                  refine ⟨442211878841690503626893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18867706830578794821414101 442211878841690503626893)
                  ·
                    rfl

theorem cell23_7750841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 7].length) (baseStart_7750841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750841 prefixEnd_7750841 := by exact prefixLift 7750841
  have htrace : WordTrace (prefixWord ++ tailWord_7750841) baseStart_7750841 baseEnd_7750841 := by
    simpa [prefixWord, tailWord_7750841, baseEnd_7750841] using wordTrace_append hprefix tailTrace_7750841
  have hstable : (prefixWord ++ tailWord_7750841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750841).length < 2 ^ (prefixWord ++ tailWord_7750841).sum := by decide
  have hdescent : baseEnd_7750841 < baseStart_7750841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750852 : List Nat := [2, 3, 3, 1, 3, 1, 1, 3, 2, 2, 2]
def baseStart_7750852 : Nat := 118140960795 + 7750852 * 2 ^ 59
def prefixEnd_7750852 : Nat := 4983230072969 + 3 ^ 40 * 7750852 * 2
def baseEnd_7750852 : Nat := 3979912557862413989604487

theorem tailTrace_7750852 : CollatzResearch.WordTrace tailWord_7750852 prefixEnd_7750852 3979912557862413989604487 := by
  unfold tailWord_7750852
  simp only [CollatzResearch.WordTrace]
  refine ⟨141348398457997209489187405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188464531277329612652249873 141348398457997209489187405)
  ·
    refine ⟨53005649421748953558445277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141348398457997209489187405 53005649421748953558445277)
    ·
      refine ⟨19877118533155857584416979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53005649421748953558445277 19877118533155857584416979)
      ·
        refine ⟨29815677799733786376625469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19877118533155857584416979 29815677799733786376625469)
        ·
          refine ⟨11180879174900169891234551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29815677799733786376625469 11180879174900169891234551)
          ·
            refine ⟨16771318762350254836851827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11180879174900169891234551 16771318762350254836851827)
            ·
              refine ⟨25156978143525382255277741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16771318762350254836851827 25156978143525382255277741)
              ·
                refine ⟨9433866803822018345729153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25156978143525382255277741 9433866803822018345729153)
                ·
                  refine ⟨7075400102866513759296865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9433866803822018345729153 7075400102866513759296865)
                  ·
                    refine ⟨5306550077149885319472649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7075400102866513759296865 5306550077149885319472649)
                    ·
                      refine ⟨3979912557862413989604487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5306550077149885319472649 3979912557862413989604487)
                      ·
                        rfl

theorem cell23_7750852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_7750852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750852 prefixEnd_7750852 := by exact prefixLift 7750852
  have htrace : WordTrace (prefixWord ++ tailWord_7750852) baseStart_7750852 baseEnd_7750852 := by
    simpa [prefixWord, tailWord_7750852, baseEnd_7750852] using wordTrace_append hprefix tailTrace_7750852
  have hstable : (prefixWord ++ tailWord_7750852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750852).length < 2 ^ (prefixWord ++ tailWord_7750852).sum := by decide
  have hdescent : baseEnd_7750852 < baseStart_7750852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750891 : List Nat := [1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 4]
def baseStart_7750891 : Nat := 118140960795 + 7750891 * 2 ^ 59
def prefixEnd_7750891 : Nat := 4983230072969 + 3 ^ 40 * 7750891 * 2
def baseEnd_7750891 : Nat := 3979932583607939337016807

theorem tailTrace_7750891 : CollatzResearch.WordTrace tailWord_7750891 prefixEnd_7750891 3979932583607939337016807 := by
  unfold tailWord_7750891
  simp only [CollatzResearch.WordTrace]
  refine ⟨282698219362853128639044527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188465479575235419092696351 282698219362853128639044527)
  ·
    refine ⟨424047329044279692958566791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282698219362853128639044527 424047329044279692958566791)
    ·
      refine ⟨636070993566419539437850187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424047329044279692958566791 636070993566419539437850187)
      ·
        refine ⟨954106490349629309156775281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636070993566419539437850187 954106490349629309156775281)
        ·
          refine ⟨715579867762221981867581461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 954106490349629309156775281 715579867762221981867581461)
          ·
            refine ⟨33542806301354155400042881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 715579867762221981867581461 33542806301354155400042881)
            ·
              refine ⟨25157104726015616550032161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33542806301354155400042881 25157104726015616550032161)
              ·
                refine ⟨18867828544511712412524121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25157104726015616550032161 18867828544511712412524121)
                ·
                  refine ⟨14150871408383784309393091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18867828544511712412524121 14150871408383784309393091)
                  ·
                    refine ⟨21226307112575676464089637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14150871408383784309393091 21226307112575676464089637)
                    ·
                      refine ⟨3979932583607939337016807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21226307112575676464089637 3979932583607939337016807)
                      ·
                        rfl

theorem cell23_7750891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 4].length) (baseStart_7750891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750891 prefixEnd_7750891 := by exact prefixLift 7750891
  have htrace : WordTrace (prefixWord ++ tailWord_7750891) baseStart_7750891 baseEnd_7750891 := by
    simpa [prefixWord, tailWord_7750891, baseEnd_7750891] using wordTrace_append hprefix tailTrace_7750891
  have hstable : (prefixWord ++ tailWord_7750891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750891).length < 2 ^ (prefixWord ++ tailWord_7750891).sum := by decide
  have hdescent : baseEnd_7750891 < baseStart_7750891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750904 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 4, 4, 4]
def baseStart_7750904 : Nat := 118140960795 + 7750904 * 2 ^ 59
def prefixEnd_7750904 : Nat := 4983230072969 + 3 ^ 40 * 7750904 * 2
def baseEnd_7750904 : Nat := 3979939258856447786154247

theorem tailTrace_7750904 : CollatzResearch.WordTrace tailWord_7750904 prefixEnd_7750904 3979939258856447786154247 := by
  unfold tailWord_7750904
  simp only [CollatzResearch.WordTrace]
  refine ⟨141349346755903015929633883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188465795674537354572845177 141349346755903015929633883)
  ·
    refine ⟨212024020133854523894450825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141349346755903015929633883 212024020133854523894450825)
    ·
      refine ⟨159018015100390892920838119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212024020133854523894450825 159018015100390892920838119)
      ·
        refine ⟨238527022650586339381257179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159018015100390892920838119 238527022650586339381257179)
        ·
          refine ⟨357790533975879509071885769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238527022650586339381257179 357790533975879509071885769)
          ·
            refine ⟨268342900481909631803914327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357790533975879509071885769 268342900481909631803914327)
            ·
              refine ⟨402514350722864447705871491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268342900481909631803914327 402514350722864447705871491)
              ·
                refine ⟨603771526084296671558807237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402514350722864447705871491 603771526084296671558807237)
                ·
                  refine ⟨113207161140805625917276357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 603771526084296671558807237 113207161140805625917276357)
                  ·
                    refine ⟨21226342713901054859489317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113207161140805625917276357 21226342713901054859489317)
                    ·
                      refine ⟨3979939258856447786154247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21226342713901054859489317 3979939258856447786154247)
                      ·
                        rfl

theorem cell23_7750904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_7750904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750904 prefixEnd_7750904 := by exact prefixLift 7750904
  have htrace : WordTrace (prefixWord ++ tailWord_7750904) baseStart_7750904 baseEnd_7750904 := by
    simpa [prefixWord, tailWord_7750904, baseEnd_7750904] using wordTrace_append hprefix tailTrace_7750904
  have hstable : (prefixWord ++ tailWord_7750904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750904).length < 2 ^ (prefixWord ++ tailWord_7750904).sum := by decide
  have hdescent : baseEnd_7750904 < baseStart_7750904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750935 : List Nat := [1, 1, 3, 4, 1, 1, 4, 3, 1, 4]
def baseStart_7750935 : Nat := 118140960795 + 7750935 * 2 ^ 59
def prefixEnd_7750935 : Nat := 4983230072969 + 3 ^ 40 * 7750935 * 2
def baseEnd_7750935 : Nat := 1326651725585579054955535

theorem tailTrace_7750935 : CollatzResearch.WordTrace tailWord_7750935 prefixEnd_7750935 1326651725585579054955535 := by
  unfold tailWord_7750935
  simp only [CollatzResearch.WordTrace]
  refine ⟨282699824174693724153646259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188466549449795816102430839 282699824174693724153646259)
  ·
    refine ⟨424049736262040586230469389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282699824174693724153646259 424049736262040586230469389)
    ·
      refine ⟨159018651098265219836426021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424049736262040586230469389 159018651098265219836426021)
      ·
        refine ⟨29815997080924728719329879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159018651098265219836426021 29815997080924728719329879)
        ·
          refine ⟨44723995621387093078994819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29815997080924728719329879 44723995621387093078994819)
          ·
            refine ⟨67085993432080639618492229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44723995621387093078994819 67085993432080639618492229)
            ·
              refine ⟨12578623768515119928467293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67085993432080639618492229 12578623768515119928467293)
              ·
                refine ⟨4716983913193169973175235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12578623768515119928467293 4716983913193169973175235)
                ·
                  refine ⟨7075475869789754959762853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4716983913193169973175235 7075475869789754959762853)
                  ·
                    refine ⟨1326651725585579054955535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7075475869789754959762853 1326651725585579054955535)
                    ·
                      rfl

theorem cell23_7750935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 1, 4].length) (baseStart_7750935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750935 prefixEnd_7750935 := by exact prefixLift 7750935
  have htrace : WordTrace (prefixWord ++ tailWord_7750935) baseStart_7750935 baseEnd_7750935 := by
    simpa [prefixWord, tailWord_7750935, baseEnd_7750935] using wordTrace_append hprefix tailTrace_7750935
  have hstable : (prefixWord ++ tailWord_7750935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750935).length < 2 ^ (prefixWord ++ tailWord_7750935).sum := by decide
  have hdescent : baseEnd_7750935 < baseStart_7750935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7750981 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 3, 1, 4]
def baseStart_7750981 : Nat := 118140960795 + 7750981 * 2 ^ 59
def prefixEnd_7750981 : Nat := 4983230072969 + 3 ^ 40 * 7750981 * 2
def baseEnd_7750981 : Nat := 3979978796866843984891393

theorem tailTrace_7750981 : CollatzResearch.WordTrace tailWord_7750981 prefixEnd_7750981 3979978796866843984891393 := by
  unfold tailWord_7750981
  simp only [CollatzResearch.WordTrace]
  refine ⟨282701501932527074009820797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188467667955018049339880531 282701501932527074009820797)
  ·
    refine ⟨106013063224697652753682799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282701501932527074009820797 106013063224697652753682799)
    ·
      refine ⟨159019594837046479130524199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106013063224697652753682799 159019594837046479130524199)
      ·
        refine ⟨238529392255569718695786299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159019594837046479130524199 238529392255569718695786299)
        ·
          refine ⟨357794088383354578043679449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238529392255569718695786299 357794088383354578043679449)
          ·
            refine ⟨268345566287515933532759587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357794088383354578043679449 268345566287515933532759587)
            ·
              refine ⟨402518349431273900299139381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268345566287515933532759587 402518349431273900299139381)
              ·
                refine ⟨37736095259181928153044317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 402518349431273900299139381 37736095259181928153044317)
                ·
                  refine ⟨14151035722193223057391619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37736095259181928153044317 14151035722193223057391619)
                  ·
                    refine ⟨21226553583289834586087429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14151035722193223057391619 21226553583289834586087429)
                    ·
                      refine ⟨3979978796866843984891393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21226553583289834586087429 3979978796866843984891393)
                      ·
                        rfl

theorem cell23_7750981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_7750981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7750981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7750981 prefixEnd_7750981 := by exact prefixLift 7750981
  have htrace : WordTrace (prefixWord ++ tailWord_7750981) baseStart_7750981 baseEnd_7750981 := by
    simpa [prefixWord, tailWord_7750981, baseEnd_7750981] using wordTrace_append hprefix tailTrace_7750981
  have hstable : (prefixWord ++ tailWord_7750981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7750981).length < 2 ^ (prefixWord ++ tailWord_7750981).sum := by decide
  have hdescent : baseEnd_7750981 < baseStart_7750981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7750981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751001 : List Nat := [1, 2, 1, 2, 2, 2, 3, 3, 1, 1, 5]
def baseStart_7751001 : Nat := 118140960795 + 7751001 * 2 ^ 59
def prefixEnd_7751001 : Nat := 4983230072969 + 3 ^ 40 * 7751001 * 2
def baseEnd_7751001 : Nat := 3979989066479933906641301

theorem tailTrace_7751001 : CollatzResearch.WordTrace tailWord_7751001 prefixEnd_7751001 3979989066479933906641301 := by
  unfold tailWord_7751001
  simp only [CollatzResearch.WordTrace]
  refine ⟨282702231392454617425548857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188468154261636411617032571 282702231392454617425548857)
  ·
    refine ⟨212026673544340963069161643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282702231392454617425548857 212026673544340963069161643)
    ·
      refine ⟨318040010316511444603742465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212026673544340963069161643 318040010316511444603742465)
      ·
        refine ⟨238530007737383583452806849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318040010316511444603742465 238530007737383583452806849)
        ·
          refine ⟨178897505803037687589605137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238530007737383583452806849 178897505803037687589605137)
          ·
            refine ⟨134173129352278265692203853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178897505803037687589605137 134173129352278265692203853)
            ·
              refine ⟨50314923507104349634576445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134173129352278265692203853 50314923507104349634576445)
              ·
                refine ⟨18868096315164131112966167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50314923507104349634576445 18868096315164131112966167)
                ·
                  refine ⟨28302144472746196669449251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18868096315164131112966167 28302144472746196669449251)
                  ·
                    refine ⟨42453216709119295004173877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28302144472746196669449251 42453216709119295004173877)
                    ·
                      refine ⟨3979989066479933906641301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42453216709119295004173877 3979989066479933906641301)
                      ·
                        rfl

theorem cell23_7751001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_7751001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751001 prefixEnd_7751001 := by exact prefixLift 7751001
  have htrace : WordTrace (prefixWord ++ tailWord_7751001) baseStart_7751001 baseEnd_7751001 := by
    simpa [prefixWord, tailWord_7751001, baseEnd_7751001] using wordTrace_append hprefix tailTrace_7751001
  have hstable : (prefixWord ++ tailWord_7751001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751001).length < 2 ^ (prefixWord ++ tailWord_7751001).sum := by decide
  have hdescent : baseEnd_7751001 < baseStart_7751001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751008 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 4, 4]
def baseStart_7751008 : Nat := 118140960795 + 7751008 * 2 ^ 59
def prefixEnd_7751008 : Nat := 4983230072969 + 3 ^ 40 * 7751008 * 2
def baseEnd_7751008 : Nat := 1326664220281505126417923

theorem tailTrace_7751008 : CollatzResearch.WordTrace tailWord_7751008 prefixEnd_7751008 1326664220281505126417923 := by
  unfold tailWord_7751008
  simp only [CollatzResearch.WordTrace]
  refine ⟨141351243351714628810526839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188468324468952838414035785 141351243351714628810526839)
  ·
    refine ⟨212026865027571943215790259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141351243351714628810526839 212026865027571943215790259)
    ·
      refine ⟨318040297541357914823685389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212026865027571943215790259 318040297541357914823685389)
      ·
        refine ⟨119265111578009218058882021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318040297541357914823685389 119265111578009218058882021)
        ·
          refine ⟨22362208420876728386040379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119265111578009218058882021 22362208420876728386040379)
          ·
            refine ⟨33543312631315092579060569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22362208420876728386040379 33543312631315092579060569)
            ·
              refine ⟨25157484473486319434295427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33543312631315092579060569 25157484473486319434295427)
              ·
                refine ⟨37736226710229479151443141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25157484473486319434295427 37736226710229479151443141)
                ·
                  refine ⟨7075542508168027340895589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37736226710229479151443141 7075542508168027340895589)
                  ·
                    refine ⟨1326664220281505126417923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7075542508168027340895589 1326664220281505126417923)
                    ·
                      rfl

theorem cell23_7751008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 4, 4].length) (baseStart_7751008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751008 prefixEnd_7751008 := by exact prefixLift 7751008
  have htrace : WordTrace (prefixWord ++ tailWord_7751008) baseStart_7751008 baseEnd_7751008 := by
    simpa [prefixWord, tailWord_7751008, baseEnd_7751008] using wordTrace_append hprefix tailTrace_7751008
  have hstable : (prefixWord ++ tailWord_7751008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751008).length < 2 ^ (prefixWord ++ tailWord_7751008).sum := by decide
  have hdescent : baseEnd_7751008 < baseStart_7751008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751011 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 6]
def baseStart_7751011 : Nat := 118140960795 + 7751011 * 2 ^ 59
def prefixEnd_7751011 : Nat := 4983230072969 + 3 ^ 40 * 7751011 * 2
def baseEnd_7751011 : Nat := 3979994201286478867516255

theorem tailTrace_7751011 : CollatzResearch.WordTrace tailWord_7751011 prefixEnd_7751011 3979994201286478867516255 := by
  unfold tailWord_7751011
  simp only [CollatzResearch.WordTrace]
  refine ⟨282702596122418389133412887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188468397414945592755608591 282702596122418389133412887)
  ·
    refine ⟨424053894183627583700119331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282702596122418389133412887 424053894183627583700119331)
    ·
      refine ⟨636080841275441375550178997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424053894183627583700119331 636080841275441375550178997)
      ·
        refine ⟨59632578869572628957829281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 636080841275441375550178997 59632578869572628957829281)
        ·
          refine ⟨44724434152179471718371961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59632578869572628957829281 44724434152179471718371961)
          ·
            refine ⟨33543325614134603788778971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44724434152179471718371961 33543325614134603788778971)
            ·
              refine ⟨50314988421201905683168457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33543325614134603788778971 50314988421201905683168457)
              ·
                refine ⟨37736241315901429262376343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50314988421201905683168457 37736241315901429262376343)
                ·
                  refine ⟨56604361973852143893564515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37736241315901429262376343 56604361973852143893564515)
                  ·
                    refine ⟨84906542960778215840346773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56604361973852143893564515 84906542960778215840346773)
                    ·
                      refine ⟨3979994201286478867516255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84906542960778215840346773 3979994201286478867516255)
                      ·
                        rfl

theorem cell23_7751011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_7751011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751011 prefixEnd_7751011 := by exact prefixLift 7751011
  have htrace : WordTrace (prefixWord ++ tailWord_7751011) baseStart_7751011 baseEnd_7751011 := by
    simpa [prefixWord, tailWord_7751011, baseEnd_7751011] using wordTrace_append hprefix tailTrace_7751011
  have hstable : (prefixWord ++ tailWord_7751011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751011).length < 2 ^ (prefixWord ++ tailWord_7751011).sum := by decide
  have hdescent : baseEnd_7751011 < baseStart_7751011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751021 : List Nat := [1, 5, 1, 1, 1, 3, 1, 10]
def baseStart_7751021 : Nat := 118140960795 + 7751021 * 2 ^ 59
def prefixEnd_7751021 : Nat := 4983230072969 + 3 ^ 40 * 7751021 * 2
def baseEnd_7751021 : Nat := 147407382818260141792267

theorem tailTrace_7751021 : CollatzResearch.WordTrace tailWord_7751021 prefixEnd_7751021 147407382818260141792267 := by
  unfold tailWord_7751021
  simp only [CollatzResearch.WordTrace]
  refine ⟨282702960852382160841276917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188468640568254773894184611 282702960852382160841276917)
  ·
    refine ⟨26503402579910827578869711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 282702960852382160841276917 26503402579910827578869711)
    ·
      refine ⟨39755103869866241368304567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26503402579910827578869711 39755103869866241368304567)
      ·
        refine ⟨59632655804799362052456851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39755103869866241368304567 59632655804799362052456851)
        ·
          refine ⟨89448983707199043078685277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59632655804799362052456851 89448983707199043078685277)
          ·
            refine ⟨33543368890199641154506979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89448983707199043078685277 33543368890199641154506979)
            ·
              refine ⟨50315053335299461731760469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33543368890199641154506979 50315053335299461731760469)
              ·
                refine ⟨147407382818260141792267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50315053335299461731760469 147407382818260141792267)
                ·
                  rfl

theorem cell23_7751021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 10].length) (baseStart_7751021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751021 prefixEnd_7751021 := by exact prefixLift 7751021
  have htrace : WordTrace (prefixWord ++ tailWord_7751021) baseStart_7751021 baseEnd_7751021 := by
    simpa [prefixWord, tailWord_7751021, baseEnd_7751021] using wordTrace_append hprefix tailTrace_7751021
  have hstable : (prefixWord ++ tailWord_7751021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751021).length < 2 ^ (prefixWord ++ tailWord_7751021).sum := by decide
  have hdescent : baseEnd_7751021 < baseStart_7751021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751025 : List Nat := [1, 2, 2, 2, 1, 2, 6, 1, 2, 4]
def baseStart_7751025 : Nat := 118140960795 + 7751025 * 2 ^ 59
def prefixEnd_7751025 : Nat := 4983230072969 + 3 ^ 40 * 7751025 * 2
def baseEnd_7751025 : Nat := 1326667130005213937580397

theorem tailTrace_7751025 : CollatzResearch.WordTrace tailWord_7751025 prefixEnd_7751025 1326667130005213937580397 := by
  unfold tailWord_7751025
  simp only [CollatzResearch.WordTrace]
  refine ⟨282703106744367669524422529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188468737829578446349615019 282703106744367669524422529)
  ·
    refine ⟨212027330058275752143316897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282703106744367669524422529 212027330058275752143316897)
    ·
      refine ⟨159020497543706814107487673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212027330058275752143316897 159020497543706814107487673)
      ·
        refine ⟨119265373157780110580615755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159020497543706814107487673 119265373157780110580615755)
        ·
          refine ⟨178898059736670165870923633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119265373157780110580615755 178898059736670165870923633)
          ·
            refine ⟨134173544802502624403192725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178898059736670165870923633 134173544802502624403192725)
            ·
              refine ⟨6289384912617310518899659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134173544802502624403192725 6289384912617310518899659)
              ·
                refine ⟨9434077368925965778349489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6289384912617310518899659 9434077368925965778349489)
                ·
                  refine ⟨7075558026694474333762117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9434077368925965778349489 7075558026694474333762117)
                  ·
                    refine ⟨1326667130005213937580397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7075558026694474333762117 1326667130005213937580397)
                    ·
                      rfl

theorem cell23_7751025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 2, 4].length) (baseStart_7751025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751025 prefixEnd_7751025 := by exact prefixLift 7751025
  have htrace : WordTrace (prefixWord ++ tailWord_7751025) baseStart_7751025 baseEnd_7751025 := by
    simpa [prefixWord, tailWord_7751025, baseEnd_7751025] using wordTrace_append hprefix tailTrace_7751025
  have hstable : (prefixWord ++ tailWord_7751025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751025).length < 2 ^ (prefixWord ++ tailWord_7751025).sum := by decide
  have hdescent : baseEnd_7751025 < baseStart_7751025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751048 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 3, 3, 3]
def baseStart_7751048 : Nat := 118140960795 + 7751048 * 2 ^ 59
def prefixEnd_7751048 : Nat := 4983230072969 + 3 ^ 40 * 7751048 * 2
def baseEnd_7751048 : Nat := 3980013200070695222753585

theorem tailTrace_7751048 : CollatzResearch.WordTrace tailWord_7751048 prefixEnd_7751048 3980013200070695222753585 := by
  unfold tailWord_7751048
  simp only [CollatzResearch.WordTrace]
  refine ⟨141351972811642172226254899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188469297082189562968339865 141351972811642172226254899)
  ·
    refine ⟨212027959217463258339382349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141351972811642172226254899 212027959217463258339382349)
    ·
      refine ⟨79510484706548721877268381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212027959217463258339382349 79510484706548721877268381)
      ·
        refine ⟨29816431764955770703975643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79510484706548721877268381 29816431764955770703975643)
        ·
          refine ⟨44724647647433656055963465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29816431764955770703975643 44724647647433656055963465)
          ·
            refine ⟨33543485735575242041972599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44724647647433656055963465 33543485735575242041972599)
            ·
              refine ⟨50315228603362863062958899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33543485735575242041972599 50315228603362863062958899)
              ·
                refine ⟨75472842905044294594438349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50315228603362863062958899 75472842905044294594438349)
                ·
                  refine ⟨28302316089391610472914381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75472842905044294594438349 28302316089391610472914381)
                  ·
                    refine ⟨10613368533521853927342893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28302316089391610472914381 10613368533521853927342893)
                    ·
                      refine ⟨3980013200070695222753585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10613368533521853927342893 3980013200070695222753585)
                      ·
                        rfl

theorem cell23_7751048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_7751048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751048 prefixEnd_7751048 := by exact prefixLift 7751048
  have htrace : WordTrace (prefixWord ++ tailWord_7751048) baseStart_7751048 baseEnd_7751048 := by
    simpa [prefixWord, tailWord_7751048, baseEnd_7751048] using wordTrace_append hprefix tailTrace_7751048
  have hstable : (prefixWord ++ tailWord_7751048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751048).length < 2 ^ (prefixWord ++ tailWord_7751048).sum := by decide
  have hdescent : baseEnd_7751048 < baseStart_7751048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751061 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 2, 2, 5]
def baseStart_7751061 : Nat := 118140960795 + 7751061 * 2 ^ 59
def prefixEnd_7751061 : Nat := 4983230072969 + 3 ^ 40 * 7751061 * 2
def baseEnd_7751061 : Nat := 3980019875319203671891025

theorem tailTrace_7751061 : CollatzResearch.WordTrace tailWord_7751061 prefixEnd_7751061 3980019875319203671891025 := by
  unfold tailWord_7751061
  simp only [CollatzResearch.WordTrace]
  refine ⟨282704419772237247672733037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188469613181491498448488691 282704419772237247672733037)
  ·
    refine ⟨106014157414588967877274889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282704419772237247672733037 106014157414588967877274889)
    ·
      refine ⟨79510618060941725907956167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106014157414588967877274889 79510618060941725907956167)
      ·
        refine ⟨119265927091412588861934251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79510618060941725907956167 119265927091412588861934251)
        ·
          refine ⟨178898890637118883292901377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119265927091412588861934251 178898890637118883292901377)
          ·
            refine ⟨134174167977839162469676033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178898890637118883292901377 134174167977839162469676033)
            ·
              refine ⟨100630625983379371852257025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134174167977839162469676033 100630625983379371852257025)
              ·
                refine ⟨75472969487534528889192769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100630625983379371852257025 75472969487534528889192769)
                ·
                  refine ⟨56604727115650896666894577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75472969487534528889192769 56604727115650896666894577)
                  ·
                    refine ⟨42453545336738172500170933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56604727115650896666894577 42453545336738172500170933)
                    ·
                      refine ⟨3980019875319203671891025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42453545336738172500170933 3980019875319203671891025)
                      ·
                        rfl

theorem cell23_7751061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_7751061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751061 prefixEnd_7751061 := by exact prefixLift 7751061
  have htrace : WordTrace (prefixWord ++ tailWord_7751061) baseStart_7751061 baseEnd_7751061 := by
    simpa [prefixWord, tailWord_7751061, baseEnd_7751061] using wordTrace_append hprefix tailTrace_7751061
  have hstable : (prefixWord ++ tailWord_7751061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751061).length < 2 ^ (prefixWord ++ tailWord_7751061).sum := by decide
  have hdescent : baseEnd_7751061 < baseStart_7751061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751065 : List Nat := [1, 2, 1, 2, 1, 5, 1, 4, 2, 1, 3]
def baseStart_7751065 : Nat := 118140960795 + 7751065 * 2 ^ 59
def prefixEnd_7751065 : Nat := 4983230072969 + 3 ^ 40 * 7751065 * 2
def baseEnd_7751065 : Nat := 3980021929241821656241007

theorem tailTrace_7751065 : CollatzResearch.WordTrace tailWord_7751065 prefixEnd_7751065 3980021929241821656241007 := by
  unfold tailWord_7751065
  simp only [CollatzResearch.WordTrace]
  refine ⟨282704565664222756355878649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188469710442815170903919099 282704565664222756355878649)
  ·
    refine ⟨212028424248167067266908987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282704565664222756355878649 212028424248167067266908987)
    ·
      refine ⟨318042636372250600900363481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212028424248167067266908987 318042636372250600900363481)
      ·
        refine ⟨238531977279187950675272611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318042636372250600900363481 238531977279187950675272611)
        ·
          refine ⟨357797965918781926012908917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238531977279187950675272611 357797965918781926012908917)
          ·
            refine ⟨33543559304885805563710211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 357797965918781926012908917 33543559304885805563710211)
            ·
              refine ⟨50315338957328708345565317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33543559304885805563710211 50315338957328708345565317)
              ·
                refine ⟨9434126054499132814793497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50315338957328708345565317 9434126054499132814793497)
                ·
                  refine ⟨7075594540874349611095123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9434126054499132814793497 7075594540874349611095123)
                  ·
                    refine ⟨10613391811311524416642685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7075594540874349611095123 10613391811311524416642685)
                    ·
                      refine ⟨3980021929241821656241007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10613391811311524416642685 3980021929241821656241007)
                      ·
                        rfl

theorem cell23_7751065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 1, 3].length) (baseStart_7751065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751065 prefixEnd_7751065 := by exact prefixLift 7751065
  have htrace : WordTrace (prefixWord ++ tailWord_7751065) baseStart_7751065 baseEnd_7751065 := by
    simpa [prefixWord, tailWord_7751065, baseEnd_7751065] using wordTrace_append hprefix tailTrace_7751065
  have hstable : (prefixWord ++ tailWord_7751065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751065).length < 2 ^ (prefixWord ++ tailWord_7751065).sum := by decide
  have hdescent : baseEnd_7751065 < baseStart_7751065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751091 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 5]
def baseStart_7751091 : Nat := 118140960795 + 7751091 * 2 ^ 59
def prefixEnd_7751091 : Nat := 4983230072969 + 3 ^ 40 * 7751091 * 2
def baseEnd_7751091 : Nat := 3980035279738838554515887

theorem tailTrace_7751091 : CollatzResearch.WordTrace tailWord_7751091 prefixEnd_7751091 3980035279738838554515887 := by
  unfold tailWord_7751091
  simp only [CollatzResearch.WordTrace]
  refine ⟨282705513962128562796325127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188470342641419041864216751 282705513962128562796325127)
  ·
    refine ⟨424058270943192844194487691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282705513962128562796325127 424058270943192844194487691)
    ·
      refine ⟨636087406414789266291731537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424058270943192844194487691 636087406414789266291731537)
      ·
        refine ⟨477065554811091949718798653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 636087406414789266291731537 477065554811091949718798653)
        ·
          refine ⟨178899583054159481144549495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 477065554811091949718798653 178899583054159481144549495)
          ·
            refine ⟨268349374581239221716824243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178899583054159481144549495 268349374581239221716824243)
            ·
              refine ⟨402524061871858832575236365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268349374581239221716824243 402524061871858832575236365)
              ·
                refine ⟨150946523201947062215713637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 402524061871858832575236365 150946523201947062215713637)
                ·
                  refine ⟨28302473100365074165446307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150946523201947062215713637 28302473100365074165446307)
                  ·
                    refine ⟨42453709650547611248169461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28302473100365074165446307 42453709650547611248169461)
                    ·
                      refine ⟨3980035279738838554515887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42453709650547611248169461 3980035279738838554515887)
                      ·
                        rfl

theorem cell23_7751091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 5].length) (baseStart_7751091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751091 prefixEnd_7751091 := by exact prefixLift 7751091
  have htrace : WordTrace (prefixWord ++ tailWord_7751091) baseStart_7751091 baseEnd_7751091 := by
    simpa [prefixWord, tailWord_7751091, baseEnd_7751091] using wordTrace_append hprefix tailTrace_7751091
  have hstable : (prefixWord ++ tailWord_7751091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751091).length < 2 ^ (prefixWord ++ tailWord_7751091).sum := by decide
  have hdescent : baseEnd_7751091 < baseStart_7751091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751111 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 9]
def baseStart_7751111 : Nat := 118140960795 + 7751111 * 2 ^ 59
def prefixEnd_7751111 : Nat := 4983230072969 + 3 ^ 40 * 7751111 * 2
def baseEnd_7751111 : Nat := 442227283261325386251755

theorem tailTrace_7751111 : CollatzResearch.WordTrace tailWord_7751111 prefixEnd_7751111 442227283261325386251755 := by
  unfold tailWord_7751111
  simp only [CollatzResearch.WordTrace]
  refine ⟨282706243422056106212053187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188470828948037404141368791 282706243422056106212053187)
  ·
    refine ⟨424059365133084159318079781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282706243422056106212053187 424059365133084159318079781)
    ·
      refine ⟨79511130962453279872139959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 424059365133084159318079781 79511130962453279872139959)
      ·
        refine ⟨119266696443679919808209939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79511130962453279872139959 119266696443679919808209939)
        ·
          refine ⟨178900044665519879712314909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119266696443679919808209939 178900044665519879712314909)
          ·
            refine ⟨67087516749569954892118091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178900044665519879712314909 67087516749569954892118091)
            ·
              refine ⟨100631275124354932338177137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67087516749569954892118091 100631275124354932338177137)
              ·
                refine ⟨75473456343266199253632853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100631275124354932338177137 75473456343266199253632853)
                ·
                  refine ⟨442227283261325386251755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75473456343266199253632853 442227283261325386251755)
                  ·
                    rfl

theorem cell23_7751111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 9].length) (baseStart_7751111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751111 prefixEnd_7751111 := by exact prefixLift 7751111
  have htrace : WordTrace (prefixWord ++ tailWord_7751111) baseStart_7751111 baseEnd_7751111 := by
    simpa [prefixWord, tailWord_7751111, baseEnd_7751111] using wordTrace_append hprefix tailTrace_7751111
  have hstable : (prefixWord ++ tailWord_7751111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751111).length < 2 ^ (prefixWord ++ tailWord_7751111).sum := by decide
  have hdescent : baseEnd_7751111 < baseStart_7751111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751118 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4]
def baseStart_7751118 : Nat := 118140960795 + 7751118 * 2 ^ 59
def prefixEnd_7751118 : Nat := 4983230072969 + 3 ^ 40 * 7751118 * 2
def baseEnd_7751118 : Nat := 3980049143716509948878263

theorem tailTrace_7751118 : CollatzResearch.WordTrace tailWord_7751118 prefixEnd_7751118 3980049143716509948878263 := by
  unfold tailWord_7751118
  simp only [CollatzResearch.WordTrace]
  refine ⟨35338312341628843300944751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188470999155353830938372005 35338312341628843300944751)
  ·
    refine ⟨53007468512443264951417127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35338312341628843300944751 53007468512443264951417127)
    ·
      refine ⟨79511202768664897427125691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53007468512443264951417127 79511202768664897427125691)
      ·
        refine ⟨119266804152997346140688537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79511202768664897427125691 119266804152997346140688537)
        ·
          refine ⟨89450103114748009605516403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119266804152997346140688537 89450103114748009605516403)
          ·
            refine ⟨134175154672122014408274605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89450103114748009605516403 134175154672122014408274605)
            ·
              refine ⟨50315683002045755403102977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134175154672122014408274605 50315683002045755403102977)
              ·
                refine ⟨37736762251534316552327233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50315683002045755403102977 37736762251534316552327233)
                ·
                  refine ⟨28302571688650737414245425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37736762251534316552327233 28302571688650737414245425)
                  ·
                    refine ⟨21226928766488053060684069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28302571688650737414245425 21226928766488053060684069)
                    ·
                      refine ⟨3980049143716509948878263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21226928766488053060684069 3980049143716509948878263)
                      ·
                        rfl

theorem cell23_7751118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_7751118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751118 prefixEnd_7751118 := by exact prefixLift 7751118
  have htrace : WordTrace (prefixWord ++ tailWord_7751118) baseStart_7751118 baseEnd_7751118 := by
    simpa [prefixWord, tailWord_7751118, baseEnd_7751118] using wordTrace_append hprefix tailTrace_7751118
  have hstable : (prefixWord ++ tailWord_7751118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751118).length < 2 ^ (prefixWord ++ tailWord_7751118).sum := by decide
  have hdescent : baseEnd_7751118 < baseStart_7751118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751175 : List Nat := [1, 1, 4, 3, 2, 2, 1, 2, 2, 5]
def baseStart_7751175 : Nat := 118140960795 + 7751175 * 2 ^ 59
def prefixEnd_7751175 : Nat := 4983230072969 + 3 ^ 40 * 7751175 * 2
def baseEnd_7751175 : Nat := 1326692804037938741955167

theorem tailTrace_7751175 : CollatzResearch.WordTrace tailWord_7751175 prefixEnd_7751175 1326692804037938741955167 := by
  unfold tailWord_7751175
  simp only [CollatzResearch.WordTrace]
  refine ⟨282708577693824245142382979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188472385129216163428255319 282708577693824245142382979)
  ·
    refine ⟨424062866540736367713574469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282708577693824245142382979 424062866540736367713574469)
    ·
      refine ⟨79511787476388068946295213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 424062866540736367713574469 79511787476388068946295213)
      ·
        refine ⟨29816920303645525854860705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79511787476388068946295213 29816920303645525854860705)
        ·
          refine ⟨22362690227734144391145529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29816920303645525854860705 22362690227734144391145529)
          ·
            refine ⟨16772017670800608293359147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22362690227734144391145529 16772017670800608293359147)
            ·
              refine ⟨25158026506200912440038721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16772017670800608293359147 25158026506200912440038721)
              ·
                refine ⟨18868519879650684330029041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25158026506200912440038721 18868519879650684330029041)
                ·
                  refine ⟨14151389909738013247521781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18868519879650684330029041 14151389909738013247521781)
                  ·
                    refine ⟨1326692804037938741955167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14151389909738013247521781 1326692804037938741955167)
                    ·
                      rfl

theorem cell23_7751175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_7751175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751175 prefixEnd_7751175 := by exact prefixLift 7751175
  have htrace : WordTrace (prefixWord ++ tailWord_7751175) baseStart_7751175 baseEnd_7751175 := by
    simpa [prefixWord, tailWord_7751175, baseEnd_7751175] using wordTrace_append hprefix tailTrace_7751175
  have hstable : (prefixWord ++ tailWord_7751175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751175).length < 2 ^ (prefixWord ++ tailWord_7751175).sum := by decide
  have hdescent : baseEnd_7751175 < baseStart_7751175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751239 : List Nat := [1, 1, 4, 1, 5, 1, 1, 4, 1, 4]
def baseStart_7751239 : Nat := 118140960795 + 7751239 * 2 ^ 59
def prefixEnd_7751239 : Nat := 4983230072969 + 3 ^ 40 * 7751239 * 2
def baseEnd_7751239 : Nat := 1326703758291901325155069

theorem tailTrace_7751239 : CollatzResearch.WordTrace tailWord_7751239 prefixEnd_7751239 1326703758291901325155069 := by
  unfold tailWord_7751239
  simp only [CollatzResearch.WordTrace]
  refine ⟨282710911965592384072712771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188473941310394922715141847 282710911965592384072712771)
  ·
    refine ⟨424066367948388576109069157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282710911965592384072712771 424066367948388576109069157)
    ·
      refine ⟨79512443990322858020450467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 424066367948388576109069157 79512443990322858020450467)
      ·
        refine ⟨119268665985484287030675701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79512443990322858020450467 119268665985484287030675701)
        ·
          refine ⟨11181437436139151909125847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119268665985484287030675701 11181437436139151909125847)
          ·
            refine ⟨16772156154208727863688771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11181437436139151909125847 16772156154208727863688771)
            ·
              refine ⟨25158234231313091795533157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16772156154208727863688771 25158234231313091795533157)
              ·
                refine ⟨4717168918371204711662467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25158234231313091795533157 4717168918371204711662467)
                ·
                  refine ⟨7075753377556807067493701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4717168918371204711662467 7075753377556807067493701)
                  ·
                    refine ⟨1326703758291901325155069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7075753377556807067493701 1326703758291901325155069)
                    ·
                      rfl

theorem cell23_7751239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_7751239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751239 prefixEnd_7751239 := by exact prefixLift 7751239
  have htrace : WordTrace (prefixWord ++ tailWord_7751239) baseStart_7751239 baseEnd_7751239 := by
    simpa [prefixWord, tailWord_7751239, baseEnd_7751239] using wordTrace_append hprefix tailTrace_7751239
  have hstable : (prefixWord ++ tailWord_7751239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751239).length < 2 ^ (prefixWord ++ tailWord_7751239).sum := by decide
  have hdescent : baseEnd_7751239 < baseStart_7751239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751248 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 5, 5]
def baseStart_7751248 : Nat := 118140960795 + 7751248 * 2 ^ 59
def prefixEnd_7751248 : Nat := 4983230072969 + 3 ^ 40 * 7751248 * 2
def baseEnd_7751248 : Nat := 1326705298733864813417555

theorem tailTrace_7751248 : CollatzResearch.WordTrace tailWord_7751248 prefixEnd_7751248 1326705298733864813417555 := by
  unfold tailWord_7751248
  simp only [CollatzResearch.WordTrace]
  refine ⟨141355620111279889304895199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188474160148373185739860265 141355620111279889304895199)
  ·
    refine ⟨212033430166919833957342799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141355620111279889304895199 212033430166919833957342799)
    ·
      refine ⟨318050145250379750936014199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212033430166919833957342799 318050145250379750936014199)
      ·
        refine ⟨477075217875569626404021299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318050145250379750936014199 477075217875569626404021299)
        ·
          refine ⟨715612826813354439606031949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477075217875569626404021299 715612826813354439606031949)
          ·
            refine ⟨268354810055007914852261981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 715612826813354439606031949 268354810055007914852261981)
            ·
              refine ⟨100633053770627968069598243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268354810055007914852261981 100633053770627968069598243)
              ·
                refine ⟨150949580655941952104397365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100633053770627968069598243 150949580655941952104397365)
                ·
                  refine ⟨14151523186494558009787253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150949580655941952104397365 14151523186494558009787253)
                  ·
                    refine ⟨1326705298733864813417555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14151523186494558009787253 1326705298733864813417555)
                    ·
                      rfl

theorem cell23_7751248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 5, 5].length) (baseStart_7751248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751248 prefixEnd_7751248 := by exact prefixLift 7751248
  have htrace : WordTrace (prefixWord ++ tailWord_7751248) baseStart_7751248 baseEnd_7751248 := by
    simpa [prefixWord, tailWord_7751248, baseEnd_7751248] using wordTrace_append hprefix tailTrace_7751248
  have hstable : (prefixWord ++ tailWord_7751248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751248).length < 2 ^ (prefixWord ++ tailWord_7751248).sum := by decide
  have hdescent : baseEnd_7751248 < baseStart_7751248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751265 : List Nat := [1, 2, 3, 1, 1, 3, 2, 4, 1, 5]
def baseStart_7751265 : Nat := 118140960795 + 7751265 * 2 ^ 59
def prefixEnd_7751265 : Nat := 4983230072969 + 3 ^ 40 * 7751265 * 2
def baseEnd_7751265 : Nat := 1326708208457573624580029

theorem tailTrace_7751265 : CollatzResearch.WordTrace tailWord_7751265 prefixEnd_7751265 1326708208457573624580029 := by
  unfold tailWord_7751265
  simp only [CollatzResearch.WordTrace]
  refine ⟨282711860263498190513159249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188474573508998793675439499 282711860263498190513159249)
  ·
    refine ⟨212033895197623642884869437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282711860263498190513159249 212033895197623642884869437)
    ·
      refine ⟨79512710699108866081826039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212033895197623642884869437 79512710699108866081826039)
      ·
        refine ⟨119269066048663299122739059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79512710699108866081826039 119269066048663299122739059)
        ·
          refine ⟨178903599072994948684108589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119269066048663299122739059 178903599072994948684108589)
          ·
            refine ⟨67088849652373105756540721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178903599072994948684108589 67088849652373105756540721)
            ·
              refine ⟨50316637239279829317405541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67088849652373105756540721 50316637239279829317405541)
              ·
                refine ⟨9434369482364967997013539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50316637239279829317405541 9434369482364967997013539)
                ·
                  refine ⟨14151554223547451995520309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9434369482364967997013539 14151554223547451995520309)
                  ·
                    refine ⟨1326708208457573624580029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14151554223547451995520309 1326708208457573624580029)
                    ·
                      rfl

theorem cell23_7751265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_7751265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751265 prefixEnd_7751265 := by exact prefixLift 7751265
  have htrace : WordTrace (prefixWord ++ tailWord_7751265) baseStart_7751265 baseEnd_7751265 := by
    simpa [prefixWord, tailWord_7751265, baseEnd_7751265] using wordTrace_append hprefix tailTrace_7751265
  have hstable : (prefixWord ++ tailWord_7751265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751265).length < 2 ^ (prefixWord ++ tailWord_7751265).sum := by decide
  have hdescent : baseEnd_7751265 < baseStart_7751265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751282 : List Nat := [3, 2, 1, 2, 3, 2, 1, 3, 1, 5]
def baseStart_7751282 : Nat := 118140960795 + 7751282 * 2 ^ 59
def prefixEnd_7751282 : Nat := 4983230072969 + 3 ^ 40 * 7751282 * 2
def baseEnd_7751282 : Nat := 1326711118181282435742503

theorem tailTrace_7751282 : CollatzResearch.WordTrace tailWord_7751282 prefixEnd_7751282 1326711118181282435742503 := by
  unfold tailWord_7751282
  simp only [CollatzResearch.WordTrace]
  refine ⟨70678120076109150604132025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188474986869624401611018733 70678120076109150604132025)
  ·
    refine ⟨53008590057081862953099019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70678120076109150604132025 53008590057081862953099019)
    ·
      refine ⟨79512885085622794429648529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53008590057081862953099019 79512885085622794429648529)
      ·
        refine ⟨59634663814217095822236397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79512885085622794429648529 59634663814217095822236397)
        ·
          refine ⟨22362998930331410933338649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59634663814217095822236397 22362998930331410933338649)
          ·
            refine ⟨16772249197748558200003987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22362998930331410933338649 16772249197748558200003987)
            ·
              refine ⟨25158373796622837300005981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16772249197748558200003987 25158373796622837300005981)
              ·
                refine ⟨9434390173733563987502243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25158373796622837300005981 9434390173733563987502243)
                ·
                  refine ⟨14151585260600345981253365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9434390173733563987502243 14151585260600345981253365)
                  ·
                    refine ⟨1326711118181282435742503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14151585260600345981253365 1326711118181282435742503)
                    ·
                      rfl

theorem cell23_7751282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_7751282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751282 prefixEnd_7751282 := by exact prefixLift 7751282
  have htrace : WordTrace (prefixWord ++ tailWord_7751282) baseStart_7751282 baseEnd_7751282 := by
    simpa [prefixWord, tailWord_7751282, baseEnd_7751282] using wordTrace_append hprefix tailTrace_7751282
  have hstable : (prefixWord ++ tailWord_7751282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751282).length < 2 ^ (prefixWord ++ tailWord_7751282).sum := by decide
  have hdescent : baseEnd_7751282 < baseStart_7751282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751305 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 5, 2, 3]
def baseStart_7751305 : Nat := 118140960795 + 7751305 * 2 ^ 59
def prefixEnd_7751305 : Nat := 4983230072969 + 3 ^ 40 * 7751305 * 2
def baseEnd_7751305 : Nat := 3980145164598900717239903

theorem tailTrace_7751305 : CollatzResearch.WordTrace tailWord_7751305 prefixEnd_7751305 3980145164598900717239903 := by
  unfold tailWord_7751305
  simp only [CollatzResearch.WordTrace]
  refine ⟨282713319183353277344615369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188475546122235518229743579 282713319183353277344615369)
  ·
    refine ⟨212034989387514958008461527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282713319183353277344615369 212034989387514958008461527)
    ·
      refine ⟨318052484081272437012692291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212034989387514958008461527 318052484081272437012692291)
      ·
        refine ⟨477078726121908655519038437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318052484081272437012692291 477078726121908655519038437)
        ·
          refine ⟨89452261147857872909819707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 477078726121908655519038437 89452261147857872909819707)
          ·
            refine ⟨134178391721786809364729561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89452261147857872909819707 134178391721786809364729561)
            ·
              refine ⟨100633793791340107023547171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134178391721786809364729561 100633793791340107023547171)
              ·
                refine ⟨150950690687010160535320757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100633793791340107023547171 150950690687010160535320757)
                ·
                  refine ⟨14151627251907202550186321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150950690687010160535320757 14151627251907202550186321)
                  ·
                    refine ⟨10613720438930401912639741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14151627251907202550186321 10613720438930401912639741)
                    ·
                      refine ⟨3980145164598900717239903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10613720438930401912639741 3980145164598900717239903)
                      ·
                        rfl

theorem cell23_7751305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 2, 3].length) (baseStart_7751305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751305 prefixEnd_7751305 := by exact prefixLift 7751305
  have htrace : WordTrace (prefixWord ++ tailWord_7751305) baseStart_7751305 baseEnd_7751305 := by
    simpa [prefixWord, tailWord_7751305, baseEnd_7751305] using wordTrace_append hprefix tailTrace_7751305
  have hstable : (prefixWord ++ tailWord_7751305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751305).length < 2 ^ (prefixWord ++ tailWord_7751305).sum := by decide
  have hdescent : baseEnd_7751305 < baseStart_7751305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751308 : List Nat := [2, 2, 1, 2, 1, 1, 4, 10]
def baseStart_7751308 : Nat := 118140960795 + 7751308 * 2 ^ 59
def prefixEnd_7751308 : Nat := 4983230072969 + 3 ^ 40 * 7751308 * 2
def baseEnd_7751308 : Nat := 147412840927439415018607

theorem tailTrace_7751308 : CollatzResearch.WordTrace tailWord_7751308 prefixEnd_7751308 147412840927439415018607 := by
  unfold tailWord_7751308
  simp only [CollatzResearch.WordTrace]
  refine ⟨141356714301171204428487289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188475619068228272571316385 141356714301171204428487289)
  ·
    refine ⟨106017535725878403321365467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141356714301171204428487289 106017535725878403321365467)
    ·
      refine ⟨159026303588817604982048201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106017535725878403321365467 159026303588817604982048201)
      ·
        refine ⟨119269727691613203736536151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159026303588817604982048201 119269727691613203736536151)
        ·
          refine ⟨178904591537419805604804227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119269727691613203736536151 178904591537419805604804227)
          ·
            refine ⟨268356887306129708407206341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178904591537419805604804227 268356887306129708407206341)
            ·
              refine ⟨50316916369899320326351189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268356887306129708407206341 50316916369899320326351189)
              ·
                refine ⟨147412840927439415018607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50316916369899320326351189 147412840927439415018607)
                ·
                  rfl

theorem cell23_7751308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 10].length) (baseStart_7751308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751308 prefixEnd_7751308 := by exact prefixLift 7751308
  have htrace : WordTrace (prefixWord ++ tailWord_7751308) baseStart_7751308 baseEnd_7751308 := by
    simpa [prefixWord, tailWord_7751308, baseEnd_7751308] using wordTrace_append hprefix tailTrace_7751308
  have hstable : (prefixWord ++ tailWord_7751308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751308).length < 2 ^ (prefixWord ++ tailWord_7751308).sum := by decide
  have hdescent : baseEnd_7751308 < baseStart_7751308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751319 : List Nat := [1, 1, 3, 3, 2, 2, 2, 2, 3, 2, 2]
def baseStart_7751319 : Nat := 118140960795 + 7751319 * 2 ^ 59
def prefixEnd_7751319 : Nat := 4983230072969 + 3 ^ 40 * 7751319 * 2
def baseEnd_7751319 : Nat := 3980152353328063662464839

theorem tailTrace_7751319 : CollatzResearch.WordTrace tailWord_7751319 prefixEnd_7751319 3980152353328063662464839 := by
  unfold tailWord_7751319
  simp only [CollatzResearch.WordTrace]
  refine ⟨282713829805302557735625011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188475886536868371823750007 282713829805302557735625011)
  ·
    refine ⟨424070744707953836603437517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282713829805302557735625011 424070744707953836603437517)
    ·
      refine ⟨159026529265482688726289069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424070744707953836603437517 159026529265482688726289069)
      ·
        refine ⟨59634948474556008272358401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159026529265482688726289069 59634948474556008272358401)
        ·
          refine ⟨44726211355917006204268801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59634948474556008272358401 44726211355917006204268801)
          ·
            refine ⟨33544658516937754653201601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44726211355917006204268801 33544658516937754653201601)
            ·
              refine ⟨25158493887703315989901201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33544658516937754653201601 25158493887703315989901201)
              ·
                refine ⟨18868870415777486992425901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25158493887703315989901201 18868870415777486992425901)
                ·
                  refine ⟨7075826405916557622159713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18868870415777486992425901 7075826405916557622159713)
                  ·
                    refine ⟨5306869804437418216619785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7075826405916557622159713 5306869804437418216619785)
                    ·
                      refine ⟨3980152353328063662464839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5306869804437418216619785 3980152353328063662464839)
                      ·
                        rfl

theorem cell23_7751319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_7751319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751319 prefixEnd_7751319 := by exact prefixLift 7751319
  have htrace : WordTrace (prefixWord ++ tailWord_7751319) baseStart_7751319 baseEnd_7751319 := by
    simpa [prefixWord, tailWord_7751319, baseEnd_7751319] using wordTrace_append hprefix tailTrace_7751319
  have hstable : (prefixWord ++ tailWord_7751319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751319).length < 2 ^ (prefixWord ++ tailWord_7751319).sum := by decide
  have hdescent : baseEnd_7751319 < baseStart_7751319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751330 : List Nat := [3, 3, 1, 4, 1, 2, 1, 3, 1, 1, 3]
def baseStart_7751330 : Nat := 118140960795 + 7751330 * 2 ^ 59
def prefixEnd_7751330 : Nat := 4983230072969 + 3 ^ 40 * 7751330 * 2
def baseEnd_7751330 : Nat := 3980158001615263119427289

theorem tailTrace_7751330 : CollatzResearch.WordTrace tailWord_7751330 prefixEnd_7751330 3980158001615263119427289 := by
  unfold tailWord_7751330
  simp only [CollatzResearch.WordTrace]
  refine ⟨70678557752065676653568861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188476154005508471076183629 70678557752065676653568861)
  ·
    refine ⟨26504459157024628745088323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70678557752065676653568861 26504459157024628745088323)
    ·
      refine ⟨39756688735536943117632485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26504459157024628745088323 39756688735536943117632485)
      ·
        refine ⟨7454379137913176834556091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39756688735536943117632485 7454379137913176834556091)
        ·
          refine ⟨11181568706869765251834137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7454379137913176834556091 11181568706869765251834137)
          ·
            refine ⟨8386176530152323938875603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11181568706869765251834137 8386176530152323938875603)
            ·
              refine ⟨12579264795228485908313405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8386176530152323938875603 12579264795228485908313405)
              ·
                refine ⟨4717224298210682215617527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12579264795228485908313405 4717224298210682215617527)
                ·
                  refine ⟨7075836447316023323426291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4717224298210682215617527 7075836447316023323426291)
                  ·
                    refine ⟨10613754670974034985139437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7075836447316023323426291 10613754670974034985139437)
                    ·
                      refine ⟨3980158001615263119427289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10613754670974034985139437 3980158001615263119427289)
                      ·
                        rfl

theorem cell23_7751330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_7751330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751330 prefixEnd_7751330 := by exact prefixLift 7751330
  have htrace : WordTrace (prefixWord ++ tailWord_7751330) baseStart_7751330 baseEnd_7751330 := by
    simpa [prefixWord, tailWord_7751330, baseEnd_7751330] using wordTrace_append hprefix tailTrace_7751330
  have hstable : (prefixWord ++ tailWord_7751330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751330).length < 2 ^ (prefixWord ++ tailWord_7751330).sum := by decide
  have hdescent : baseEnd_7751330 < baseStart_7751330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751373 : List Nat := [1, 6, 2, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_7751373 : Nat := 118140960795 + 7751373 * 2 ^ 59
def prefixEnd_7751373 : Nat := 4983230072969 + 3 ^ 40 * 7751373 * 2
def baseEnd_7751373 : Nat := 3980180081283406451189591

theorem tailTrace_7751373 : CollatzResearch.WordTrace tailWord_7751373 prefixEnd_7751373 3980180081283406451189591 := by
  unfold tailWord_7751373
  simp only [CollatzResearch.WordTrace]
  refine ⟨282715799347106924958090773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188477199564737949972060515 282715799347106924958090773)
  ·
    refine ⟨13252303094395637107410505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 282715799347106924958090773 13252303094395637107410505)
    ·
      refine ⟨9939227320796727830557879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13252303094395637107410505 9939227320796727830557879)
      ·
        refine ⟨14908840981195091745836819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9939227320796727830557879 14908840981195091745836819)
        ·
          refine ⟨22363261471792637618755229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14908840981195091745836819 22363261471792637618755229)
          ·
            refine ⟨8386223051922239107033211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22363261471792637618755229 8386223051922239107033211)
            ·
              refine ⟨12579334577883358660549817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8386223051922239107033211 12579334577883358660549817)
              ·
                refine ⟨9434500933412518995412363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12579334577883358660549817 9434500933412518995412363)
                ·
                  refine ⟨14151751400118778493118545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9434500933412518995412363 14151751400118778493118545)
                  ·
                    refine ⟨10613813550089083869838909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14151751400118778493118545 10613813550089083869838909)
                    ·
                      refine ⟨3980180081283406451189591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10613813550089083869838909 3980180081283406451189591)
                      ·
                        rfl

theorem cell23_7751373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_7751373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751373 prefixEnd_7751373 := by exact prefixLift 7751373
  have htrace : WordTrace (prefixWord ++ tailWord_7751373) baseStart_7751373 baseEnd_7751373 := by
    simpa [prefixWord, tailWord_7751373, baseEnd_7751373] using wordTrace_append hprefix tailTrace_7751373
  have hstable : (prefixWord ++ tailWord_7751373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751373).length < 2 ^ (prefixWord ++ tailWord_7751373).sum := by decide
  have hdescent : baseEnd_7751373 < baseStart_7751373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751392 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 3, 4, 2]
def baseStart_7751392 : Nat := 118140960795 + 7751392 * 2 ^ 59
def prefixEnd_7751392 : Nat := 4983230072969 + 3 ^ 40 * 7751392 * 2
def baseEnd_7751392 : Nat := 3980189837415841876852003

theorem tailTrace_7751392 : CollatzResearch.WordTrace tailWord_7751392 prefixEnd_7751392 3980189837415841876852003 := by
  unfold tailWord_7751392
  simp only [CollatzResearch.WordTrace]
  refine ⟨141358246167019045601516215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188477661556025394135354953 141358246167019045601516215)
  ·
    refine ⟨212037369250528568402274323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141358246167019045601516215 212037369250528568402274323)
    ·
      refine ⟨318056053875792852603411485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212037369250528568402274323 318056053875792852603411485)
      ·
        refine ⟨119271020203422319726279307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318056053875792852603411485 119271020203422319726279307)
        ·
          refine ⟨178906530305133479589418961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119271020203422319726279307 178906530305133479589418961)
          ·
            refine ⟨134179897728850109692064221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178906530305133479589418961 134179897728850109692064221)
            ·
              refine ⟨50317461648318791134524083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134179897728850109692064221 50317461648318791134524083)
              ·
                refine ⟨75476192472478186701786125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50317461648318791134524083 75476192472478186701786125)
                ·
                  refine ⟨28303572177179320013169797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75476192472478186701786125 28303572177179320013169797)
                  ·
                    refine ⟨5306919783221122502469337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28303572177179320013169797 5306919783221122502469337)
                    ·
                      refine ⟨3980189837415841876852003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5306919783221122502469337 3980189837415841876852003)
                      ·
                        rfl

theorem cell23_7751392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 3, 4, 2].length) (baseStart_7751392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751392 prefixEnd_7751392 := by exact prefixLift 7751392
  have htrace : WordTrace (prefixWord ++ tailWord_7751392) baseStart_7751392 baseEnd_7751392 := by
    simpa [prefixWord, tailWord_7751392, baseEnd_7751392] using wordTrace_append hprefix tailTrace_7751392
  have hstable : (prefixWord ++ tailWord_7751392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751392).length < 2 ^ (prefixWord ++ tailWord_7751392).sum := by decide
  have hdescent : baseEnd_7751392 < baseStart_7751392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751396 : List Nat := [2, 3, 1, 1, 1, 3, 5, 1, 1, 3, 2]
def baseStart_7751396 : Nat := 118140960795 + 7751396 * 2 ^ 59
def prefixEnd_7751396 : Nat := 4983230072969 + 3 ^ 40 * 7751396 * 2
def baseEnd_7751396 : Nat := 3980191891338459861201985

theorem tailTrace_7751396 : CollatzResearch.WordTrace tailWord_7751396 prefixEnd_7751396 3980191891338459861201985 := by
  unfold tailWord_7751396
  simp only [CollatzResearch.WordTrace]
  refine ⟨141358319113011799943089021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188477758817349066590785361 141358319113011799943089021)
  ·
    refine ⟨53009369667379424978658383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141358319113011799943089021 53009369667379424978658383)
    ·
      refine ⟨79514054501069137467987575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53009369667379424978658383 79514054501069137467987575)
      ·
        refine ⟨119271081751603706201981363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79514054501069137467987575 119271081751603706201981363)
        ·
          refine ⟨178906622627405559302972045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119271081751603706201981363 178906622627405559302972045)
          ·
            refine ⟨67089983485277084738614517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178906622627405559302972045 67089983485277084738614517)
            ·
              refine ⟨6289685951744726694245111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67089983485277084738614517 6289685951744726694245111)
              ·
                refine ⟨9434528927617090041367667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6289685951744726694245111 9434528927617090041367667)
                ·
                  refine ⟨14151793391425635062051501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9434528927617090041367667 14151793391425635062051501)
                  ·
                    refine ⟨5306922521784613148269313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14151793391425635062051501 5306922521784613148269313)
                    ·
                      refine ⟨3980191891338459861201985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5306922521784613148269313 3980191891338459861201985)
                      ·
                        rfl

theorem cell23_7751396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 1, 3, 2].length) (baseStart_7751396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751396 prefixEnd_7751396 := by exact prefixLift 7751396
  have htrace : WordTrace (prefixWord ++ tailWord_7751396) baseStart_7751396 baseEnd_7751396 := by
    simpa [prefixWord, tailWord_7751396, baseEnd_7751396] using wordTrace_append hprefix tailTrace_7751396
  have hstable : (prefixWord ++ tailWord_7751396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751396).length < 2 ^ (prefixWord ++ tailWord_7751396).sum := by decide
  have hdescent : baseEnd_7751396 < baseStart_7751396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751426 : List Nat := [3, 4, 1, 1, 1, 1, 4, 1, 1, 4, 2]
def baseStart_7751426 : Nat := 118140960795 + 7751426 * 2 ^ 59
def prefixEnd_7751426 : Nat := 4983230072969 + 3 ^ 40 * 7751426 * 2
def baseEnd_7751426 : Nat := 3980207295758094743826847

theorem tailTrace_7751426 : CollatzResearch.WordTrace tailWord_7751426 prefixEnd_7751426 3980207295758094743826847 := by
  unfold tailWord_7751426
  simp only [CollatzResearch.WordTrace]
  refine ⟨70679433103978728752442533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188478488277276610006513421 70679433103978728752442533)
  ·
    refine ⟨13252393706996011641082975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70679433103978728752442533 13252393706996011641082975)
    ·
      refine ⟨19878590560494017461624463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13252393706996011641082975 19878590560494017461624463)
      ·
        refine ⟨29817885840741026192436695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19878590560494017461624463 29817885840741026192436695)
        ·
          refine ⟨44726828761111539288655043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29817885840741026192436695 44726828761111539288655043)
          ·
            refine ⟨67090243141667308932982565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44726828761111539288655043 67090243141667308932982565)
            ·
              refine ⟨12579420589062620424934231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67090243141667308932982565 12579420589062620424934231)
              ·
                refine ⟨18869130883593930637401347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12579420589062620424934231 18869130883593930637401347)
                ·
                  refine ⟨28303696325390895956102021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18869130883593930637401347 28303696325390895956102021)
                  ·
                    refine ⟨5306943061010792991769129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28303696325390895956102021 5306943061010792991769129)
                    ·
                      refine ⟨3980207295758094743826847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5306943061010792991769129 3980207295758094743826847)
                      ·
                        rfl

theorem cell23_7751426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_7751426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751426 prefixEnd_7751426 := by exact prefixLift 7751426
  have htrace : WordTrace (prefixWord ++ tailWord_7751426) baseStart_7751426 baseEnd_7751426 := by
    simpa [prefixWord, tailWord_7751426, baseEnd_7751426] using wordTrace_append hprefix tailTrace_7751426
  have hstable : (prefixWord ++ tailWord_7751426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751426).length < 2 ^ (prefixWord ++ tailWord_7751426).sum := by decide
  have hdescent : baseEnd_7751426 < baseStart_7751426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751465 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 5, 3, 4]
def baseStart_7751465 : Nat := 118140960795 + 7751465 * 2 ^ 59
def prefixEnd_7751465 : Nat := 4983230072969 + 3 ^ 40 * 7751465 * 2
def baseEnd_7751465 : Nat := 3980227321503620091239167

theorem tailTrace_7751465 : CollatzResearch.WordTrace tailWord_7751465 prefixEnd_7751465 3980227321503620091239167 := by
  unfold tailWord_7751465
  simp only [CollatzResearch.WordTrace]
  refine ⟨282719154862773624670439849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188479436575182416446959899 282719154862773624670439849)
  ·
    refine ⟨212039366147080218502829887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282719154862773624670439849 212039366147080218502829887)
    ·
      refine ⟨318059049220620327754244831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212039366147080218502829887 318059049220620327754244831)
      ·
        refine ⟨477088573830930491631367247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318059049220620327754244831 477088573830930491631367247)
        ·
          refine ⟨715632860746395737447050871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477088573830930491631367247 715632860746395737447050871)
          ·
            refine ⟨1073449291119593606170576307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715632860746395737447050871 1073449291119593606170576307)
            ·
              refine ⟨1610173936679390409255864461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1073449291119593606170576307 1610173936679390409255864461)
              ·
                refine ⟨603815226254771403470949173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1610173936679390409255864461 603815226254771403470949173)
                ·
                  refine ⟨56607677461384819075401485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 603815226254771403470949173 56607677461384819075401485)
                  ·
                    refine ⟨21227879048019307153275557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56607677461384819075401485 21227879048019307153275557)
                    ·
                      refine ⟨3980227321503620091239167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21227879048019307153275557 3980227321503620091239167)
                      ·
                        rfl

theorem cell23_7751465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 3, 4].length) (baseStart_7751465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751465 prefixEnd_7751465 := by exact prefixLift 7751465
  have htrace : WordTrace (prefixWord ++ tailWord_7751465) baseStart_7751465 baseEnd_7751465 := by
    simpa [prefixWord, tailWord_7751465, baseEnd_7751465] using wordTrace_append hprefix tailTrace_7751465
  have hstable : (prefixWord ++ tailWord_7751465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751465).length < 2 ^ (prefixWord ++ tailWord_7751465).sum := by decide
  have hdescent : baseEnd_7751465 < baseStart_7751465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751482 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4]
def baseStart_7751482 : Nat := 118140960795 + 7751482 * 2 ^ 59
def prefixEnd_7751482 : Nat := 4983230072969 + 3 ^ 40 * 7751482 * 2
def baseEnd_7751482 : Nat := 3980236050674746524726589

theorem tailTrace_7751482 : CollatzResearch.WordTrace tailWord_7751482 prefixEnd_7751482 3980236050674746524726589 := by
  unfold tailWord_7751482
  simp only [CollatzResearch.WordTrace]
  refine ⟨70679943725928009143452175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188479849935808024382539133 70679943725928009143452175)
  ·
    refine ⟨106019915588892013715178263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70679943725928009143452175 106019915588892013715178263)
    ·
      refine ⟨159029873383338020572767395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106019915588892013715178263 159029873383338020572767395)
      ·
        refine ⟨238544810075007030859151093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159029873383338020572767395 238544810075007030859151093)
        ·
          refine ⟨22363575944531909143045415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 238544810075007030859151093 22363575944531909143045415)
          ·
            refine ⟨33545363916797863714568123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22363575944531909143045415 33545363916797863714568123)
            ·
              refine ⟨50318045875196795571852185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33545363916797863714568123 50318045875196795571852185)
              ·
                refine ⟨37738534406397596678889139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50318045875196795571852185 37738534406397596678889139)
                ·
                  refine ⟨56607801609596395018333709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37738534406397596678889139 56607801609596395018333709)
                  ·
                    refine ⟨21227925603598648131875141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56607801609596395018333709 21227925603598648131875141)
                    ·
                      refine ⟨3980236050674746524726589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21227925603598648131875141 3980236050674746524726589)
                      ·
                        rfl

theorem cell23_7751482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_7751482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751482 prefixEnd_7751482 := by exact prefixLift 7751482
  have htrace : WordTrace (prefixWord ++ tailWord_7751482) baseStart_7751482 baseEnd_7751482 := by
    simpa [prefixWord, tailWord_7751482, baseEnd_7751482] using wordTrace_append hprefix tailTrace_7751482
  have hstable : (prefixWord ++ tailWord_7751482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751482).length < 2 ^ (prefixWord ++ tailWord_7751482).sum := by decide
  have hdescent : baseEnd_7751482 < baseStart_7751482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751516 : List Nat := [2, 2, 4, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_7751516 : Nat := 118140960795 + 7751516 * 2 ^ 59
def prefixEnd_7751516 : Nat := 4983230072969 + 3 ^ 40 * 7751516 * 2
def baseEnd_7751516 : Nat := 3980253509016999391701433

theorem tailTrace_7751516 : CollatzResearch.WordTrace tailWord_7751516 prefixEnd_7751516 3980253509016999391701433 := by
  unfold tailWord_7751516
  simp only [CollatzResearch.WordTrace]
  refine ⟨141360507492794430190273201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188480676657059240253697601 141360507492794430190273201)
  ·
    refine ⟨106020380619595822642704901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141360507492794430190273201 106020380619595822642704901)
    ·
      refine ⟨19878821366174216745507169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106020380619595822642704901 19878821366174216745507169)
      ·
        refine ⟨14909116024630662559130377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19878821366174216745507169 14909116024630662559130377)
        ·
          refine ⟨11181837018472996919347783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14909116024630662559130377 11181837018472996919347783)
          ·
            refine ⟨16772755527709495379021675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11181837018472996919347783 16772755527709495379021675)
            ·
              refine ⟨25159133291564243068532513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16772755527709495379021675 25159133291564243068532513)
              ·
                refine ⟨18869349968673182301399385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25159133291564243068532513 18869349968673182301399385)
                ·
                  refine ⟨14152012476504886726049539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18869349968673182301399385 14152012476504886726049539)
                  ·
                    refine ⟨21228018714757330089074309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14152012476504886726049539 21228018714757330089074309)
                    ·
                      refine ⟨3980253509016999391701433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21228018714757330089074309 3980253509016999391701433)
                      ·
                        rfl

theorem cell23_7751516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_7751516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751516 prefixEnd_7751516 := by exact prefixLift 7751516
  have htrace : WordTrace (prefixWord ++ tailWord_7751516) baseStart_7751516 baseEnd_7751516 := by
    simpa [prefixWord, tailWord_7751516, baseEnd_7751516] using wordTrace_append hprefix tailTrace_7751516
  have hstable : (prefixWord ++ tailWord_7751516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751516).length < 2 ^ (prefixWord ++ tailWord_7751516).sum := by decide
  have hdescent : baseEnd_7751516 < baseStart_7751516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751519 : List Nat := [1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 3]
def baseStart_7751519 : Nat := 118140960795 + 7751519 * 2 ^ 59
def prefixEnd_7751519 : Nat := 4983230072969 + 3 ^ 40 * 7751519 * 2
def baseEnd_7751519 : Nat := 3980255049458962879963919

theorem tailTrace_7751519 : CollatzResearch.WordTrace tailWord_7751519 prefixEnd_7751519 3980255049458962879963919 := by
  unfold tailWord_7751519
  simp only [CollatzResearch.WordTrace]
  refine ⟨282721124404577991892905611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188480749603051994595270407 282721124404577991892905611)
  ·
    refine ⟨424081686606866987839358417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282721124404577991892905611 424081686606866987839358417)
    ·
      refine ⟨318061264955150240879518813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424081686606866987839358417 318061264955150240879518813)
      ·
        refine ⟨119272974358181340329819555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318061264955150240879518813 119272974358181340329819555)
        ·
          refine ⟨178909461537272010494729333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119272974358181340329819555 178909461537272010494729333)
          ·
            refine ⟨16772762019119250983880875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178909461537272010494729333 16772762019119250983880875)
            ·
              refine ⟨25159143028678876475821313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16772762019119250983880875 25159143028678876475821313)
              ·
                refine ⟨18869357271509157356865985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25159143028678876475821313 18869357271509157356865985)
                ·
                  refine ⟨14152017953631868017649489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18869357271509157356865985 14152017953631868017649489)
                  ·
                    refine ⟨10614013465223901013237117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14152017953631868017649489 10614013465223901013237117)
                    ·
                      refine ⟨3980255049458962879963919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10614013465223901013237117 3980255049458962879963919)
                      ·
                        rfl

theorem cell23_7751519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_7751519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751519 prefixEnd_7751519 := by exact prefixLift 7751519
  have htrace : WordTrace (prefixWord ++ tailWord_7751519) baseStart_7751519 baseEnd_7751519 := by
    simpa [prefixWord, tailWord_7751519, baseEnd_7751519] using wordTrace_append hprefix tailTrace_7751519
  have hstable : (prefixWord ++ tailWord_7751519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751519).length < 2 ^ (prefixWord ++ tailWord_7751519).sum := by decide
  have hdescent : baseEnd_7751519 < baseStart_7751519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751535 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 1, 11]
def baseStart_7751535 : Nat := 118140960795 + 7751535 * 2 ^ 59
def prefixEnd_7751535 : Nat := 4983230072969 + 3 ^ 40 * 7751535 * 2
def baseEnd_7751535 : Nat := 1326754421716478272454615

theorem tailTrace_7751535 : CollatzResearch.WordTrace tailWord_7751535 prefixEnd_7751535 1326754421716478272454615 := by
  unfold tailWord_7751535
  simp only [CollatzResearch.WordTrace]
  refine ⟨282721707972520026625488059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188481138648346684416992039 282721707972520026625488059)
  ·
    refine ⟨424082561958780039938232089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282721707972520026625488059 424082561958780039938232089)
    ·
      refine ⟨318061921469085029953674067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424082561958780039938232089 318061921469085029953674067)
      ·
        refine ⟨477092882203627544930511101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318061921469085029953674067 477092882203627544930511101)
        ·
          refine ⟨178909830826360329348941663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 477092882203627544930511101 178909830826360329348941663)
          ·
            refine ⟨268364746239540494023412495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178909830826360329348941663 268364746239540494023412495)
            ·
              refine ⟨402547119359310741035118743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268364746239540494023412495 402547119359310741035118743)
              ·
                refine ⟨603820679038966111552678115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402547119359310741035118743 603820679038966111552678115)
                ·
                  refine ⟨905731018558449167329017173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 603820679038966111552678115 905731018558449167329017173)
                  ·
                    refine ⟨1326754421716478272454615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 905731018558449167329017173 1326754421716478272454615)
                    ·
                      rfl

theorem cell23_7751535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 11].length) (baseStart_7751535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751535 prefixEnd_7751535 := by exact prefixLift 7751535
  have htrace : WordTrace (prefixWord ++ tailWord_7751535) baseStart_7751535 baseEnd_7751535 := by
    simpa [prefixWord, tailWord_7751535, baseEnd_7751535] using wordTrace_append hprefix tailTrace_7751535
  have hstable : (prefixWord ++ tailWord_7751535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751535).length < 2 ^ (prefixWord ++ tailWord_7751535).sum := by decide
  have hdescent : baseEnd_7751535 < baseStart_7751535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751549 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 5, 1, 3]
def baseStart_7751549 : Nat := 118140960795 + 7751549 * 2 ^ 59
def prefixEnd_7751549 : Nat := 4983230072969 + 3 ^ 40 * 7751549 * 2
def baseEnd_7751549 : Nat := 3980270453878597762588781

theorem tailTrace_7751549 : CollatzResearch.WordTrace tailWord_7751549 prefixEnd_7751549 3980270453878597762588781 := by
  unfold tailWord_7751549
  simp only [CollatzResearch.WordTrace]
  refine ⟨282722218594469307016497701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188481479062979538010998467 282722218594469307016497701)
  ·
    refine ⟨53010415986462995065593319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282722218594469307016497701 53010415986462995065593319)
    ·
      refine ⟨79515623979694492598389979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53010415986462995065593319 79515623979694492598389979)
      ·
        refine ⟨119273435969541738897584969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79515623979694492598389979 119273435969541738897584969)
        ·
          refine ⟨89455076977156304173188727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119273435969541738897584969 89455076977156304173188727)
          ·
            refine ⟨134182615465734456259783091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89455076977156304173188727 134182615465734456259783091)
            ·
              refine ⟨201273923198601684389674637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134182615465734456259783091 201273923198601684389674637)
              ·
                refine ⟨75477721199475631646127989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201273923198601684389674637 75477721199475631646127989)
                ·
                  refine ⟨7076036362450840466824499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75477721199475631646127989 7076036362450840466824499)
                  ·
                    refine ⟨10614054543676260700236749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7076036362450840466824499 10614054543676260700236749)
                    ·
                      refine ⟨3980270453878597762588781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10614054543676260700236749 3980270453878597762588781)
                      ·
                        rfl

theorem cell23_7751549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_7751549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751549 prefixEnd_7751549 := by exact prefixLift 7751549
  have htrace : WordTrace (prefixWord ++ tailWord_7751549) baseStart_7751549 baseEnd_7751549 := by
    simpa [prefixWord, tailWord_7751549, baseEnd_7751549] using wordTrace_append hprefix tailTrace_7751549
  have hstable : (prefixWord ++ tailWord_7751549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751549).length < 2 ^ (prefixWord ++ tailWord_7751549).sum := by decide
  have hdescent : baseEnd_7751549 < baseStart_7751549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751552 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 3, 5]
def baseStart_7751552 : Nat := 118140960795 + 7751552 * 2 ^ 59
def prefixEnd_7751552 : Nat := 4983230072969 + 3 ^ 40 * 7751552 * 2
def baseEnd_7751552 : Nat := 1326757331440187083617089

theorem tailTrace_7751552 : CollatzResearch.WordTrace tailWord_7751552 prefixEnd_7751552 1326757331440187083617089 := by
  unfold tailWord_7751552
  simp only [CollatzResearch.WordTrace]
  refine ⟨141361164006729219264428455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188481552008972292352571273 141361164006729219264428455)
  ·
    refine ⟨212041746010093828896642683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141361164006729219264428455 212041746010093828896642683)
    ·
      refine ⟨318062619015140743344964025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212041746010093828896642683 318062619015140743344964025)
      ·
        refine ⟨238546964261355557508723019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318062619015140743344964025 238546964261355557508723019)
        ·
          refine ⟨357820446392033336263084529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238546964261355557508723019 357820446392033336263084529)
          ·
            refine ⟨268365334794025002197313397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357820446392033336263084529 268365334794025002197313397)
            ·
              refine ⟨25159250136939843955998131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 268365334794025002197313397 25159250136939843955998131)
              ·
                refine ⟨37738875205409765933997197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25159250136939843955998131 37738875205409765933997197)
                ·
                  refine ⟨14152078202028662225248949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37738875205409765933997197 14152078202028662225248949)
                  ·
                    refine ⟨1326757331440187083617089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14152078202028662225248949 1326757331440187083617089)
                    ·
                      rfl

theorem cell23_7751552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 3, 5].length) (baseStart_7751552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751552 prefixEnd_7751552 := by exact prefixLift 7751552
  have htrace : WordTrace (prefixWord ++ tailWord_7751552) baseStart_7751552 baseEnd_7751552 := by
    simpa [prefixWord, tailWord_7751552, baseEnd_7751552] using wordTrace_append hprefix tailTrace_7751552
  have hstable : (prefixWord ++ tailWord_7751552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751552).length < 2 ^ (prefixWord ++ tailWord_7751552).sum := by decide
  have hdescent : baseEnd_7751552 < baseStart_7751552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751553 : List Nat := [1, 2, 4, 4, 1, 1, 2, 1, 2, 2, 3]
def baseStart_7751553 : Nat := 118140960795 + 7751553 * 2 ^ 59
def prefixEnd_7751553 : Nat := 4983230072969 + 3 ^ 40 * 7751553 * 2
def baseEnd_7751553 : Nat := 3980272507801215746938763

theorem tailTrace_7751553 : CollatzResearch.WordTrace tailWord_7751553 prefixEnd_7751553 3980272507801215746938763 := by
  unfold tailWord_7751553
  simp only [CollatzResearch.WordTrace]
  refine ⟨282722364486454815699643313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188481576324303210466428875 282722364486454815699643313)
  ·
    refine ⟨212041773364841111774732485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282722364486454815699643313 212041773364841111774732485)
    ·
      refine ⟨39757832505907708457762341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212041773364841111774732485 39757832505907708457762341)
      ·
        refine ⟨7454593594857695335830439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39757832505907708457762341 7454593594857695335830439)
        ·
          refine ⟨11181890392286543003745659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7454593594857695335830439 11181890392286543003745659)
          ·
            refine ⟨16772835588429814505618489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11181890392286543003745659 16772835588429814505618489)
            ·
              refine ⟨12579626691322360879213867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16772835588429814505618489 12579626691322360879213867)
              ·
                refine ⟨18869440036983541318820801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12579626691322360879213867 18869440036983541318820801)
                ·
                  refine ⟨14152080027737655989115601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18869440036983541318820801 14152080027737655989115601)
                  ·
                    refine ⟨10614060020803241991836701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14152080027737655989115601 10614060020803241991836701)
                    ·
                      refine ⟨3980272507801215746938763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10614060020803241991836701 3980272507801215746938763)
                      ·
                        rfl

theorem cell23_7751553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_7751553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751553 prefixEnd_7751553 := by exact prefixLift 7751553
  have htrace : WordTrace (prefixWord ++ tailWord_7751553) baseStart_7751553 baseEnd_7751553 := by
    simpa [prefixWord, tailWord_7751553, baseEnd_7751553] using wordTrace_append hprefix tailTrace_7751553
  have hstable : (prefixWord ++ tailWord_7751553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751553).length < 2 ^ (prefixWord ++ tailWord_7751553).sum := by decide
  have hdescent : baseEnd_7751553 < baseStart_7751553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751599 : List Nat := [1, 1, 2, 1, 2, 2, 3, 5, 2, 4]
def baseStart_7751599 : Nat := 118140960795 + 7751599 * 2 ^ 59
def prefixEnd_7751599 : Nat := 4983230072969 + 3 ^ 40 * 7751599 * 2
def baseEnd_7751599 : Nat := 1326765375970440855654517

theorem tailTrace_7751599 : CollatzResearch.WordTrace tailWord_7751599 prefixEnd_7751599 1326765375970440855654517 := by
  unfold tailWord_7751599
  simp only [CollatzResearch.WordTrace]
  refine ⟨282724042244288165555817851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188482694829525443703878567 282724042244288165555817851)
  ·
    refine ⟨424086063366432248333726777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282724042244288165555817851 424086063366432248333726777)
    ·
      refine ⟨318064547524824186250295083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424086063366432248333726777 318064547524824186250295083)
      ·
        refine ⟨477096821287236279375442625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318064547524824186250295083 477096821287236279375442625)
        ·
          refine ⟨357822615965427209531581969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477096821287236279375442625 357822615965427209531581969)
          ·
            refine ⟨268366961974070407148686477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357822615965427209531581969 268366961974070407148686477)
            ·
              refine ⟨100637610740276402680757429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268366961974070407148686477 100637610740276402680757429)
              ·
                refine ⟨9434776006900912751321009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100637610740276402680757429 9434776006900912751321009)
                ·
                  refine ⟨7076082005175684563490757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9434776006900912751321009 7076082005175684563490757)
                  ·
                    refine ⟨1326765375970440855654517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7076082005175684563490757 1326765375970440855654517)
                    ·
                      rfl

theorem cell23_7751599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 4].length) (baseStart_7751599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751599 prefixEnd_7751599 := by exact prefixLift 7751599
  have htrace : WordTrace (prefixWord ++ tailWord_7751599) baseStart_7751599 baseEnd_7751599 := by
    simpa [prefixWord, tailWord_7751599, baseEnd_7751599] using wordTrace_append hprefix tailTrace_7751599
  have hstable : (prefixWord ++ tailWord_7751599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751599).length < 2 ^ (prefixWord ++ tailWord_7751599).sum := by decide
  have hdescent : baseEnd_7751599 < baseStart_7751599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751602 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6]
def baseStart_7751602 : Nat := 118140960795 + 7751602 * 2 ^ 59
def prefixEnd_7751602 : Nat := 4983230072969 + 3 ^ 40 * 7751602 * 2
def baseEnd_7751602 : Nat := 3980297668353286055226037

theorem tailTrace_7751602 : CollatzResearch.WordTrace tailWord_7751602 prefixEnd_7751602 3980297668353286055226037 := by
  unfold tailWord_7751602
  simp only [CollatzResearch.WordTrace]
  refine ⟨70681037915819324267044265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188482767775518198045451373 70681037915819324267044265)
  ·
    refine ⟨53010778436864493200283199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70681037915819324267044265 53010778436864493200283199)
    ·
      refine ⟨79516167655296739800424799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53010778436864493200283199 79516167655296739800424799)
      ·
        refine ⟨119274251482945109700637199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79516167655296739800424799 119274251482945109700637199)
        ·
          refine ⟨178911377224417664550955799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119274251482945109700637199 178911377224417664550955799)
          ·
            refine ⟨268367065836626496826433699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178911377224417664550955799 268367065836626496826433699)
            ·
              refine ⟨402550598754939745239650549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268367065836626496826433699 402550598754939745239650549)
              ·
                refine ⟨37739118633275601116217239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 402550598754939745239650549 37739118633275601116217239)
                ·
                  refine ⟨56608677949913401674325859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37739118633275601116217239 56608677949913401674325859)
                  ·
                    refine ⟨84913016924870102511488789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56608677949913401674325859 84913016924870102511488789)
                    ·
                      refine ⟨3980297668353286055226037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84913016924870102511488789 3980297668353286055226037)
                      ·
                        rfl

theorem cell23_7751602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_7751602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751602 prefixEnd_7751602 := by exact prefixLift 7751602
  have htrace : WordTrace (prefixWord ++ tailWord_7751602) baseStart_7751602 baseEnd_7751602 := by
    simpa [prefixWord, tailWord_7751602, baseEnd_7751602] using wordTrace_append hprefix tailTrace_7751602
  have hstable : (prefixWord ++ tailWord_7751602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751602).length < 2 ^ (prefixWord ++ tailWord_7751602).sum := by decide
  have hdescent : baseEnd_7751602 < baseStart_7751602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751609 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 3, 2, 3]
def baseStart_7751609 : Nat := 118140960795 + 7751609 * 2 ^ 59
def prefixEnd_7751609 : Nat := 4983230072969 + 3 ^ 40 * 7751609 * 2
def baseEnd_7751609 : Nat := 3980301262717867527838505

theorem tailTrace_7751609 : CollatzResearch.WordTrace tailWord_7751609 prefixEnd_7751609 3980301262717867527838505 := by
  unfold tailWord_7751609
  simp only [CollatzResearch.WordTrace]
  refine ⟨282724406974251937263681881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188482937982834624842454587 282724406974251937263681881)
  ·
    refine ⟨212043305230688952947761411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282724406974251937263681881 212043305230688952947761411)
    ·
      refine ⟨318064957846033429421642117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212043305230688952947761411 318064957846033429421642117)
      ·
        refine ⟨59637179596131268016557897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318064957846033429421642117 59637179596131268016557897)
        ·
          refine ⟨44727884697098451012418423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59637179596131268016557897 44727884697098451012418423)
          ·
            refine ⟨67091827045647676518627635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44727884697098451012418423 67091827045647676518627635)
            ·
              refine ⟨100637740568471514777941453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67091827045647676518627635 100637740568471514777941453)
              ·
                refine ⟨37739152713176818041728045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100637740568471514777941453 37739152713176818041728045)
                ·
                  refine ⟨14152182267441306765648017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37739152713176818041728045 14152182267441306765648017)
                  ·
                    refine ⟨10614136700580980074236013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14152182267441306765648017 10614136700580980074236013)
                    ·
                      refine ⟨3980301262717867527838505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10614136700580980074236013 3980301262717867527838505)
                      ·
                        rfl

theorem cell23_7751609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_7751609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751609 prefixEnd_7751609 := by exact prefixLift 7751609
  have htrace : WordTrace (prefixWord ++ tailWord_7751609) baseStart_7751609 baseEnd_7751609 := by
    simpa [prefixWord, tailWord_7751609, baseEnd_7751609] using wordTrace_append hprefix tailTrace_7751609
  have hstable : (prefixWord ++ tailWord_7751609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751609).length < 2 ^ (prefixWord ++ tailWord_7751609).sum := by decide
  have hdescent : baseEnd_7751609 < baseStart_7751609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751650 : List Nat := [3, 3, 3, 1, 3, 1, 1, 1, 1, 6]
def baseStart_7751650 : Nat := 118140960795 + 7751650 * 2 ^ 59
def prefixEnd_7751650 : Nat := 4983230072969 + 3 ^ 40 * 7751650 * 2
def baseEnd_7751650 : Nat := 1326774105141567289141939

theorem tailTrace_7751650 : CollatzResearch.WordTrace tailWord_7751650 prefixEnd_7751650 1326774105141567289141939 := by
  unfold tailWord_7751650
  simp only [CollatzResearch.WordTrace]
  refine ⟨70681475591775850316481101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188483934911402267510616269 70681475591775850316481101)
  ·
    refine ⟨26505553346915943868680413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70681475591775850316481101 26505553346915943868680413)
    ·
      refine ⟨9939582505093478950755155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26505553346915943868680413 9939582505093478950755155)
      ·
        refine ⟨14909373757640218426132733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9939582505093478950755155 14909373757640218426132733)
        ·
          refine ⟨5591015159115081909799775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14909373757640218426132733 5591015159115081909799775)
          ·
            refine ⟨8386522738672622864699663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5591015159115081909799775 8386522738672622864699663)
            ·
              refine ⟨12579784108008934297049495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8386522738672622864699663 12579784108008934297049495)
              ·
                refine ⟨18869676162013401445574243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12579784108008934297049495 18869676162013401445574243)
                ·
                  refine ⟨28304514243020102168361365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18869676162013401445574243 28304514243020102168361365)
                  ·
                    refine ⟨1326774105141567289141939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28304514243020102168361365 1326774105141567289141939)
                    ·
                      rfl

theorem cell23_7751650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_7751650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751650 prefixEnd_7751650 := by exact prefixLift 7751650
  have htrace : WordTrace (prefixWord ++ tailWord_7751650) baseStart_7751650 baseEnd_7751650 := by
    simpa [prefixWord, tailWord_7751650, baseEnd_7751650] using wordTrace_append hprefix tailTrace_7751650
  have hstable : (prefixWord ++ tailWord_7751650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751650).length < 2 ^ (prefixWord ++ tailWord_7751650).sum := by decide
  have hdescent : baseEnd_7751650 < baseStart_7751650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751672 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 1, 8]
def baseStart_7751672 : Nat := 118140960795 + 7751672 * 2 ^ 59
def prefixEnd_7751672 : Nat := 4983230072969 + 3 ^ 40 * 7751672 * 2
def baseEnd_7751672 : Nat := 1326777870666366927116905

theorem tailTrace_7751672 : CollatzResearch.WordTrace tailWord_7751672 prefixEnd_7751672 1326777870666366927116905 := by
  unfold tailWord_7751672
  simp only [CollatzResearch.WordTrace]
  refine ⟨141363352386511849511612635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188484469848682466015483513 141363352386511849511612635)
  ·
    refine ⟨212045028579767774267418953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141363352386511849511612635 212045028579767774267418953)
    ·
      refine ⟨159033771434825830700564215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212045028579767774267418953 159033771434825830700564215)
      ·
        refine ⟨238550657152238746050846323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159033771434825830700564215 238550657152238746050846323)
        ·
          refine ⟨357825985728358119076269485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238550657152238746050846323 357825985728358119076269485)
          ·
            refine ⟨134184744648134294653601057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357825985728358119076269485 134184744648134294653601057)
            ·
              refine ⟨100638558486100720990200793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134184744648134294653601057 100638558486100720990200793)
              ·
                refine ⟨75478918864575540742650595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100638558486100720990200793 75478918864575540742650595)
                ·
                  refine ⟨113218378296863311113975893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75478918864575540742650595 113218378296863311113975893)
                  ·
                    refine ⟨1326777870666366927116905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113218378296863311113975893 1326777870666366927116905)
                    ·
                      rfl

theorem cell23_7751672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_7751672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751672 prefixEnd_7751672 := by exact prefixLift 7751672
  have htrace : WordTrace (prefixWord ++ tailWord_7751672) baseStart_7751672 baseEnd_7751672 := by
    simpa [prefixWord, tailWord_7751672, baseEnd_7751672] using wordTrace_append hprefix tailTrace_7751672
  have hstable : (prefixWord ++ tailWord_7751672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751672).length < 2 ^ (prefixWord ++ tailWord_7751672).sum := by decide
  have hdescent : baseEnd_7751672 < baseStart_7751672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751756 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 2, 5, 2]
def baseStart_7751756 : Nat := 118140960795 + 7751756 * 2 ^ 59
def prefixEnd_7751756 : Nat := 4983230072969 + 3 ^ 40 * 7751756 * 2
def baseEnd_7751756 : Nat := 3980376744374078452700329

theorem tailTrace_7751756 : CollatzResearch.WordTrace tailWord_7751756 prefixEnd_7751756 3980376744374078452700329 := by
  unfold tailWord_7751756
  simp only [CollatzResearch.WordTrace]
  refine ⟨141364884252359690684641561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188486512336479587579522081 141364884252359690684641561)
  ·
    refine ⟨106023663189269768013481171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141364884252359690684641561 106023663189269768013481171)
    ·
      refine ⟨159035494783904652020221757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106023663189269768013481171 159035494783904652020221757)
      ·
        refine ⟨59638310543964244507583159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159035494783904652020221757 59638310543964244507583159)
        ·
          refine ⟨89457465815946366761374739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59638310543964244507583159 89457465815946366761374739)
          ·
            refine ⟨134186198723919550142062109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89457465815946366761374739 134186198723919550142062109)
            ·
              refine ⟨50319824521469831303273291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134186198723919550142062109 50319824521469831303273291)
              ·
                refine ⟨75479736782204746954909937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50319824521469831303273291 75479736782204746954909937)
                ·
                  refine ⟨56609802586653560216182453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75479736782204746954909937 56609802586653560216182453)
                  ·
                    refine ⟨5307168992498771270267105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56609802586653560216182453 5307168992498771270267105)
                    ·
                      refine ⟨3980376744374078452700329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5307168992498771270267105 3980376744374078452700329)
                      ·
                        rfl

theorem cell23_7751756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_7751756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751756 prefixEnd_7751756 := by exact prefixLift 7751756
  have htrace : WordTrace (prefixWord ++ tailWord_7751756) baseStart_7751756 baseEnd_7751756 := by
    simpa [prefixWord, tailWord_7751756, baseEnd_7751756] using wordTrace_append hprefix tailTrace_7751756
  have hstable : (prefixWord ++ tailWord_7751756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751756).length < 2 ^ (prefixWord ++ tailWord_7751756).sum := by decide
  have hdescent : baseEnd_7751756 < baseStart_7751756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751769 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 1, 3, 4]
def baseStart_7751769 : Nat := 118140960795 + 7751769 * 2 ^ 59
def prefixEnd_7751769 : Nat := 4983230072969 + 3 ^ 40 * 7751769 * 2
def baseEnd_7751769 : Nat := 3980383419622586901837769

theorem tailTrace_7751769 : CollatzResearch.WordTrace tailWord_7751769 prefixEnd_7751769 3980383419622586901837769 := by
  unfold tailWord_7751769
  simp only [CollatzResearch.WordTrace]
  refine ⟨282730242653672284589506361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188486828435781523059670907 282730242653672284589506361)
  ·
    refine ⟨212047681990254213442129771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282730242653672284589506361 212047681990254213442129771)
    ·
      refine ⟨318071522985381320163194657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212047681990254213442129771 318071522985381320163194657)
      ·
        refine ⟨238553642239035990122395993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318071522985381320163194657 238553642239035990122395993)
        ·
          refine ⟨178915231679276992591796995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238553642239035990122395993 178915231679276992591796995)
          ·
            refine ⟨268372847518915488887695493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178915231679276992591796995 268372847518915488887695493)
            ·
              refine ⟨50319908909796654166442905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268372847518915488887695493 50319908909796654166442905)
              ·
                refine ⟨37739931682347490624832179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50319908909796654166442905 37739931682347490624832179)
                ·
                  refine ⟨56609897523521235937248269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37739931682347490624832179 56609897523521235937248269)
                  ·
                    refine ⟨21228711571320463476468101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56609897523521235937248269 21228711571320463476468101)
                    ·
                      refine ⟨3980383419622586901837769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21228711571320463476468101 3980383419622586901837769)
                      ·
                        rfl

theorem cell23_7751769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_7751769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751769 prefixEnd_7751769 := by exact prefixLift 7751769
  have htrace : WordTrace (prefixWord ++ tailWord_7751769) baseStart_7751769 baseEnd_7751769 := by
    simpa [prefixWord, tailWord_7751769, baseEnd_7751769] using wordTrace_append hprefix tailTrace_7751769
  have hstable : (prefixWord ++ tailWord_7751769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751769).length < 2 ^ (prefixWord ++ tailWord_7751769).sum := by decide
  have hdescent : baseEnd_7751769 < baseStart_7751769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751799 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 6]
def baseStart_7751799 : Nat := 118140960795 + 7751799 * 2 ^ 59
def prefixEnd_7751799 : Nat := 4983230072969 + 3 ^ 40 * 7751799 * 2
def baseEnd_7751799 : Nat := 3980398824042221784462631

theorem tailTrace_7751799 : CollatzResearch.WordTrace tailWord_7751799 prefixEnd_7751799 3980398824042221784462631 := by
  unfold tailWord_7751799
  simp only [CollatzResearch.WordTrace]
  refine ⟨282731336843563599713098451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188487557895709066475398967 282731336843563599713098451)
  ·
    refine ⟨424097005265345399569647677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282731336843563599713098451 424097005265345399569647677)
    ·
      refine ⟨159036376974504524838617879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424097005265345399569647677 159036376974504524838617879)
      ·
        refine ⟨238554565461756787257926819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159036376974504524838617879 238554565461756787257926819)
        ·
          refine ⟨357831848192635180886890229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238554565461756787257926819 357831848192635180886890229)
          ·
            refine ⟨33546735768059548208145959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 357831848192635180886890229 33546735768059548208145959)
            ·
              refine ⟨50320103652089322312218939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33546735768059548208145959 50320103652089322312218939)
              ·
                refine ⟨75480155478133983468328409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50320103652089322312218939 75480155478133983468328409)
                ·
                  refine ⟨56610116608600487601246307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75480155478133983468328409 56610116608600487601246307)
                  ·
                    refine ⟨84915174912900731401869461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56610116608600487601246307 84915174912900731401869461)
                    ·
                      refine ⟨3980398824042221784462631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84915174912900731401869461 3980398824042221784462631)
                      ·
                        rfl

theorem cell23_7751799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_7751799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751799 prefixEnd_7751799 := by exact prefixLift 7751799
  have htrace : WordTrace (prefixWord ++ tailWord_7751799) baseStart_7751799 baseEnd_7751799 := by
    simpa [prefixWord, tailWord_7751799, baseEnd_7751799] using wordTrace_append hprefix tailTrace_7751799
  have hstable : (prefixWord ++ tailWord_7751799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751799).length < 2 ^ (prefixWord ++ tailWord_7751799).sum := by decide
  have hdescent : baseEnd_7751799 < baseStart_7751799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751813 : List Nat := [1, 3, 1, 1, 5, 2, 2, 1, 3, 4]
def baseStart_7751813 : Nat := 118140960795 + 7751813 * 2 ^ 59
def prefixEnd_7751813 : Nat := 4983230072969 + 3 ^ 40 * 7751813 * 2
def baseEnd_7751813 : Nat := 1326802004257128243229189

theorem tailTrace_7751813 : CollatzResearch.WordTrace tailWord_7751813 prefixEnd_7751813 1326802004257128243229189 := by
  unfold tailWord_7751813
  simp only [CollatzResearch.WordTrace]
  refine ⟨282731847465512880104108093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188487898310341920069405395 282731847465512880104108093)
  ·
    refine ⟨106024442799567330039040535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282731847465512880104108093 106024442799567330039040535)
    ·
      refine ⟨159036664199350995058560803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106024442799567330039040535 159036664199350995058560803)
      ·
        refine ⟨238554996299026492587841205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159036664199350995058560803 238554996299026492587841205)
        ·
          refine ⟨22364530903033733680110113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 238554996299026492587841205 22364530903033733680110113)
          ·
            refine ⟨16773398177275300260082585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22364530903033733680110113 16773398177275300260082585)
            ·
              refine ⟨12580048632956475195061939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16773398177275300260082585 12580048632956475195061939)
              ·
                refine ⟨18870072949434712792592909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12580048632956475195061939 18870072949434712792592909)
                ·
                  refine ⟨7076277356038017297222341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18870072949434712792592909 7076277356038017297222341)
                  ·
                    refine ⟨1326802004257128243229189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7076277356038017297222341 1326802004257128243229189)
                    ·
                      rfl

theorem cell23_7751813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 4].length) (baseStart_7751813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751813 prefixEnd_7751813 := by exact prefixLift 7751813
  have htrace : WordTrace (prefixWord ++ tailWord_7751813) baseStart_7751813 baseEnd_7751813 := by
    simpa [prefixWord, tailWord_7751813, baseEnd_7751813] using wordTrace_append hprefix tailTrace_7751813
  have hstable : (prefixWord ++ tailWord_7751813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751813).length < 2 ^ (prefixWord ++ tailWord_7751813).sum := by decide
  have hdescent : baseEnd_7751813 < baseStart_7751813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751829 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 1, 2, 6]
def baseStart_7751829 : Nat := 118140960795 + 7751829 * 2 ^ 59
def prefixEnd_7751829 : Nat := 4983230072969 + 3 ^ 40 * 7751829 * 2
def baseEnd_7751829 : Nat := 3980414228461856667087493

theorem tailTrace_7751829 : CollatzResearch.WordTrace tailWord_7751829 prefixEnd_7751829 3980414228461856667087493 := by
  unfold tailWord_7751829
  simp only [CollatzResearch.WordTrace]
  refine ⟨282732431033454914836690541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188488287355636609891127027 282732431033454914836690541)
  ·
    refine ⟨106024661637545593063758953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282732431033454914836690541 106024661637545593063758953)
    ·
      refine ⟨79518496228159194797819215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106024661637545593063758953 79518496228159194797819215)
      ·
        refine ⟨119277744342238792196728823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79518496228159194797819215 119277744342238792196728823)
        ·
          refine ⟨178916616513358188295093235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119277744342238792196728823 178916616513358188295093235)
          ·
            refine ⟨268374924770037282442639853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178916616513358188295093235 268374924770037282442639853)
            ·
              refine ⟨100640596788763980915989945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268374924770037282442639853 100640596788763980915989945)
              ·
                refine ⟨75480447591572985686992459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100640596788763980915989945 75480447591572985686992459)
                ·
                  refine ⟨113220671387359478530488689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75480447591572985686992459 113220671387359478530488689)
                  ·
                    refine ⟨84915503540519608897866517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113220671387359478530488689 84915503540519608897866517)
                    ·
                      refine ⟨3980414228461856667087493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84915503540519608897866517 3980414228461856667087493)
                      ·
                        rfl

theorem cell23_7751829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_7751829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751829 prefixEnd_7751829 := by exact prefixLift 7751829
  have htrace : WordTrace (prefixWord ++ tailWord_7751829) baseStart_7751829 baseEnd_7751829 := by
    simpa [prefixWord, tailWord_7751829, baseEnd_7751829] using wordTrace_append hprefix tailTrace_7751829
  have hstable : (prefixWord ++ tailWord_7751829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751829).length < 2 ^ (prefixWord ++ tailWord_7751829).sum := by decide
  have hdescent : baseEnd_7751829 < baseStart_7751829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751836 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 2, 5, 3]
def baseStart_7751836 : Nat := 118140960795 + 7751836 * 2 ^ 59
def prefixEnd_7751836 : Nat := 4983230072969 + 3 ^ 40 * 7751836 * 2
def baseEnd_7751836 : Nat := 3980417822826438139699961

theorem tailTrace_7751836 : CollatzResearch.WordTrace tailWord_7751836 prefixEnd_7751836 3980417822826438139699961 := by
  unfold tailWord_7751836
  simp only [CollatzResearch.WordTrace]
  refine ⟨141366343172214777516097681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188488457562953036688130241 141366343172214777516097681)
  ·
    refine ⟨106024757379161083137073261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141366343172214777516097681 106024757379161083137073261)
    ·
      refine ⟨39759284017185406176402473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106024757379161083137073261 39759284017185406176402473)
      ·
        refine ⟨29819463012889054632301855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39759284017185406176402473 29819463012889054632301855)
        ·
          refine ⟨44729194519333581948452783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29819463012889054632301855 44729194519333581948452783)
          ·
            refine ⟨67093791779000372922679175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44729194519333581948452783 67093791779000372922679175)
            ·
              refine ⟨100640687668500559384018763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67093791779000372922679175 100640687668500559384018763)
              ·
                refine ⟨150961031502750839076028145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100640687668500559384018763 150961031502750839076028145)
                ·
                  refine ⟨113220773627063129307021109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150961031502750839076028145 113220773627063129307021109)
                  ·
                    refine ⟨10614447527537168372533229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113220773627063129307021109 10614447527537168372533229)
                    ·
                      refine ⟨3980417822826438139699961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10614447527537168372533229 3980417822826438139699961)
                      ·
                        rfl

theorem cell23_7751836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_7751836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751836 prefixEnd_7751836 := by exact prefixLift 7751836
  have htrace : WordTrace (prefixWord ++ tailWord_7751836) baseStart_7751836 baseEnd_7751836 := by
    simpa [prefixWord, tailWord_7751836, baseEnd_7751836] using wordTrace_append hprefix tailTrace_7751836
  have hstable : (prefixWord ++ tailWord_7751836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751836).length < 2 ^ (prefixWord ++ tailWord_7751836).sum := by decide
  have hdescent : baseEnd_7751836 < baseStart_7751836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751863 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 4, 3, 2]
def baseStart_7751863 : Nat := 118140960795 + 7751863 * 2 ^ 59
def prefixEnd_7751863 : Nat := 4983230072969 + 3 ^ 40 * 7751863 * 2
def baseEnd_7751863 : Nat := 3980431686804109534062337

theorem tailTrace_7751863 : CollatzResearch.WordTrace tailWord_7751863 prefixEnd_7751863 3980431686804109534062337 := by
  unfold tailWord_7751863
  simp only [CollatzResearch.WordTrace]
  refine ⟨282733671115331738643428243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188489114076887825762285495 282733671115331738643428243)
  ·
    refine ⟨424100506672997607965142365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282733671115331738643428243 424100506672997607965142365)
    ·
      refine ⟨159037690002374102986928387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424100506672997607965142365 159037690002374102986928387)
      ·
        refine ⟨238556535003561154480392581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159037690002374102986928387 238556535003561154480392581)
        ·
          refine ⟨44729350313167716465073609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238556535003561154480392581 44729350313167716465073609)
          ·
            refine ⟨33547012734875787348805207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44729350313167716465073609 33547012734875787348805207)
            ·
              refine ⟨50320519102313681023207811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33547012734875787348805207 50320519102313681023207811)
              ·
                refine ⟨75480778653470521534811717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50320519102313681023207811 75480778653470521534811717)
                ·
                  refine ⟨14152645997525722787777197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75480778653470521534811717 14152645997525722787777197)
                  ·
                    refine ⟨5307242249072146045416449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14152645997525722787777197 5307242249072146045416449)
                    ·
                      refine ⟨3980431686804109534062337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5307242249072146045416449 3980431686804109534062337)
                      ·
                        rfl

theorem cell23_7751863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 3, 2].length) (baseStart_7751863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751863 prefixEnd_7751863 := by exact prefixLift 7751863
  have htrace : WordTrace (prefixWord ++ tailWord_7751863) baseStart_7751863 baseEnd_7751863 := by
    simpa [prefixWord, tailWord_7751863, baseEnd_7751863] using wordTrace_append hprefix tailTrace_7751863
  have hstable : (prefixWord ++ tailWord_7751863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751863).length < 2 ^ (prefixWord ++ tailWord_7751863).sum := by decide
  have hdescent : baseEnd_7751863 < baseStart_7751863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751890 : List Nat := [3, 2, 2, 2, 1, 4, 1, 2, 1, 5]
def baseStart_7751890 : Nat := 118140960795 + 7751890 * 2 ^ 59
def prefixEnd_7751890 : Nat := 4983230072969 + 3 ^ 40 * 7751890 * 2
def baseEnd_7751890 : Nat := 1326815183593926976141571

theorem tailTrace_7751890 : CollatzResearch.WordTrace tailWord_7751890 prefixEnd_7751890 1326815183593926976141571 := by
  unfold tailWord_7751890
  simp only [CollatzResearch.WordTrace]
  refine ⟨70683663971558480563665281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188489770590822614836440749 70683663971558480563665281)
  ·
    refine ⟨53012747978668860422748961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70683663971558480563665281 53012747978668860422748961)
    ·
      refine ⟨39759560984001645317061721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53012747978668860422748961 39759560984001645317061721)
      ·
        refine ⟨29819670738001233987796291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39759560984001645317061721 29819670738001233987796291)
        ·
          refine ⟨44729506107001850981694437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29819670738001233987796291 44729506107001850981694437)
          ·
            refine ⟨8386782395062847059067707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44729506107001850981694437 8386782395062847059067707)
            ·
              refine ⟨12580173592594270588601561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8386782395062847059067707 12580173592594270588601561)
              ·
                refine ⟨9435130194445702941451171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12580173592594270588601561 9435130194445702941451171)
                ·
                  refine ⟨14152695291668554412176757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9435130194445702941451171 14152695291668554412176757)
                  ·
                    refine ⟨1326815183593926976141571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14152695291668554412176757 1326815183593926976141571)
                    ·
                      rfl

theorem cell23_7751890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_7751890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751890 prefixEnd_7751890 := by exact prefixLift 7751890
  have htrace : WordTrace (prefixWord ++ tailWord_7751890) baseStart_7751890 baseEnd_7751890 := by
    simpa [prefixWord, tailWord_7751890, baseEnd_7751890] using wordTrace_append hprefix tailTrace_7751890
  have hstable : (prefixWord ++ tailWord_7751890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751890).length < 2 ^ (prefixWord ++ tailWord_7751890).sum := by decide
  have hdescent : baseEnd_7751890 < baseStart_7751890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751907 : List Nat := [1, 1, 1, 8, 1, 1, 3, 1, 1, 5]
def baseStart_7751907 : Nat := 118140960795 + 7751907 * 2 ^ 59
def prefixEnd_7751907 : Nat := 4983230072969 + 3 ^ 40 * 7751907 * 2
def baseEnd_7751907 : Nat := 1326818093317635787304045

theorem tailTrace_7751907 : CollatzResearch.WordTrace tailWord_7751907 prefixEnd_7751907 1326818093317635787304045 := by
  unfold tailWord_7751907
  simp only [CollatzResearch.WordTrace]
  refine ⟨282735275927172334158029975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188490183951448222772019983 282735275927172334158029975)
  ·
    refine ⟨424102913890758501237044963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282735275927172334158029975 424102913890758501237044963)
    ·
      refine ⟨636154370836137751855567445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424102913890758501237044963 636154370836137751855567445)
      ·
        refine ⟨7454934033235989279557431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 636154370836137751855567445 7454934033235989279557431)
        ·
          refine ⟨11182401049853983919336147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7454934033235989279557431 11182401049853983919336147)
          ·
            refine ⟨16773601574780975879004221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11182401049853983919336147 16773601574780975879004221)
            ·
              refine ⟨6290100590542865954626583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16773601574780975879004221 6290100590542865954626583)
              ·
                refine ⟨9435150885814298931939875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6290100590542865954626583 9435150885814298931939875)
                ·
                  refine ⟨14152726328721448397909813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9435150885814298931939875 14152726328721448397909813)
                  ·
                    refine ⟨1326818093317635787304045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14152726328721448397909813 1326818093317635787304045)
                    ·
                      rfl

theorem cell23_7751907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 1, 5].length) (baseStart_7751907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751907 prefixEnd_7751907 := by exact prefixLift 7751907
  have htrace : WordTrace (prefixWord ++ tailWord_7751907) baseStart_7751907 baseEnd_7751907 := by
    simpa [prefixWord, tailWord_7751907, baseEnd_7751907] using wordTrace_append hprefix tailTrace_7751907
  have hstable : (prefixWord ++ tailWord_7751907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751907).length < 2 ^ (prefixWord ++ tailWord_7751907).sum := by decide
  have hdescent : baseEnd_7751907 < baseStart_7751907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751940 : List Nat := [2, 3, 2, 2, 3, 1, 2, 1, 1, 2, 4]
def baseStart_7751940 : Nat := 118140960795 + 7751940 * 2 ^ 59
def prefixEnd_7751940 : Nat := 4983230072969 + 3 ^ 40 * 7751940 * 2
def baseEnd_7751940 : Nat := 3980471224814505732799483

theorem tailTrace_7751940 : CollatzResearch.WordTrace tailWord_7751940 prefixEnd_7751940 3980471224814505732799483 := by
  unfold tailWord_7751940
  simp only [CollatzResearch.WordTrace]
  refine ⟨141368239768026390396990637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188490986357368520529320849 141368239768026390396990637)
  ·
    refine ⟨53013089913009896398871489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141368239768026390396990637 53013089913009896398871489)
    ·
      refine ⟨39759817434757422299153617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53013089913009896398871489 39759817434757422299153617)
      ·
        refine ⟨29819863076068066724365213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39759817434757422299153617 29819863076068066724365213)
        ·
          refine ⟨11182448653525525021636955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29819863076068066724365213 11182448653525525021636955)
          ·
            refine ⟨16773672980288287532455433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11182448653525525021636955 16773672980288287532455433)
            ·
              refine ⟨12580254735216215649341575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16773672980288287532455433 12580254735216215649341575)
              ·
                refine ⟨18870382102824323474012363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12580254735216215649341575 18870382102824323474012363)
                ·
                  refine ⟨28305573154236485211018545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18870382102824323474012363 28305573154236485211018545)
                  ·
                    refine ⟨21229179865677363908263909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28305573154236485211018545 21229179865677363908263909)
                    ·
                      refine ⟨3980471224814505732799483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21229179865677363908263909 3980471224814505732799483)
                      ·
                        rfl

theorem cell23_7751940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_7751940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751940 prefixEnd_7751940 := by exact prefixLift 7751940
  have htrace : WordTrace (prefixWord ++ tailWord_7751940) baseStart_7751940 baseEnd_7751940 := by
    simpa [prefixWord, tailWord_7751940, baseEnd_7751940] using wordTrace_append hprefix tailTrace_7751940
  have hstable : (prefixWord ++ tailWord_7751940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751940).length < 2 ^ (prefixWord ++ tailWord_7751940).sum := by decide
  have hdescent : baseEnd_7751940 < baseStart_7751940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751983 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 3, 4, 2]
def baseStart_7751983 : Nat := 118140960795 + 7751983 * 2 ^ 59
def prefixEnd_7751983 : Nat := 4983230072969 + 3 ^ 40 * 7751983 * 2
def baseEnd_7751983 : Nat := 3980493304482649064561785

theorem tailTrace_7751983 : CollatzResearch.WordTrace tailWord_7751983 prefixEnd_7751983 3980493304482649064561785 := by
  unfold tailWord_7751983
  simp only [CollatzResearch.WordTrace]
  refine ⟨282738047874896999137796603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188492031916597999425197735 282738047874896999137796603)
  ·
    refine ⟨424107071812345498706694905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282738047874896999137796603 424107071812345498706694905)
    ·
      refine ⟨318080303859259124030021179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424107071812345498706694905 318080303859259124030021179)
      ·
        refine ⟨477120455788888686045031769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318080303859259124030021179 477120455788888686045031769)
        ·
          refine ⟨357840341841666514533773827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477120455788888686045031769 357840341841666514533773827)
          ·
            refine ⟨536760512762499771800660741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357840341841666514533773827 536760512762499771800660741)
            ·
              refine ⟨100642596142968707212623889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 536760512762499771800660741 100642596142968707212623889)
              ·
                refine ⟨75481947107226530409467917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100642596142968707212623889 75481947107226530409467917)
                ·
                  refine ⟨28305730165209948903550469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75481947107226530409467917 28305730165209948903550469)
                  ·
                    refine ⟨5307324405976865419415713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28305730165209948903550469 5307324405976865419415713)
                    ·
                      refine ⟨3980493304482649064561785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5307324405976865419415713 3980493304482649064561785)
                      ·
                        rfl

theorem cell23_7751983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 4, 2].length) (baseStart_7751983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751983 prefixEnd_7751983 := by exact prefixLift 7751983
  have htrace : WordTrace (prefixWord ++ tailWord_7751983) baseStart_7751983 baseEnd_7751983 := by
    simpa [prefixWord, tailWord_7751983, baseEnd_7751983] using wordTrace_append hprefix tailTrace_7751983
  have hstable : (prefixWord ++ tailWord_7751983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751983).length < 2 ^ (prefixWord ++ tailWord_7751983).sum := by decide
  have hdescent : baseEnd_7751983 < baseStart_7751983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7751993 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 2, 6]
def baseStart_7751993 : Nat := 118140960795 + 7751993 * 2 ^ 59
def prefixEnd_7751993 : Nat := 4983230072969 + 3 ^ 40 * 7751993 * 2
def baseEnd_7751993 : Nat := 1326832813096398008478913

theorem tailTrace_7751993 : CollatzResearch.WordTrace tailWord_7751993 prefixEnd_7751993 1326832813096398008478913 := by
  unfold tailWord_7751993
  simp only [CollatzResearch.WordTrace]
  refine ⟨282738412604860770845660633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188492275069907180563773755 282738412604860770845660633)
  ·
    refine ⟨212053809453645578134245475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282738412604860770845660633 212053809453645578134245475)
    ·
      refine ⟨318080714180468367201368213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212053809453645578134245475 318080714180468367201368213)
      ·
        refine ⟨14910033477209454712564135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 318080714180468367201368213 14910033477209454712564135)
        ·
          refine ⟨22365050215814182068846203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14910033477209454712564135 22365050215814182068846203)
          ·
            refine ⟨33547575323721273103269305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22365050215814182068846203 33547575323721273103269305)
            ·
              refine ⟨25160681492790954827451979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33547575323721273103269305 25160681492790954827451979)
              ·
                refine ⟨37741022239186432241177969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25160681492790954827451979 37741022239186432241177969)
                ·
                  refine ⟨28305766679389824180883477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37741022239186432241177969 28305766679389824180883477)
                  ·
                    refine ⟨1326832813096398008478913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28305766679389824180883477 1326832813096398008478913)
                    ·
                      rfl

theorem cell23_7751993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 6].length) (baseStart_7751993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7751993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7751993 prefixEnd_7751993 := by exact prefixLift 7751993
  have htrace : WordTrace (prefixWord ++ tailWord_7751993) baseStart_7751993 baseEnd_7751993 := by
    simpa [prefixWord, tailWord_7751993, baseEnd_7751993] using wordTrace_append hprefix tailTrace_7751993
  have hstable : (prefixWord ++ tailWord_7751993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7751993).length < 2 ^ (prefixWord ++ tailWord_7751993).sum := by decide
  have hdescent : baseEnd_7751993 < baseStart_7751993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7751993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752040 : List Nat := [2, 1, 4, 2, 2, 3, 1, 1, 7]
def baseStart_7752040 : Nat := 118140960795 + 7752040 * 2 ^ 59
def prefixEnd_7752040 : Nat := 4983230072969 + 3 ^ 40 * 7752040 * 2
def baseEnd_7752040 : Nat := 442280285875550593505447

theorem tailTrace_7752040 : CollatzResearch.WordTrace tailWord_7752040 prefixEnd_7752040 442280285875550593505447 := by
  unfold tailWord_7752040
  simp only [CollatzResearch.WordTrace]
  refine ⟨141370063417845248936310787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188493417890460331915081049 141370063417845248936310787)
  ·
    refine ⟨212055095126767873404466181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141370063417845248936310787 212055095126767873404466181)
    ·
      refine ⟨39760330336268976263337409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212055095126767873404466181 39760330336268976263337409)
      ·
        refine ⟨29820247752201732197503057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39760330336268976263337409 29820247752201732197503057)
        ·
          refine ⟨22365185814151299148127293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29820247752201732197503057 22365185814151299148127293)
          ·
            refine ⟨8386944680306737180547735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22365185814151299148127293 8386944680306737180547735)
            ·
              refine ⟨12580417020460105770821603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8386944680306737180547735 12580417020460105770821603)
              ·
                refine ⟨18870625530690158656232405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12580417020460105770821603 18870625530690158656232405)
                ·
                  refine ⟨442280285875550593505447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18870625530690158656232405 442280285875550593505447)
                  ·
                    rfl

theorem cell23_7752040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 7].length) (baseStart_7752040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752040 prefixEnd_7752040 := by exact prefixLift 7752040
  have htrace : WordTrace (prefixWord ++ tailWord_7752040) baseStart_7752040 baseEnd_7752040 := by
    simpa [prefixWord, tailWord_7752040, baseEnd_7752040] using wordTrace_append hprefix tailTrace_7752040
  have hstable : (prefixWord ++ tailWord_7752040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752040).length < 2 ^ (prefixWord ++ tailWord_7752040).sum := by decide
  have hdescent : baseEnd_7752040 < baseStart_7752040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752043 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 1, 7, 2]
def baseStart_7752043 : Nat := 118140960795 + 7752043 * 2 ^ 59
def prefixEnd_7752043 : Nat := 4983230072969 + 3 ^ 40 * 7752043 * 2
def baseEnd_7752043 : Nat := 3980524113321918829811509

theorem tailTrace_7752043 : CollatzResearch.WordTrace tailWord_7752043 prefixEnd_7752043 3980524113321918829811509 := by
  unfold tailWord_7752043
  simp only [CollatzResearch.WordTrace]
  refine ⟨282740236254679629384980783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188493490836453086256653855 282740236254679629384980783)
  ·
    refine ⟨424110354382019444077471175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282740236254679629384980783 424110354382019444077471175)
    ·
      refine ⟨636165531573029166116206763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424110354382019444077471175 636165531573029166116206763)
      ·
        refine ⟨954248297359543749174310145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636165531573029166116206763 954248297359543749174310145)
        ·
          refine ⟨715686223019657811880732609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 954248297359543749174310145 715686223019657811880732609)
          ·
            refine ⟨536764667264743358910549457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 715686223019657811880732609 536764667264743358910549457)
            ·
              refine ⟨402573500448557519182912093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 536764667264743358910549457 402573500448557519182912093)
              ·
                refine ⟨150965062668209069693592035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 402573500448557519182912093 150965062668209069693592035)
                ·
                  refine ⟨226447594002313604540388053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150965062668209069693592035 226447594002313604540388053)
                  ·
                    refine ⟨5307365484429225106415345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 226447594002313604540388053 5307365484429225106415345)
                    ·
                      refine ⟨3980524113321918829811509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5307365484429225106415345 3980524113321918829811509)
                      ·
                        rfl

theorem cell23_7752043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 7, 2].length) (baseStart_7752043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752043 prefixEnd_7752043 := by exact prefixLift 7752043
  have htrace : WordTrace (prefixWord ++ tailWord_7752043) baseStart_7752043 baseEnd_7752043 := by
    simpa [prefixWord, tailWord_7752043, baseEnd_7752043] using wordTrace_append hprefix tailTrace_7752043
  have hstable : (prefixWord ++ tailWord_7752043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752043).length < 2 ^ (prefixWord ++ tailWord_7752043).sum := by decide
  have hdescent : baseEnd_7752043 < baseStart_7752043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752090 : List Nat := [3, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4]
def baseStart_7752090 : Nat := 118140960795 + 7752090 * 2 ^ 59
def prefixEnd_7752090 : Nat := 4983230072969 + 3 ^ 40 * 7752090 * 2
def baseEnd_7752090 : Nat := 3980548246912680145923793

theorem tailTrace_7752090 : CollatzResearch.WordTrace tailWord_7752090 prefixEnd_7752090 3980548246912680145923793 := by
  unfold tailWord_7752090
  simp only [CollatzResearch.WordTrace]
  refine ⟨70685487621377339102985431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188494633657006237607961149 70685487621377339102985431)
  ·
    refine ⟨106028231432066008654478147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70685487621377339102985431 106028231432066008654478147)
    ·
      refine ⟨159042347148099012981717221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106028231432066008654478147 159042347148099012981717221)
      ·
        refine ⟨29820440090268564934071979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159042347148099012981717221 29820440090268564934071979)
        ·
          refine ⟨44730660135402847401107969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29820440090268564934071979 44730660135402847401107969)
          ·
            refine ⟨33547995101552135550830977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44730660135402847401107969 33547995101552135550830977)
            ·
              refine ⟨25160996326164101663123233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33547995101552135550830977 25160996326164101663123233)
              ·
                refine ⟨18870747244623076247342425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25160996326164101663123233 18870747244623076247342425)
                ·
                  refine ⟨14153060433467307185506819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18870747244623076247342425 14153060433467307185506819)
                  ·
                    refine ⟨21229590650200960778260229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14153060433467307185506819 21229590650200960778260229)
                    ·
                      refine ⟨3980548246912680145923793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21229590650200960778260229 3980548246912680145923793)
                      ·
                        rfl

theorem cell23_7752090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_7752090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752090 prefixEnd_7752090 := by exact prefixLift 7752090
  have htrace : WordTrace (prefixWord ++ tailWord_7752090) baseStart_7752090 baseEnd_7752090 := by
    simpa [prefixWord, tailWord_7752090, baseEnd_7752090] using wordTrace_append hprefix tailTrace_7752090
  have hstable : (prefixWord ++ tailWord_7752090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752090).length < 2 ^ (prefixWord ++ tailWord_7752090).sum := by decide
  have hdescent : baseEnd_7752090 < baseStart_7752090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752117 : List Nat := [1, 3, 3, 2, 3, 1, 1, 2, 3, 4]
def baseStart_7752117 : Nat := 118140960795 + 7752117 * 2 ^ 59
def prefixEnd_7752117 : Nat := 4983230072969 + 3 ^ 40 * 7752117 * 2
def baseEnd_7752117 : Nat := 1326854036963450513428723

theorem tailTrace_7752117 : CollatzResearch.WordTrace tailWord_7752117 prefixEnd_7752117 1326854036963450513428723 := by
  unfold tailWord_7752117
  simp only [CollatzResearch.WordTrace]
  refine ⟨282742935256411540023174605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188495290170941026682116403 282742935256411540023174605)
  ·
    refine ⟨106028600721154327508690477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282742935256411540023174605 106028600721154327508690477)
    ·
      refine ⟨39760725270432872815758929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106028600721154327508690477 39760725270432872815758929)
      ·
        refine ⟨29820543952824654611819197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39760725270432872815758929 29820543952824654611819197)
        ·
          refine ⟨11182703982309245479432199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29820543952824654611819197 11182703982309245479432199)
          ·
            refine ⟨16774055973463868219148299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11182703982309245479432199 16774055973463868219148299)
            ·
              refine ⟨25161083960195802328722449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16774055973463868219148299 25161083960195802328722449)
              ·
                refine ⟨18870812970146851746541837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25161083960195802328722449 18870812970146851746541837)
                ·
                  refine ⟨7076554863805069404953189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18870812970146851746541837 7076554863805069404953189)
                  ·
                    refine ⟨1326854036963450513428723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7076554863805069404953189 1326854036963450513428723)
                    ·
                      rfl

theorem cell23_7752117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_7752117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752117 prefixEnd_7752117 := by exact prefixLift 7752117
  have htrace : WordTrace (prefixWord ++ tailWord_7752117) baseStart_7752117 baseEnd_7752117 := by
    simpa [prefixWord, tailWord_7752117, baseEnd_7752117] using wordTrace_append hprefix tailTrace_7752117
  have hstable : (prefixWord ++ tailWord_7752117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752117).length < 2 ^ (prefixWord ++ tailWord_7752117).sum := by decide
  have hdescent : baseEnd_7752117 < baseStart_7752117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752150 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_7752150 : Nat := 118140960795 + 7752150 * 2 ^ 59
def prefixEnd_7752150 : Nat := 4983230072969 + 3 ^ 40 * 7752150 * 2
def baseEnd_7752150 : Nat := 3980579055751949911173517

theorem tailTrace_7752150 : CollatzResearch.WordTrace tailWord_7752150 prefixEnd_7752150 3980579055751949911173517 := by
  unfold tailWord_7752150
  simp only [CollatzResearch.WordTrace]
  refine ⟨17671508679080749166195369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188496092576861324439417269 17671508679080749166195369)
  ·
    refine ⟨13253631509310561874646527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17671508679080749166195369 13253631509310561874646527)
    ·
      refine ⟨19880447263965842811969791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13253631509310561874646527 19880447263965842811969791)
      ·
        refine ⟨29820670895948764217954687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19880447263965842811969791 29820670895948764217954687)
        ·
          refine ⟨44731006343923146326932031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29820670895948764217954687 44731006343923146326932031)
          ·
            refine ⟨67096509515884719490398047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44731006343923146326932031 67096509515884719490398047)
            ·
              refine ⟨100644764273827079235597071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67096509515884719490398047 100644764273827079235597071)
              ·
                refine ⟨150967146410740618853395607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100644764273827079235597071 150967146410740618853395607)
                ·
                  refine ⟨226450719616110928280093411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150967146410740618853395607 226450719616110928280093411)
                  ·
                    refine ⟨339676079424166392420140117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 226450719616110928280093411 339676079424166392420140117)
                    ·
                      refine ⟨3980579055751949911173517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 339676079424166392420140117 3980579055751949911173517)
                      ·
                        rfl

theorem cell23_7752150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_7752150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752150 prefixEnd_7752150 := by exact prefixLift 7752150
  have htrace : WordTrace (prefixWord ++ tailWord_7752150) baseStart_7752150 baseEnd_7752150 := by
    simpa [prefixWord, tailWord_7752150, baseEnd_7752150] using wordTrace_append hprefix tailTrace_7752150
  have hstable : (prefixWord ++ tailWord_7752150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752150).length < 2 ^ (prefixWord ++ tailWord_7752150).sum := by decide
  have hdescent : baseEnd_7752150 < baseStart_7752150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752197 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 5, 2, 2]
def baseStart_7752197 : Nat := 118140960795 + 7752197 * 2 ^ 59
def prefixEnd_7752197 : Nat := 4983230072969 + 3 ^ 40 * 7752197 * 2
def baseEnd_7752197 : Nat := 3980603189342711227285801

theorem tailTrace_7752197 : CollatzResearch.WordTrace tailWord_7752197 prefixEnd_7752197 3980603189342711227285801 := by
  unfold tailWord_7752197
  simp only [CollatzResearch.WordTrace]
  refine ⟨282745853096121713686086845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188497235397414475790724563 282745853096121713686086845)
  ·
    refine ⟨106029694911045642632282567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282745853096121713686086845 106029694911045642632282567)
    ·
      refine ⟨159044542366568463948423851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106029694911045642632282567 159044542366568463948423851)
      ·
        refine ⟨238566813549852695922635777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159044542366568463948423851 238566813549852695922635777)
        ·
          refine ⟨178925110162389521941976833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238566813549852695922635777 178925110162389521941976833)
          ·
            refine ⟨134193832621792141456482625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178925110162389521941976833 134193832621792141456482625)
            ·
              refine ⟨100645374466344106092361969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134193832621792141456482625 100645374466344106092361969)
              ·
                refine ⟨75484030849758079569271477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100645374466344106092361969 75484030849758079569271477)
                ·
                  refine ⟨7076627892164819959619201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75484030849758079569271477 7076627892164819959619201)
                  ·
                    refine ⟨5307470919123614969714401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7076627892164819959619201 5307470919123614969714401)
                    ·
                      refine ⟨3980603189342711227285801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5307470919123614969714401 3980603189342711227285801)
                      ·
                        rfl

theorem cell23_7752197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 2, 2].length) (baseStart_7752197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752197 prefixEnd_7752197 := by exact prefixLift 7752197
  have htrace : WordTrace (prefixWord ++ tailWord_7752197) baseStart_7752197 baseEnd_7752197 := by
    simpa [prefixWord, tailWord_7752197, baseEnd_7752197] using wordTrace_append hprefix tailTrace_7752197
  have hstable : (prefixWord ++ tailWord_7752197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752197).length < 2 ^ (prefixWord ++ tailWord_7752197).sum := by decide
  have hdescent : baseEnd_7752197 < baseStart_7752197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752200 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 5, 2, 3]
def baseStart_7752200 : Nat := 118140960795 + 7752200 * 2 ^ 59
def prefixEnd_7752200 : Nat := 4983230072969 + 3 ^ 40 * 7752200 * 2
def baseEnd_7752200 : Nat := 3980604729784674715548287

theorem tailTrace_7752200 : CollatzResearch.WordTrace tailWord_7752200 prefixEnd_7752200 3980604729784674715548287 := by
  unfold tailWord_7752200
  simp only [CollatzResearch.WordTrace]
  refine ⟨141372981257555422599223027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188497308343407230132297369 141372981257555422599223027)
  ·
    refine ⟨212059471886333133898834541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141372981257555422599223027 212059471886333133898834541)
    ·
      refine ⟨79522301957374925212062953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212059471886333133898834541 79522301957374925212062953)
      ·
        refine ⟨59641726468031193909047215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79522301957374925212062953 59641726468031193909047215)
        ·
          refine ⟨89462589702046790863570823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59641726468031193909047215 89462589702046790863570823)
          ·
            refine ⟨134193884553070186295356235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89462589702046790863570823 134193884553070186295356235)
            ·
              refine ⟨201290826829605279443034353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134193884553070186295356235 201290826829605279443034353)
              ·
                refine ⟨150968120122203959582275765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201290826829605279443034353 150968120122203959582275765)
                ·
                  refine ⟨14153261261456621210838353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150968120122203959582275765 14153261261456621210838353)
                  ·
                    refine ⟨10614945946092465908128765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14153261261456621210838353 10614945946092465908128765)
                    ·
                      refine ⟨3980604729784674715548287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10614945946092465908128765 3980604729784674715548287)
                      ·
                        rfl

theorem cell23_7752200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_7752200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752200 prefixEnd_7752200 := by exact prefixLift 7752200
  have htrace : WordTrace (prefixWord ++ tailWord_7752200) baseStart_7752200 baseEnd_7752200 := by
    simpa [prefixWord, tailWord_7752200, baseEnd_7752200] using wordTrace_append hprefix tailTrace_7752200
  have hstable : (prefixWord ++ tailWord_7752200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752200).length < 2 ^ (prefixWord ++ tailWord_7752200).sum := by decide
  have hdescent : baseEnd_7752200 < baseStart_7752200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752203 : List Nat := [1, 1, 1, 1, 7, 1, 11]
def baseStart_7752203 : Nat := 118140960795 + 7752203 * 2 ^ 59
def prefixEnd_7752203 : Nat := 4983230072969 + 3 ^ 40 * 7752203 * 2
def baseEnd_7752203 : Nat := 49143287286748619800133

theorem tailTrace_7752203 : CollatzResearch.WordTrace tailWord_7752203 prefixEnd_7752203 49143287286748619800133 := by
  unfold tailWord_7752203
  simp only [CollatzResearch.WordTrace]
  refine ⟨282746071934099976710805263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188497381289399984473870175 282746071934099976710805263)
  ·
    refine ⟨424119107901149965066207895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282746071934099976710805263 424119107901149965066207895)
    ·
      refine ⟨636178661851724947599311843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424119107901149965066207895 636178661851724947599311843)
      ·
        refine ⟨954267992777587421398967765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636178661851724947599311843 954267992777587421398967765)
        ·
          refine ⟨22365656080724705189038307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 954267992777587421398967765 22365656080724705189038307)
          ·
            refine ⟨33548484121087057783557461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22365656080724705189038307 33548484121087057783557461)
            ·
              refine ⟨49143287286748619800133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 33548484121087057783557461 49143287286748619800133)
              ·
                rfl

theorem cell23_7752203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 11].length) (baseStart_7752203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752203 prefixEnd_7752203 := by exact prefixLift 7752203
  have htrace : WordTrace (prefixWord ++ tailWord_7752203) baseStart_7752203 baseEnd_7752203 := by
    simpa [prefixWord, tailWord_7752203, baseEnd_7752203] using wordTrace_append hprefix tailTrace_7752203
  have hstable : (prefixWord ++ tailWord_7752203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752203).length < 2 ^ (prefixWord ++ tailWord_7752203).sum := by decide
  have hdescent : baseEnd_7752203 < baseStart_7752203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752220 : List Nat := [2, 2, 3, 1, 2, 3, 2, 8]
def baseStart_7752220 : Nat := 118140960795 + 7752220 * 2 ^ 59
def prefixEnd_7752220 : Nat := 4983230072969 + 3 ^ 40 * 7752220 * 2
def baseEnd_7752220 : Nat := 147430185162880171751785

theorem tailTrace_7752220 : CollatzResearch.WordTrace tailWord_7752220 prefixEnd_7752220 147430185162880171751785 := by
  unfold tailWord_7752220
  simp only [CollatzResearch.WordTrace]
  refine ⟨141373345987519194307087057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188497794650025592409449409 141373345987519194307087057)
  ·
    refine ⟨106030009490639395730315293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141373345987519194307087057 106030009490639395730315293)
    ·
      refine ⟨39761253558989773398868235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106030009490639395730315293 39761253558989773398868235)
      ·
        refine ⟨59641880338484660098302353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39761253558989773398868235 59641880338484660098302353)
        ·
          refine ⟨44731410253863495073726765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59641880338484660098302353 44731410253863495073726765)
          ·
            refine ⟨16774278845198810652647537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44731410253863495073726765 16774278845198810652647537)
            ·
              refine ⟨12580709133899107989485653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16774278845198810652647537 12580709133899107989485653)
              ·
                refine ⟨147430185162880171751785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12580709133899107989485653 147430185162880171751785)
                ·
                  rfl

theorem cell23_7752220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 8].length) (baseStart_7752220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752220 prefixEnd_7752220 := by exact prefixLift 7752220
  have htrace : WordTrace (prefixWord ++ tailWord_7752220) baseStart_7752220 baseEnd_7752220 := by
    simpa [prefixWord, tailWord_7752220, baseEnd_7752220] using wordTrace_append hprefix tailTrace_7752220
  have hstable : (prefixWord ++ tailWord_7752220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752220).length < 2 ^ (prefixWord ++ tailWord_7752220).sum := by decide
  have hdescent : baseEnd_7752220 < baseStart_7752220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752223 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 6]
def baseStart_7752223 : Nat := 118140960795 + 7752223 * 2 ^ 59
def prefixEnd_7752223 : Nat := 4983230072969 + 3 ^ 40 * 7752223 * 2
def baseEnd_7752223 : Nat := 3980616539839728125560681

theorem tailTrace_7752223 : CollatzResearch.WordTrace tailWord_7752223 prefixEnd_7752223 3980616539839728125560681 := by
  unfold tailWord_7752223
  simp only [CollatzResearch.WordTrace]
  refine ⟨282746801394027520126533323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188497867596018346751022215 282746801394027520126533323)
  ·
    refine ⟨424120202091041280189799985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282746801394027520126533323 424120202091041280189799985)
    ·
      refine ⟨318090151568280960142349989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424120202091041280189799985 318090151568280960142349989)
      ·
        refine ⟨59641903419052680026690623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318090151568280960142349989 59641903419052680026690623)
        ·
          refine ⟨89462855128579020040035935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59641903419052680026690623 89462855128579020040035935)
          ·
            refine ⟨134194282692868530060053903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89462855128579020040035935 134194282692868530060053903)
            ·
              refine ⟨201291424039302795090080855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134194282692868530060053903 201291424039302795090080855)
              ·
                refine ⟨301937136058954192635121283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201291424039302795090080855 301937136058954192635121283)
                ·
                  refine ⟨452905704088431288952681925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301937136058954192635121283 452905704088431288952681925)
                  ·
                    refine ⟨84919819516580866678627861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 452905704088431288952681925 84919819516580866678627861)
                    ·
                      refine ⟨3980616539839728125560681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84919819516580866678627861 3980616539839728125560681)
                      ·
                        rfl

theorem cell23_7752223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_7752223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752223 prefixEnd_7752223 := by exact prefixLift 7752223
  have htrace : WordTrace (prefixWord ++ tailWord_7752223) baseStart_7752223 baseEnd_7752223 := by
    simpa [prefixWord, tailWord_7752223, baseEnd_7752223] using wordTrace_append hprefix tailTrace_7752223
  have hstable : (prefixWord ++ tailWord_7752223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752223).length < 2 ^ (prefixWord ++ tailWord_7752223).sum := by decide
  have hdescent : baseEnd_7752223 < baseStart_7752223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752224 : List Nat := [2, 1, 1, 6, 2, 1, 1, 3, 2, 4]
def baseStart_7752224 : Nat := 118140960795 + 7752224 * 2 ^ 59
def prefixEnd_7752224 : Nat := 4983230072969 + 3 ^ 40 * 7752224 * 2
def baseEnd_7752224 : Nat := 1326872351106794207216059

theorem tailTrace_7752224 : CollatzResearch.WordTrace tailWord_7752224 prefixEnd_7752224 1326872351106794207216059 := by
  unfold tailWord_7752224
  simp only [CollatzResearch.WordTrace]
  refine ⟨141373418933511948648659863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188497891911349264864879817 141373418933511948648659863)
  ·
    refine ⟨212060128400267922972989795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141373418933511948648659863 212060128400267922972989795)
    ·
      refine ⟨318090192600401884459484693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212060128400267922972989795 318090192600401884459484693)
      ·
        refine ⟨14910477778143838334038345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 318090192600401884459484693 14910477778143838334038345)
        ·
          refine ⟨11182858333607878750528759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14910477778143838334038345 11182858333607878750528759)
          ·
            refine ⟨16774287500411818125793139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11182858333607878750528759 16774287500411818125793139)
            ·
              refine ⟨25161431250617727188689709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16774287500411818125793139 25161431250617727188689709)
              ·
                refine ⟨9435536718981647695758641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25161431250617727188689709 9435536718981647695758641)
                ·
                  refine ⟨7076652539236235771818981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9435536718981647695758641 7076652539236235771818981)
                  ·
                    refine ⟨1326872351106794207216059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7076652539236235771818981 1326872351106794207216059)
                    ·
                      rfl

theorem cell23_7752224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 2, 4].length) (baseStart_7752224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752224 prefixEnd_7752224 := by exact prefixLift 7752224
  have htrace : WordTrace (prefixWord ++ tailWord_7752224) baseStart_7752224 baseEnd_7752224 := by
    simpa [prefixWord, tailWord_7752224, baseEnd_7752224] using wordTrace_append hprefix tailTrace_7752224
  have hstable : (prefixWord ++ tailWord_7752224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752224).length < 2 ^ (prefixWord ++ tailWord_7752224).sum := by decide
  have hdescent : baseEnd_7752224 < baseStart_7752224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752234 : List Nat := [3, 1, 4, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_7752234 : Nat := 118140960795 + 7752234 * 2 ^ 59
def prefixEnd_7752234 : Nat := 4983230072969 + 3 ^ 40 * 7752234 * 2
def baseEnd_7752234 : Nat := 3980622188126927582523131

theorem tailTrace_7752234 : CollatzResearch.WordTrace tailWord_7752234 prefixEnd_7752234 3980622188126927582523131 := by
  unfold tailWord_7752234
  simp only [CollatzResearch.WordTrace]
  refine ⟨70686800649246917251295939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188498135064658446003455837 70686800649246917251295939)
  ·
    refine ⟨106030200973870375876943909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70686800649246917251295939 106030200973870375876943909)
    ·
      refine ⟨19880662682600695476926983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106030200973870375876943909 19880662682600695476926983)
      ·
        refine ⟨29820994023901043215390475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19880662682600695476926983 29820994023901043215390475)
        ·
          refine ⟨44731491035851564823085713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29820994023901043215390475 44731491035851564823085713)
          ·
            refine ⟨33548618276888673617314285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44731491035851564823085713 33548618276888673617314285)
            ·
              refine ⟨12580731853833252606492857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33548618276888673617314285 12580731853833252606492857)
              ·
                refine ⟨9435548890374939454869643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12580731853833252606492857 9435548890374939454869643)
                ·
                  refine ⟨14153323335562409182304465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9435548890374939454869643 14153323335562409182304465)
                  ·
                    refine ⟨10614992501671806886728349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14153323335562409182304465 10614992501671806886728349)
                    ·
                      refine ⟨3980622188126927582523131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10614992501671806886728349 3980622188126927582523131)
                      ·
                        rfl

theorem cell23_7752234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_7752234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752234 prefixEnd_7752234 := by exact prefixLift 7752234
  have htrace : WordTrace (prefixWord ++ tailWord_7752234) baseStart_7752234 baseEnd_7752234 := by
    simpa [prefixWord, tailWord_7752234, baseEnd_7752234] using wordTrace_append hprefix tailTrace_7752234
  have hstable : (prefixWord ++ tailWord_7752234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752234).length < 2 ^ (prefixWord ++ tailWord_7752234).sum := by decide
  have hdescent : baseEnd_7752234 < baseStart_7752234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752270 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4]
def baseStart_7752270 : Nat := 118140960795 + 7752270 * 2 ^ 59
def prefixEnd_7752270 : Nat := 4983230072969 + 3 ^ 40 * 7752270 * 2
def baseEnd_7752270 : Nat := 3980640673430489441672965

theorem tailTrace_7752270 : CollatzResearch.WordTrace tailWord_7752270 prefixEnd_7752270 3980640673430489441672965 := by
  unfold tailWord_7752270
  simp only [CollatzResearch.WordTrace]
  refine ⟨35343564453107155894186783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188499010416571498102329509 35343564453107155894186783)
  ·
    refine ⟨53015346679660733841280175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35343564453107155894186783 53015346679660733841280175)
    ·
      refine ⟨79523020019491100761920263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53015346679660733841280175 79523020019491100761920263)
      ·
        refine ⟨119284530029236651142880395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79523020019491100761920263 119284530029236651142880395)
        ·
          refine ⟨178926795043854976714320593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119284530029236651142880395 178926795043854976714320593)
          ·
            refine ⟨134195096282891232535740445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178926795043854976714320593 134195096282891232535740445)
            ·
              refine ⟨50323161106084212200902667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134195096282891232535740445 50323161106084212200902667)
              ·
                refine ⟨75484741659126318301354001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50323161106084212200902667 75484741659126318301354001)
                ·
                  refine ⟨56613556244344738726015501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75484741659126318301354001 56613556244344738726015501)
                  ·
                    refine ⟨21230083591629277022255813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56613556244344738726015501 21230083591629277022255813)
                    ·
                      refine ⟨3980640673430489441672965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21230083591629277022255813 3980640673430489441672965)
                      ·
                        rfl

theorem cell23_7752270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_7752270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752270 prefixEnd_7752270 := by exact prefixLift 7752270
  have htrace : WordTrace (prefixWord ++ tailWord_7752270) baseStart_7752270 baseEnd_7752270 := by
    simpa [prefixWord, tailWord_7752270, baseEnd_7752270] using wordTrace_append hprefix tailTrace_7752270
  have hstable : (prefixWord ++ tailWord_7752270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752270).length < 2 ^ (prefixWord ++ tailWord_7752270).sum := by decide
  have hdescent : baseEnd_7752270 < baseStart_7752270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752327 : List Nat := [1, 1, 4, 2, 1, 2, 1, 6, 5]
def baseStart_7752327 : Nat := 118140960795 + 7752327 * 2 ^ 59
def prefixEnd_7752327 : Nat := 4983230072969 + 3 ^ 40 * 7752327 * 2
def baseEnd_7752327 : Nat := 442296660203088413184467

theorem tailTrace_7752327 : CollatzResearch.WordTrace tailWord_7752327 prefixEnd_7752327 442296660203088413184467 := by
  unfold tailWord_7752327
  simp only [CollatzResearch.WordTrace]
  refine ⟨282750594585650745888319235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188500396390433830592212823 282750594585650745888319235)
  ·
    refine ⟨424125891878476118832478853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282750594585650745888319235 424125891878476118832478853)
    ·
      refine ⟨79523604727214272281089785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 424125891878476118832478853 79523604727214272281089785)
      ·
        refine ⟨59642703545410704210817339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79523604727214272281089785 59642703545410704210817339)
        ·
          refine ⟨89464055318116056316226009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59642703545410704210817339 89464055318116056316226009)
          ·
            refine ⟨67098041488587042237169507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89464055318116056316226009 67098041488587042237169507)
            ·
              refine ⟨100647062232880563355754261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67098041488587042237169507 100647062232880563355754261)
              ·
                refine ⟨4717831042166276407300981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100647062232880563355754261 4717831042166276407300981)
                ·
                  refine ⟨442296660203088413184467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4717831042166276407300981 442296660203088413184467)
                  ·
                    rfl

theorem cell23_7752327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 5].length) (baseStart_7752327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752327 prefixEnd_7752327 := by exact prefixLift 7752327
  have htrace : WordTrace (prefixWord ++ tailWord_7752327) baseStart_7752327 baseEnd_7752327 := by
    simpa [prefixWord, tailWord_7752327, baseEnd_7752327] using wordTrace_append hprefix tailTrace_7752327
  have hstable : (prefixWord ++ tailWord_7752327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752327).length < 2 ^ (prefixWord ++ tailWord_7752327).sum := by decide
  have hdescent : baseEnd_7752327 < baseStart_7752327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752434 : List Nat := [3, 2, 1, 3, 1, 3, 2, 2, 6]
def baseStart_7752434 : Nat := 118140960795 + 7752434 * 2 ^ 59
def prefixEnd_7752434 : Nat := 4983230072969 + 3 ^ 40 * 7752434 * 2
def baseEnd_7752434 : Nat := 442302764917536311113579

theorem tailTrace_7752434 : CollatzResearch.WordTrace tailWord_7752434 prefixEnd_7752434 442302764917536311113579 := by
  unfold tailWord_7752434
  simp only [CollatzResearch.WordTrace]
  refine ⟨70688624299065775790616089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188502998130842068774976237 70688624299065775790616089)
  ·
    refine ⟨53016468224299331842962067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70688624299065775790616089 53016468224299331842962067)
    ·
      refine ⟨79524702336448997764443101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53016468224299331842962067 79524702336448997764443101)
      ·
        refine ⟨29821763376168374161666163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79524702336448997764443101 29821763376168374161666163)
        ·
          refine ⟨44732645064252561242499245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29821763376168374161666163 44732645064252561242499245)
          ·
            refine ⟨16774741899094710465937217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44732645064252561242499245 16774741899094710465937217)
            ·
              refine ⟨12581056424321032849452913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16774741899094710465937217 12581056424321032849452913)
              ·
                refine ⟨9435792318240774637089685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12581056424321032849452913 9435792318240774637089685)
                ·
                  refine ⟨442302764917536311113579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9435792318240774637089685 442302764917536311113579)
                  ·
                    rfl

theorem cell23_7752434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_7752434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752434 prefixEnd_7752434 := by exact prefixLift 7752434
  have htrace : WordTrace (prefixWord ++ tailWord_7752434) baseStart_7752434 baseEnd_7752434 := by
    simpa [prefixWord, tailWord_7752434, baseEnd_7752434] using wordTrace_append hprefix tailTrace_7752434
  have hstable : (prefixWord ++ tailWord_7752434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752434).length < 2 ^ (prefixWord ++ tailWord_7752434).sum := by decide
  have hdescent : baseEnd_7752434 < baseStart_7752434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752467 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 4]
def baseStart_7752467 : Nat := 118140960795 + 7752467 * 2 ^ 59
def prefixEnd_7752467 : Nat := 4983230072969 + 3 ^ 40 * 7752467 * 2
def baseEnd_7752467 : Nat := 3980741829119425170909559

theorem tailTrace_7752467 : CollatzResearch.WordTrace tailWord_7752467 prefixEnd_7752467 3980741829119425170909559 := by
  unfold tailWord_7752467
  simp only [CollatzResearch.WordTrace]
  refine ⟨282755700805143549798415655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188503800536762366532277103 282755700805143549798415655)
  ·
    refine ⟨424133551207715324697623483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282755700805143549798415655 424133551207715324697623483)
    ·
      refine ⟨636200326811572987046435225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424133551207715324697623483 636200326811572987046435225)
      ·
        refine ⟨477150245108679740284826419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 636200326811572987046435225 477150245108679740284826419)
        ·
          refine ⟨715725367663019610427239629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477150245108679740284826419 715725367663019610427239629)
          ·
            refine ⟨268397012873632353910214861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 715725367663019610427239629 268397012873632353910214861)
            ·
              refine ⟨100648879827612132716330573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268397012873632353910214861 100648879827612132716330573)
              ·
                refine ⟨37743329935354549768623965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100648879827612132716330573 37743329935354549768623965)
                ·
                  refine ⟨14153748725757956163233987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37743329935354549768623965 14153748725757956163233987)
                  ·
                    refine ⟨21230623088636934244850981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14153748725757956163233987 21230623088636934244850981)
                    ·
                      refine ⟨3980741829119425170909559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21230623088636934244850981 3980741829119425170909559)
                      ·
                        rfl

theorem cell23_7752467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 4].length) (baseStart_7752467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752467 prefixEnd_7752467 := by exact prefixLift 7752467
  have htrace : WordTrace (prefixWord ++ tailWord_7752467) baseStart_7752467 baseEnd_7752467 := by
    simpa [prefixWord, tailWord_7752467, baseEnd_7752467] using wordTrace_append hprefix tailTrace_7752467
  have hstable : (prefixWord ++ tailWord_7752467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752467).length < 2 ^ (prefixWord ++ tailWord_7752467).sum := by decide
  have hdescent : baseEnd_7752467 < baseStart_7752467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752471 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 1, 5, 2]
def baseStart_7752471 : Nat := 118140960795 + 7752471 * 2 ^ 59
def prefixEnd_7752471 : Nat := 4983230072969 + 3 ^ 40 * 7752471 * 2
def baseEnd_7752471 : Nat := 3980743883042043155259541

theorem tailTrace_7752471 : CollatzResearch.WordTrace tailWord_7752471 prefixEnd_7752471 3980743883042043155259541 := by
  unfold tailWord_7752471
  simp only [CollatzResearch.WordTrace]
  refine ⟨282755846697129058481561267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188503897798086038987707511 282755846697129058481561267)
  ·
    refine ⟨424133770045693587722341901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282755846697129058481561267 424133770045693587722341901)
    ·
      refine ⟨159050163767135095395878213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424133770045693587722341901 159050163767135095395878213)
      ·
        refine ⟨29821905706337830386727165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159050163767135095395878213 29821905706337830386727165)
        ·
          refine ⟨11183214639876686395022687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29821905706337830386727165 11183214639876686395022687)
          ·
            refine ⟨16774821959815029592534031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11183214639876686395022687 16774821959815029592534031)
            ·
              refine ⟨25162232939722544388801047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16774821959815029592534031 25162232939722544388801047)
              ·
                refine ⟨37743349409583816583201571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25162232939722544388801047 37743349409583816583201571)
                ·
                  refine ⟨56615024114375724874802357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37743349409583816583201571 56615024114375724874802357)
                  ·
                    refine ⟨5307658510722724207012721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56615024114375724874802357 5307658510722724207012721)
                    ·
                      refine ⟨3980743883042043155259541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5307658510722724207012721 3980743883042043155259541)
                      ·
                        rfl

theorem cell23_7752471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_7752471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752471 prefixEnd_7752471 := by exact prefixLift 7752471
  have htrace : WordTrace (prefixWord ++ tailWord_7752471) baseStart_7752471 baseEnd_7752471 := by
    simpa [prefixWord, tailWord_7752471, baseEnd_7752471] using wordTrace_append hprefix tailTrace_7752471
  have hstable : (prefixWord ++ tailWord_7752471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752471).length < 2 ^ (prefixWord ++ tailWord_7752471).sum := by decide
  have hdescent : baseEnd_7752471 < baseStart_7752471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752497 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 1, 1, 6]
def baseStart_7752497 : Nat := 118140960795 + 7752497 * 2 ^ 59
def prefixEnd_7752497 : Nat := 4983230072969 + 3 ^ 40 * 7752497 * 2
def baseEnd_7752497 : Nat := 3980757233539060053534421

theorem tailTrace_7752497 : CollatzResearch.WordTrace tailWord_7752497 prefixEnd_7752497 3980757233539060053534421 := by
  unfold tailWord_7752497
  simp only [CollatzResearch.WordTrace]
  refine ⟨282756794995034864922007745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188504529996689909948005163 282756794995034864922007745)
  ·
    refine ⟨212067596246276148691505809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282756794995034864922007745 212067596246276148691505809)
    ·
      refine ⟨159050697184707111518629357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212067596246276148691505809 159050697184707111518629357)
      ·
        refine ⟨59644011444265166819486009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159050697184707111518629357 59644011444265166819486009)
        ·
          refine ⟨44733008583198875114614507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59644011444265166819486009 44733008583198875114614507)
          ·
            refine ⟨67099512874798312671921761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44733008583198875114614507 67099512874798312671921761)
            ·
              refine ⟨50324634656098734503941321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67099512874798312671921761 50324634656098734503941321)
              ·
                refine ⟨37743475992074050877955991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50324634656098734503941321 37743475992074050877955991)
                ·
                  refine ⟨56615213988111076316933987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37743475992074050877955991 56615213988111076316933987)
                  ·
                    refine ⟨84922820982166614475400981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56615213988111076316933987 84922820982166614475400981)
                    ·
                      refine ⟨3980757233539060053534421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84922820982166614475400981 3980757233539060053534421)
                      ·
                        rfl

theorem cell23_7752497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_7752497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752497 prefixEnd_7752497 := by exact prefixLift 7752497
  have htrace : WordTrace (prefixWord ++ tailWord_7752497) baseStart_7752497 baseEnd_7752497 := by
    simpa [prefixWord, tailWord_7752497, baseEnd_7752497] using wordTrace_append hprefix tailTrace_7752497
  have hstable : (prefixWord ++ tailWord_7752497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752497).length < 2 ^ (prefixWord ++ tailWord_7752497).sum := by decide
  have hdescent : baseEnd_7752497 < baseStart_7752497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752521 : List Nat := [1, 2, 1, 1, 2, 6, 2, 2, 1, 2, 3]
def baseStart_7752521 : Nat := 118140960795 + 7752521 * 2 ^ 59
def prefixEnd_7752521 : Nat := 4983230072969 + 3 ^ 40 * 7752521 * 2
def baseEnd_7752521 : Nat := 3980769557074767959634311

theorem tailTrace_7752521 : CollatzResearch.WordTrace tailWord_7752521 prefixEnd_7752521 3980769557074767959634311 := by
  unfold tailWord_7752521
  simp only [CollatzResearch.WordTrace]
  refine ⟨282757670346947917020881417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188505113564631944680587611 282757670346947917020881417)
  ·
    refine ⟨212068252760210937765661063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282757670346947917020881417 212068252760210937765661063)
    ·
      refine ⟨318102379140316406648491595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212068252760210937765661063 318102379140316406648491595)
      ·
        refine ⟨477153568710474609972737393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318102379140316406648491595 477153568710474609972737393)
        ·
          refine ⟨357865176532855957479553045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477153568710474609972737393 357865176532855957479553045)
          ·
            refine ⟨16774930149977623006854049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 357865176532855957479553045 16774930149977623006854049)
            ·
              refine ⟨12581197612483217255140537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16774930149977623006854049 12581197612483217255140537)
              ·
                refine ⟨9435898209362412941355403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12581197612483217255140537 9435898209362412941355403)
                ·
                  refine ⟨14153847314043619412033105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9435898209362412941355403 14153847314043619412033105)
                  ·
                    refine ⟨10615385485532714559024829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14153847314043619412033105 10615385485532714559024829)
                    ·
                      refine ⟨3980769557074767959634311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10615385485532714559024829 3980769557074767959634311)
                      ·
                        rfl

theorem cell23_7752521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 2, 3].length) (baseStart_7752521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752521 prefixEnd_7752521 := by exact prefixLift 7752521
  have htrace : WordTrace (prefixWord ++ tailWord_7752521) baseStart_7752521 baseEnd_7752521 := by
    simpa [prefixWord, tailWord_7752521, baseEnd_7752521] using wordTrace_append hprefix tailTrace_7752521
  have hstable : (prefixWord ++ tailWord_7752521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752521).length < 2 ^ (prefixWord ++ tailWord_7752521).sum := by decide
  have hdescent : baseEnd_7752521 < baseStart_7752521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752524 : List Nat := [2, 2, 1, 3, 3, 1, 4, 7]
def baseStart_7752524 : Nat := 118140960795 + 7752524 * 2 ^ 59
def prefixEnd_7752524 : Nat := 4983230072969 + 3 ^ 40 * 7752524 * 2
def baseEnd_7752524 : Nat := 147435966574693757329511

theorem tailTrace_7752524 : CollatzResearch.WordTrace tailWord_7752524 prefixEnd_7752524 147435966574693757329511 := by
  unfold tailWord_7752524
  simp only [CollatzResearch.WordTrace]
  refine ⟨141378889882968524266620313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188505186510624699022160417 141378889882968524266620313)
  ·
    refine ⟨106034167412226393199965235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141378889882968524266620313 106034167412226393199965235)
    ·
      refine ⟨159051251118339589799947853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106034167412226393199965235 159051251118339589799947853)
      ·
        refine ⟨59644219169377346174980445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159051251118339589799947853 59644219169377346174980445)
        ·
          refine ⟨22366582188516504815617667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59644219169377346174980445 22366582188516504815617667)
          ·
            refine ⟨33549873282774757223426501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22366582188516504815617667 33549873282774757223426501)
            ·
              refine ⟨6290601240520266979392469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33549873282774757223426501 6290601240520266979392469)
              ·
                refine ⟨147435966574693757329511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6290601240520266979392469 147435966574693757329511)
                ·
                  rfl

theorem cell23_7752524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 7].length) (baseStart_7752524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752524 prefixEnd_7752524 := by exact prefixLift 7752524
  have htrace : WordTrace (prefixWord ++ tailWord_7752524) baseStart_7752524 baseEnd_7752524 := by
    simpa [prefixWord, tailWord_7752524, baseEnd_7752524] using wordTrace_append hprefix tailTrace_7752524
  have hstable : (prefixWord ++ tailWord_7752524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752524).length < 2 ^ (prefixWord ++ tailWord_7752524).sum := by decide
  have hdescent : baseEnd_7752524 < baseStart_7752524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752535 : List Nat := [1, 1, 3, 2, 4, 1, 3, 3, 1, 2, 2]
def baseStart_7752535 : Nat := 118140960795 + 7752535 * 2 ^ 59
def prefixEnd_7752535 : Nat := 4983230072969 + 3 ^ 40 * 7752535 * 2
def baseEnd_7752535 : Nat := 3980776745803930904859247

theorem tailTrace_7752535 : CollatzResearch.WordTrace tailWord_7752535 prefixEnd_7752535 3980776745803930904859247 := by
  unfold tailWord_7752535
  simp only [CollatzResearch.WordTrace]
  refine ⟨282758180968897197411891059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188505453979264798274594039 282758180968897197411891059)
  ·
    refine ⟨424137271453345796117836589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282758180968897197411891059 424137271453345796117836589)
    ·
      refine ⟨159051476795004673544188721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424137271453345796117836589 159051476795004673544188721)
      ·
        refine ⟨119288607596253505158141541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159051476795004673544188721 119288607596253505158141541)
        ·
          refine ⟨22366613924297532217151539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119288607596253505158141541 22366613924297532217151539)
          ·
            refine ⟨33549920886446298325727309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22366613924297532217151539 33549920886446298325727309)
            ·
              refine ⟨12581220332417361872147741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33549920886446298325727309 12581220332417361872147741)
              ·
                refine ⟨4717957624656510702055403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12581220332417361872147741 4717957624656510702055403)
                ·
                  refine ⟨7076936436984766053083105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4717957624656510702055403 7076936436984766053083105)
                  ·
                    refine ⟨5307702327738574539812329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7076936436984766053083105 5307702327738574539812329)
                    ·
                      refine ⟨3980776745803930904859247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5307702327738574539812329 3980776745803930904859247)
                      ·
                        rfl

theorem cell23_7752535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 1, 2, 2].length) (baseStart_7752535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752535 prefixEnd_7752535 := by exact prefixLift 7752535
  have htrace : WordTrace (prefixWord ++ tailWord_7752535) baseStart_7752535 baseEnd_7752535 := by
    simpa [prefixWord, tailWord_7752535, baseEnd_7752535] using wordTrace_append hprefix tailTrace_7752535
  have hstable : (prefixWord ++ tailWord_7752535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752535).length < 2 ^ (prefixWord ++ tailWord_7752535).sum := by decide
  have hdescent : baseEnd_7752535 < baseStart_7752535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752551 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 4, 1, 3]
def baseStart_7752551 : Nat := 118140960795 + 7752551 * 2 ^ 59
def prefixEnd_7752551 : Nat := 4983230072969 + 3 ^ 40 * 7752551 * 2
def baseEnd_7752551 : Nat := 3980784961494402842259173

theorem tailTrace_7752551 : CollatzResearch.WordTrace tailWord_7752551 prefixEnd_7752551 3980784961494402842259173 := by
  unfold tailWord_7752551
  simp only [CollatzResearch.WordTrace]
  refine ⟨282758764536839232144473507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188505843024559488096315671 282758764536839232144473507)
  ·
    refine ⟨424138146805258848216710261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282758764536839232144473507 424138146805258848216710261)
    ·
      refine ⟨39762951262993017020316587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 424138146805258848216710261 39762951262993017020316587)
      ·
        refine ⟨59644426894489525530474881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39762951262993017020316587 59644426894489525530474881)
        ·
          refine ⟨44733320170867144147856161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59644426894489525530474881 44733320170867144147856161)
          ·
            refine ⟨33549990128150358110892121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44733320170867144147856161 33549990128150358110892121)
            ·
              refine ⟨25162492596112768583169091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33549990128150358110892121 25162492596112768583169091)
              ·
                refine ⟨37743738894169152874753637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25162492596112768583169091 37743738894169152874753637)
                ·
                  refine ⟨7076951042656716164016307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37743738894169152874753637 7076951042656716164016307)
                  ·
                    refine ⟨10615426563985074246024461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7076951042656716164016307 10615426563985074246024461)
                    ·
                      refine ⟨3980784961494402842259173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10615426563985074246024461 3980784961494402842259173)
                      ·
                        rfl

theorem cell23_7752551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_7752551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752551 prefixEnd_7752551 := by exact prefixLift 7752551
  have htrace : WordTrace (prefixWord ++ tailWord_7752551) baseStart_7752551 baseEnd_7752551 := by
    simpa [prefixWord, tailWord_7752551, baseEnd_7752551] using wordTrace_append hprefix tailTrace_7752551
  have hstable : (prefixWord ++ tailWord_7752551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752551).length < 2 ^ (prefixWord ++ tailWord_7752551).sum := by decide
  have hdescent : baseEnd_7752551 < baseStart_7752551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752552 : List Nat := [2, 1, 4, 2, 1, 3, 3, 2, 1, 2, 2]
def baseStart_7752552 : Nat := 118140960795 + 7752552 * 2 ^ 59
def prefixEnd_7752552 : Nat := 4983230072969 + 3 ^ 40 * 7752552 * 2
def baseEnd_7752552 : Nat := 3980785474975057338346669

theorem tailTrace_7752552 : CollatzResearch.WordTrace tailWord_7752552 prefixEnd_7752552 3980785474975057338346669 := by
  unfold tailWord_7752552
  simp only [CollatzResearch.WordTrace]
  refine ⟨141379400504917804657629955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188505867339890406210173273 141379400504917804657629955)
  ·
    refine ⟨212069100757376706986444933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141379400504917804657629955 212069100757376706986444933)
    ·
      refine ⟨39762956392008132559958425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212069100757376706986444933 39762956392008132559958425)
      ·
        refine ⟨29822217294006099419968819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39762956392008132559958425 29822217294006099419968819)
        ·
          refine ⟨44733325941009149129953229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29822217294006099419968819 44733325941009149129953229)
          ·
            refine ⟨16774997227878430923732461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44733325941009149129953229 16774997227878430923732461)
            ·
              refine ⟨6290623960454411596399673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16774997227878430923732461 6290623960454411596399673)
              ·
                refine ⟨4717967970340808697299755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6290623960454411596399673 4717967970340808697299755)
                ·
                  refine ⟨7076951955511213045949633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4717967970340808697299755 7076951955511213045949633)
                  ·
                    refine ⟨5307713966633409784462225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7076951955511213045949633 5307713966633409784462225)
                    ·
                      refine ⟨3980785474975057338346669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5307713966633409784462225 3980785474975057338346669)
                      ·
                        rfl

theorem cell23_7752552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_7752552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752552 prefixEnd_7752552 := by exact prefixLift 7752552
  have htrace : WordTrace (prefixWord ++ tailWord_7752552) baseStart_7752552 baseEnd_7752552 := by
    simpa [prefixWord, tailWord_7752552, baseEnd_7752552] using wordTrace_append hprefix tailTrace_7752552
  have hstable : (prefixWord ++ tailWord_7752552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752552).length < 2 ^ (prefixWord ++ tailWord_7752552).sum := by decide
  have hdescent : baseEnd_7752552 < baseStart_7752552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752567 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 2, 6]
def baseStart_7752567 : Nat := 118140960795 + 7752567 * 2 ^ 59
def prefixEnd_7752567 : Nat := 4983230072969 + 3 ^ 40 * 7752567 * 2
def baseEnd_7752567 : Nat := 1326931059061624926553033

theorem tailTrace_7752567 : CollatzResearch.WordTrace tailWord_7752567 prefixEnd_7752567 1326931059061624926553033 := by
  unfold tailWord_7752567
  simp only [CollatzResearch.WordTrace]
  refine ⟨282759348104781266877055955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188506232069854177918037303 282759348104781266877055955)
  ·
    refine ⟨424139022157171900315583933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282759348104781266877055955 424139022157171900315583933)
    ·
      refine ⟨159052133308939462618343975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424139022157171900315583933 159052133308939462618343975)
      ·
        refine ⟨238578199963409193927515963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159052133308939462618343975 238578199963409193927515963)
        ·
          refine ⟨357867299945113790891273945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238578199963409193927515963 357867299945113790891273945)
          ·
            refine ⟨268400474958835343168455459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357867299945113790891273945 268400474958835343168455459)
            ·
              refine ⟨402600712438253014752683189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268400474958835343168455459 402600712438253014752683189)
              ·
                refine ⟨37743816791086220133064049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 402600712438253014752683189 37743816791086220133064049)
                ·
                  refine ⟨28307862593314665099798037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37743816791086220133064049 28307862593314665099798037)
                  ·
                    refine ⟨1326931059061624926553033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28307862593314665099798037 1326931059061624926553033)
                    ·
                      rfl

theorem cell23_7752567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_7752567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752567 prefixEnd_7752567 := by exact prefixLift 7752567
  have htrace : WordTrace (prefixWord ++ tailWord_7752567) baseStart_7752567 baseEnd_7752567 := by
    simpa [prefixWord, tailWord_7752567, baseEnd_7752567] using wordTrace_append hprefix tailTrace_7752567
  have hstable : (prefixWord ++ tailWord_7752567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752567).length < 2 ^ (prefixWord ++ tailWord_7752567).sum := by decide
  have hdescent : baseEnd_7752567 < baseStart_7752567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752608 : List Nat := [2, 1, 1, 4, 1, 1, 3, 4, 2, 2, 2]
def baseStart_7752608 : Nat := 118140960795 + 7752608 * 2 ^ 59
def prefixEnd_7752608 : Nat := 4983230072969 + 3 ^ 40 * 7752608 * 2
def baseEnd_7752608 : Nat := 3980814229891709119246411

theorem tailTrace_7752608 : CollatzResearch.WordTrace tailWord_7752608 prefixEnd_7752608 3980814229891709119246411 := by
  unfold tailWord_7752608
  simp only [CollatzResearch.WordTrace]
  refine ⟨141380421748816365439649239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188507228998421820586198985 141380421748816365439649239)
  ·
    refine ⟨212070632623224548159473859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141380421748816365439649239 212070632623224548159473859)
    ·
      refine ⟨318105948934836822239210789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212070632623224548159473859 318105948934836822239210789)
      ·
        refine ⟨59644865425281904169852023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318105948934836822239210789 59644865425281904169852023)
        ·
          refine ⟨89467298137922856254778035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59644865425281904169852023 89467298137922856254778035)
          ·
            refine ⟨134200947206884284382167053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89467298137922856254778035 134200947206884284382167053)
            ·
              refine ⟨50325355202581606643312645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134200947206884284382167053 50325355202581606643312645)
              ·
                refine ⟨9436004100484051245621121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50325355202581606643312645 9436004100484051245621121)
                ·
                  refine ⟨7077003075363038434215841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9436004100484051245621121 7077003075363038434215841)
                  ·
                    refine ⟨5307752306522278825661881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7077003075363038434215841 5307752306522278825661881)
                    ·
                      refine ⟨3980814229891709119246411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5307752306522278825661881 3980814229891709119246411)
                      ·
                        rfl

theorem cell23_7752608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_7752608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752608 prefixEnd_7752608 := by exact prefixLift 7752608
  have htrace : WordTrace (prefixWord ++ tailWord_7752608) baseStart_7752608 baseEnd_7752608 := by
    simpa [prefixWord, tailWord_7752608, baseEnd_7752608] using wordTrace_append hprefix tailTrace_7752608
  have hstable : (prefixWord ++ tailWord_7752608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752608).length < 2 ^ (prefixWord ++ tailWord_7752608).sum := by decide
  have hdescent : baseEnd_7752608 < baseStart_7752608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752646 : List Nat := [6, 1, 3, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_7752646 : Nat := 118140960795 + 7752646 * 2 ^ 59
def prefixEnd_7752646 : Nat := 4983230072969 + 3 ^ 40 * 7752646 * 2
def baseEnd_7752646 : Nat := 3980833742156579970571237

theorem tailTrace_7752646 : CollatzResearch.WordTrace tailWord_7752646 prefixEnd_7752646 3980833742156579970571237 := by
  unfold tailWord_7752646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8836319670984220730286931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 188508152980996708912787861 8836319670984220730286931)
  ·
    refine ⟨13254479506476331095430397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8836319670984220730286931 13254479506476331095430397)
    ·
      refine ⟨4970429814928624160786399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13254479506476331095430397 4970429814928624160786399)
      ·
        refine ⟨7455644722392936241179599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4970429814928624160786399 7455644722392936241179599)
        ·
          refine ⟨11183467083589404361769399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7455644722392936241179599 11183467083589404361769399)
          ·
            refine ⟨16775200625384106542654099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11183467083589404361769399 16775200625384106542654099)
            ·
              refine ⟨25162800938076159813981149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16775200625384106542654099 25162800938076159813981149)
              ·
                refine ⟨9436050351778559930242931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25162800938076159813981149 9436050351778559930242931)
                ·
                  refine ⟨14154075527667839895364397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9436050351778559930242931 14154075527667839895364397)
                  ·
                    refine ⟨5307778322875439960761649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14154075527667839895364397 5307778322875439960761649)
                    ·
                      refine ⟨3980833742156579970571237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5307778322875439960761649 3980833742156579970571237)
                      ·
                        rfl

theorem cell23_7752646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_7752646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752646 prefixEnd_7752646 := by exact prefixLift 7752646
  have htrace : WordTrace (prefixWord ++ tailWord_7752646) baseStart_7752646 baseEnd_7752646 := by
    simpa [prefixWord, tailWord_7752646, baseEnd_7752646] using wordTrace_append hprefix tailTrace_7752646
  have hstable : (prefixWord ++ tailWord_7752646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752646).length < 2 ^ (prefixWord ++ tailWord_7752646).sum := by decide
  have hdescent : baseEnd_7752646 < baseStart_7752646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752648 : List Nat := [2, 1, 3, 1, 5, 1, 2, 3, 5]
def baseStart_7752648 : Nat := 118140960795 + 7752648 * 2 ^ 59
def prefixEnd_7752648 : Nat := 4983230072969 + 3 ^ 40 * 7752648 * 2
def baseEnd_7752648 : Nat := 442314974346432106971803

theorem tailTrace_7752648 : CollatzResearch.WordTrace tailWord_7752648 prefixEnd_7752648 442314974346432106971803 := by
  unfold tailWord_7752648
  simp only [CollatzResearch.WordTrace]
  refine ⟨141381151208743908855377299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188508201611658545140503065 141381151208743908855377299)
  ·
    refine ⟨212071726813115863283065949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141381151208743908855377299 212071726813115863283065949)
    ·
      refine ⟨79526897554918448731149731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212071726813115863283065949 79526897554918448731149731)
      ·
        refine ⟨119290346332377673096724597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79526897554918448731149731 119290346332377673096724597)
        ·
          refine ⟨11183469968660406852817931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119290346332377673096724597 11183469968660406852817931)
          ·
            refine ⟨16775204952990610279226897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11183469968660406852817931 16775204952990610279226897)
            ·
              refine ⟨12581403714742957709420173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16775204952990610279226897 12581403714742957709420173)
              ·
                refine ⟨4718026393028609141032565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12581403714742957709420173 4718026393028609141032565)
                ·
                  refine ⟨442314974346432106971803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4718026393028609141032565 442314974346432106971803)
                  ·
                    rfl

theorem cell23_7752648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 5].length) (baseStart_7752648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752648 prefixEnd_7752648 := by exact prefixLift 7752648
  have htrace : WordTrace (prefixWord ++ tailWord_7752648) baseStart_7752648 baseEnd_7752648 := by
    simpa [prefixWord, tailWord_7752648, baseEnd_7752648] using wordTrace_append hprefix tailTrace_7752648
  have hstable : (prefixWord ++ tailWord_7752648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752648).length < 2 ^ (prefixWord ++ tailWord_7752648).sum := by decide
  have hdescent : baseEnd_7752648 < baseStart_7752648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752701 : List Nat := [1, 4, 1, 1, 1, 2, 1, 5, 2, 2, 3]
def baseStart_7752701 : Nat := 118140960795 + 7752701 * 2 ^ 59
def prefixEnd_7752701 : Nat := 4983230072969 + 3 ^ 40 * 7752701 * 2
def baseEnd_7752701 : Nat := 3980861983592577255383483

theorem tailTrace_7752701 : CollatzResearch.WordTrace tailWord_7752701 prefixEnd_7752701 3980861983592577255383483 := by
  unfold tailWord_7752701
  simp only [CollatzResearch.WordTrace]
  refine ⟨282764235486295807762433957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188509490324197205174955971 282764235486295807762433957)
  ·
    refine ⟨53018294153680463955456367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282764235486295807762433957 53018294153680463955456367)
    ·
      refine ⟨79527441230520695933184551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53018294153680463955456367 79527441230520695933184551)
      ·
        refine ⟨119291161845781043899776827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79527441230520695933184551 119291161845781043899776827)
        ·
          refine ⟨178936742768671565849665241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119291161845781043899776827 178936742768671565849665241)
          ·
            refine ⟨134202557076503674387248931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178936742768671565849665241 134202557076503674387248931)
            ·
              refine ⟨201303835614755511580873397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134202557076503674387248931 201303835614755511580873397)
              ·
                refine ⟨18872234588883329210706881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201303835614755511580873397 18872234588883329210706881)
                ·
                  refine ⟨14154175941662496908030161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18872234588883329210706881 14154175941662496908030161)
                  ·
                    refine ⟨10615631956246872681022621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14154175941662496908030161 10615631956246872681022621)
                    ·
                      refine ⟨3980861983592577255383483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10615631956246872681022621 3980861983592577255383483)
                      ·
                        rfl

theorem cell23_7752701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_7752701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752701 prefixEnd_7752701 := by exact prefixLift 7752701
  have htrace : WordTrace (prefixWord ++ tailWord_7752701) baseStart_7752701 baseEnd_7752701 := by
    simpa [prefixWord, tailWord_7752701, baseEnd_7752701] using wordTrace_append hprefix tailTrace_7752701
  have hstable : (prefixWord ++ tailWord_7752701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752701).length < 2 ^ (prefixWord ++ tailWord_7752701).sum := by decide
  have hdescent : baseEnd_7752701 < baseStart_7752701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752718 : List Nat := [4, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3]
def baseStart_7752718 : Nat := 118140960795 + 7752718 * 2 ^ 59
def prefixEnd_7752718 : Nat := 4983230072969 + 3 ^ 40 * 7752718 * 2
def baseEnd_7752718 : Nat := 3980870712763703688870905

theorem tailTrace_7752718 : CollatzResearch.WordTrace tailWord_7752718 prefixEnd_7752718 3980870712763703688870905 := by
  unfold tailWord_7752718
  simp only [CollatzResearch.WordTrace]
  refine ⟨35345606940904277458225351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188509903684822813110535205 35345606940904277458225351)
  ·
    refine ⟨53018410411356416187338027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35345606940904277458225351 53018410411356416187338027)
    ·
      refine ⟨79527615617034624281007041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53018410411356416187338027 79527615617034624281007041)
      ·
        refine ⟨59645711712775968210755281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79527615617034624281007041 59645711712775968210755281)
        ·
          refine ⟨44734283784581976158066461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59645711712775968210755281 44734283784581976158066461)
          ·
            refine ⟨16775356419218241059274923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44734283784581976158066461 16775356419218241059274923)
            ·
              refine ⟨25163034628827361588912385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16775356419218241059274923 25163034628827361588912385)
              ·
                refine ⟨18872275971620521191684289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25163034628827361588912385 18872275971620521191684289)
                ·
                  refine ⟨14154206978715390893763217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18872275971620521191684289 14154206978715390893763217)
                  ·
                    refine ⟨10615655234036543170322413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14154206978715390893763217 10615655234036543170322413)
                    ·
                      refine ⟨3980870712763703688870905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10615655234036543170322413 3980870712763703688870905)
                      ·
                        rfl

theorem cell23_7752718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_7752718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752718 prefixEnd_7752718 := by exact prefixLift 7752718
  have htrace : WordTrace (prefixWord ++ tailWord_7752718) baseStart_7752718 baseEnd_7752718 := by
    simpa [prefixWord, tailWord_7752718, baseEnd_7752718] using wordTrace_append hprefix tailTrace_7752718
  have hstable : (prefixWord ++ tailWord_7752718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752718).length < 2 ^ (prefixWord ++ tailWord_7752718).sum := by decide
  have hdescent : baseEnd_7752718 < baseStart_7752718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752738 : List Nat := [3, 3, 1, 1, 1, 3, 4, 1, 6]
def baseStart_7752738 : Nat := 118140960795 + 7752738 * 2 ^ 59
def prefixEnd_7752738 : Nat := 4983230072969 + 3 ^ 40 * 7752738 * 2
def baseEnd_7752738 : Nat := 442320109152977067846757

theorem tailTrace_7752738 : CollatzResearch.WordTrace tailWord_7752738 prefixEnd_7752738 442320109152977067846757 := by
  unfold tailWord_7752738
  simp only [CollatzResearch.WordTrace]
  refine ⟨70691396246790440770382717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188510389991441175387687245 70691396246790440770382717)
  ·
    refine ⟨26509273592546415288893519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70691396246790440770382717 26509273592546415288893519)
    ·
      refine ⟨39763910388819622933340279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26509273592546415288893519 39763910388819622933340279)
      ·
        refine ⟨59645865583229434400010419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39763910388819622933340279 59645865583229434400010419)
        ·
          refine ⟨89468798374844151600015629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59645865583229434400010419 89468798374844151600015629)
          ·
            refine ⟨33550799390566556850005861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89468798374844151600015629 33550799390566556850005861)
            ·
              refine ⟨6290774885731229409376099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33550799390566556850005861 6290774885731229409376099)
              ·
                refine ⟨9436162328596844114064149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6290774885731229409376099 9436162328596844114064149)
                ·
                  refine ⟨442320109152977067846757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9436162328596844114064149 442320109152977067846757)
                  ·
                    rfl

theorem cell23_7752738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_7752738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752738 prefixEnd_7752738 := by exact prefixLift 7752738
  have htrace : WordTrace (prefixWord ++ tailWord_7752738) baseStart_7752738 baseEnd_7752738 := by
    simpa [prefixWord, tailWord_7752738, baseEnd_7752738] using wordTrace_append hprefix tailTrace_7752738
  have hstable : (prefixWord ++ tailWord_7752738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752738).length < 2 ^ (prefixWord ++ tailWord_7752738).sum := by decide
  have hdescent : baseEnd_7752738 < baseStart_7752738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752768 : List Nat := [2, 1, 1, 2, 2, 3, 5, 1, 1, 5]
def baseStart_7752768 : Nat := 118140960795 + 7752768 * 2 ^ 59
def prefixEnd_7752768 : Nat := 4983230072969 + 3 ^ 40 * 7752768 * 2
def baseEnd_7752768 : Nat := 1326965462265476164415225

theorem tailTrace_7752768 : CollatzResearch.WordTrace tailWord_7752768 prefixEnd_7752768 1326965462265476164415225 := by
  unfold tailWord_7752768
  simp only [CollatzResearch.WordTrace]
  refine ⟨141383339588526539102561479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188511119451368718803415305 141383339588526539102561479)
  ·
    refine ⟨212075009382789808653842219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141383339588526539102561479 212075009382789808653842219)
    ·
      refine ⟨318112514074184712980763329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212075009382789808653842219 318112514074184712980763329)
      ·
        refine ⟨238584385555638534735572497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318112514074184712980763329 238584385555638534735572497)
        ·
          refine ⟨178938289166728901051679373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238584385555638534735572497 178938289166728901051679373)
          ·
            refine ⟨67101858437523337894379765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178938289166728901051679373 67101858437523337894379765)
            ·
              refine ⟨6290799228517812927598103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67101858437523337894379765 6290799228517812927598103)
              ·
                refine ⟨9436198842776719391397155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6290799228517812927598103 9436198842776719391397155)
                ·
                  refine ⟨14154298264165079087095733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9436198842776719391397155 14154298264165079087095733)
                  ·
                    refine ⟨1326965462265476164415225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14154298264165079087095733 1326965462265476164415225)
                    ·
                      rfl

theorem cell23_7752768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 1, 5].length) (baseStart_7752768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752768 prefixEnd_7752768 := by exact prefixLift 7752768
  have htrace : WordTrace (prefixWord ++ tailWord_7752768) baseStart_7752768 baseEnd_7752768 := by
    simpa [prefixWord, tailWord_7752768, baseEnd_7752768] using wordTrace_append hprefix tailTrace_7752768
  have hstable : (prefixWord ++ tailWord_7752768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752768).length < 2 ^ (prefixWord ++ tailWord_7752768).sum := by decide
  have hdescent : baseEnd_7752768 < baseStart_7752768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752784 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 6]
def baseStart_7752784 : Nat := 118140960795 + 7752784 * 2 ^ 59
def prefixEnd_7752784 : Nat := 4983230072969 + 3 ^ 40 * 7752784 * 2
def baseEnd_7752784 : Nat := 3980904602486900430645601

theorem tailTrace_7752784 : CollatzResearch.WordTrace tailWord_7752784 prefixEnd_7752784 3980904602486900430645601 := by
  unfold tailWord_7752784
  simp only [CollatzResearch.WordTrace]
  refine ⟨141383631372497556468852703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188511508496663408625136937 141383631372497556468852703)
  ·
    refine ⟨212075447058746334703279055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141383631372497556468852703 212075447058746334703279055)
    ·
      refine ⟨318113170588119502054918583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212075447058746334703279055 318113170588119502054918583)
      ·
        refine ⟨477169755882179253082377875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318113170588119502054918583 477169755882179253082377875)
        ·
          refine ⟨715754633823268879623566813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477169755882179253082377875 715754633823268879623566813)
          ·
            refine ⟨268407987683725829858837555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 715754633823268879623566813 268407987683725829858837555)
            ·
              refine ⟨402611981525588744788256333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268407987683725829858837555 402611981525588744788256333)
              ·
                refine ⟨150979493072095779295596125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 402611981525588744788256333 150979493072095779295596125)
                ·
                  refine ⟨56617309902035917235848547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150979493072095779295596125 56617309902035917235848547)
                  ·
                    refine ⟨84925964853053875853772821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56617309902035917235848547 84925964853053875853772821)
                    ·
                      refine ⟨3980904602486900430645601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84925964853053875853772821 3980904602486900430645601)
                      ·
                        rfl

theorem cell23_7752784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_7752784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752784 prefixEnd_7752784 := by exact prefixLift 7752784
  have htrace : WordTrace (prefixWord ++ tailWord_7752784) baseStart_7752784 baseEnd_7752784 := by
    simpa [prefixWord, tailWord_7752784, baseEnd_7752784] using wordTrace_append hprefix tailTrace_7752784
  have hstable : (prefixWord ++ tailWord_7752784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752784).length < 2 ^ (prefixWord ++ tailWord_7752784).sum := by decide
  have hdescent : baseEnd_7752784 < baseStart_7752784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752794 : List Nat := [3, 1, 1, 2, 1, 1, 2, 12]
def baseStart_7752794 : Nat := 118140960795 + 7752794 * 2 ^ 59
def prefixEnd_7752794 : Nat := 4983230072969 + 3 ^ 40 * 7752794 * 2
def baseEnd_7752794 : Nat := 147441101381238718204465

theorem tailTrace_7752794 : CollatzResearch.WordTrace tailWord_7752794 prefixEnd_7752794 147441101381238718204465 := by
  unfold tailWord_7752794
  simp only [CollatzResearch.WordTrace]
  refine ⟨70691906868739721161392359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188511751649972589763712957 70691906868739721161392359)
  ·
    refine ⟨106037860303109581742088539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70691906868739721161392359 106037860303109581742088539)
    ·
      refine ⟨159056790454664372613132809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106037860303109581742088539 159056790454664372613132809)
      ·
        refine ⟨119292592840998279459849607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159056790454664372613132809 119292592840998279459849607)
        ·
          refine ⟨178938889261497419189774411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119292592840998279459849607 178938889261497419189774411)
          ·
            refine ⟨268408333892246128784661617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178938889261497419189774411 268408333892246128784661617)
            ·
              refine ⟨201306250419184596588496213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268408333892246128784661617 201306250419184596588496213)
              ·
                refine ⟨147441101381238718204465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 201306250419184596588496213 147441101381238718204465)
                ·
                  rfl

theorem cell23_7752794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 12].length) (baseStart_7752794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752794 prefixEnd_7752794 := by exact prefixLift 7752794
  have htrace : WordTrace (prefixWord ++ tailWord_7752794) baseStart_7752794 baseEnd_7752794 := by
    simpa [prefixWord, tailWord_7752794, baseEnd_7752794] using wordTrace_append hprefix tailTrace_7752794
  have hstable : (prefixWord ++ tailWord_7752794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752794).length < 2 ^ (prefixWord ++ tailWord_7752794).sum := by decide
  have hdescent : baseEnd_7752794 < baseStart_7752794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752801 : List Nat := [1, 2, 3, 1, 1, 2, 3, 3, 1, 2, 4]
def baseStart_7752801 : Nat := 118140960795 + 7752801 * 2 ^ 59
def prefixEnd_7752801 : Nat := 4983230072969 + 3 ^ 40 * 7752801 * 2
def baseEnd_7752801 : Nat := 3980913331658026864133023

theorem tailTrace_7752801 : CollatzResearch.WordTrace tailWord_7752801 prefixEnd_7752801 3980913331658026864133023 := by
  unfold tailWord_7752801
  simp only [CollatzResearch.WordTrace]
  refine ⟨282767882785933524841074257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188511921857289016560716171 282767882785933524841074257)
  ·
    refine ⟨212075912089450143630805693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282767882785933524841074257 212075912089450143630805693)
    ·
      refine ⟨79528467033543803861552135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212075912089450143630805693 79528467033543803861552135)
      ·
        refine ⟨119292700550315705792328203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79528467033543803861552135 119292700550315705792328203)
        ·
          refine ⟨178939050825473558688492305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119292700550315705792328203 178939050825473558688492305)
          ·
            refine ⟨134204288119105169016369229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178939050825473558688492305 134204288119105169016369229)
            ·
              refine ⟨50326608044664438381138461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134204288119105169016369229 50326608044664438381138461)
              ·
                refine ⟨18872478016749164392926923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50326608044664438381138461 18872478016749164392926923)
                ·
                  refine ⟨28308717025123746589390385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18872478016749164392926923 28308717025123746589390385)
                  ·
                    refine ⟨21231537768842809942042789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28308717025123746589390385 21231537768842809942042789)
                    ·
                      refine ⟨3980913331658026864133023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21231537768842809942042789 3980913331658026864133023)
                      ·
                        rfl

theorem cell23_7752801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_7752801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752801 prefixEnd_7752801 := by exact prefixLift 7752801
  have htrace : WordTrace (prefixWord ++ tailWord_7752801) baseStart_7752801 baseEnd_7752801 := by
    simpa [prefixWord, tailWord_7752801, baseEnd_7752801] using wordTrace_append hprefix tailTrace_7752801
  have hstable : (prefixWord ++ tailWord_7752801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752801).length < 2 ^ (prefixWord ++ tailWord_7752801).sum := by decide
  have hdescent : baseEnd_7752801 < baseStart_7752801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752805 : List Nat := [1, 3, 1, 3, 2, 1, 3, 2, 3, 2, 2]
def baseStart_7752805 : Nat := 118140960795 + 7752805 * 2 ^ 59
def prefixEnd_7752805 : Nat := 4983230072969 + 3 ^ 40 * 7752805 * 2
def baseEnd_7752805 : Nat := 3980915385580644848483005

theorem tailTrace_7752805 : CollatzResearch.WordTrace tailWord_7752805 prefixEnd_7752805 3980915385580644848483005 := by
  unfold tailWord_7752805
  simp only [CollatzResearch.WordTrace]
  refine ⟨282768028677919033524219869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188512019118612689016146579 282768028677919033524219869)
  ·
    refine ⟨106038010754219637571582451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282768028677919033524219869 106038010754219637571582451)
    ·
      refine ⟨159057016131329456357373677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106038010754219637571582451 159057016131329456357373677)
      ·
        refine ⟨59646381049248546134015129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159057016131329456357373677 59646381049248546134015129)
        ·
          refine ⟨44734785786936409600511347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59646381049248546134015129 44734785786936409600511347)
          ·
            refine ⟨67102178680404614400767021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44734785786936409600511347 67102178680404614400767021)
            ·
              refine ⟨25163317005151730400287633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67102178680404614400767021 25163317005151730400287633)
              ·
                refine ⟨18872487753863797800215725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25163317005151730400287633 18872487753863797800215725)
                ·
                  refine ⟨7077182907698924175080897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18872487753863797800215725 7077182907698924175080897)
                  ·
                    refine ⟨5307887180774193131310673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7077182907698924175080897 5307887180774193131310673)
                    ·
                      refine ⟨3980915385580644848483005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5307887180774193131310673 3980915385580644848483005)
                      ·
                        rfl

theorem cell23_7752805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_7752805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752805 prefixEnd_7752805 := by exact prefixLift 7752805
  have htrace : WordTrace (prefixWord ++ tailWord_7752805) baseStart_7752805 baseEnd_7752805 := by
    simpa [prefixWord, tailWord_7752805, baseEnd_7752805] using wordTrace_append hprefix tailTrace_7752805
  have hstable : (prefixWord ++ tailWord_7752805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752805).length < 2 ^ (prefixWord ++ tailWord_7752805).sum := by decide
  have hdescent : baseEnd_7752805 < baseStart_7752805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752825 : List Nat := [1, 2, 1, 3, 5, 1, 1, 3, 1, 2, 3]
def baseStart_7752825 : Nat := 118140960795 + 7752825 * 2 ^ 59
def prefixEnd_7752825 : Nat := 4983230072969 + 3 ^ 40 * 7752825 * 2
def baseEnd_7752825 : Nat := 3980925655193734770232913

theorem tailTrace_7752825 : CollatzResearch.WordTrace tailWord_7752825 prefixEnd_7752825 3980925655193734770232913 := by
  unfold tailWord_7752825
  simp only [CollatzResearch.WordTrace]
  refine ⟨282768758137846576939947929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188512505425231051293298619 282768758137846576939947929)
  ·
    refine ⟨212076568603384932704960947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282768758137846576939947929 212076568603384932704960947)
    ·
      refine ⟨318114852905077399057441421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212076568603384932704960947 318114852905077399057441421)
      ·
        refine ⟨119293069839404024646540533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318114852905077399057441421 119293069839404024646540533)
        ·
          refine ⟨11183725297444127310613175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119293069839404024646540533 11183725297444127310613175)
          ·
            refine ⟨16775587946166190965919763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11183725297444127310613175 16775587946166190965919763)
            ·
              refine ⟨25163381919249286448879645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16775587946166190965919763 25163381919249286448879645)
              ·
                refine ⟨9436268219718482418329867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25163381919249286448879645 9436268219718482418329867)
                ·
                  refine ⟨14154402329577723627494801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9436268219718482418329867 14154402329577723627494801)
                  ·
                    refine ⟨10615801747183292720621101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14154402329577723627494801 10615801747183292720621101)
                    ·
                      refine ⟨3980925655193734770232913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10615801747183292720621101 3980925655193734770232913)
                      ·
                        rfl

theorem cell23_7752825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_7752825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752825 prefixEnd_7752825 := by exact prefixLift 7752825
  have htrace : WordTrace (prefixWord ++ tailWord_7752825) baseStart_7752825 baseEnd_7752825 := by
    simpa [prefixWord, tailWord_7752825, baseEnd_7752825] using wordTrace_append hprefix tailTrace_7752825
  have hstable : (prefixWord ++ tailWord_7752825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752825).length < 2 ^ (prefixWord ++ tailWord_7752825).sum := by decide
  have hdescent : baseEnd_7752825 < baseStart_7752825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752848 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 3, 3, 2]
def baseStart_7752848 : Nat := 118140960795 + 7752848 * 2 ^ 59
def prefixEnd_7752848 : Nat := 4983230072969 + 3 ^ 40 * 7752848 * 2
def baseEnd_7752848 : Nat := 3980937465248788180245307

theorem tailTrace_7752848 : CollatzResearch.WordTrace tailWord_7752848 prefixEnd_7752848 3980937465248788180245307 := by
  unfold tailWord_7752848
  simp only [CollatzResearch.WordTrace]
  refine ⟨141384798508381625934017599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188513064677842167912023465 141384798508381625934017599)
  ·
    refine ⟨212077197762572438901026399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141384798508381625934017599 212077197762572438901026399)
    ·
      refine ⟨318115796643858658351539599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212077197762572438901026399 318115796643858658351539599)
      ·
        refine ⟨477173694965787987527309399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318115796643858658351539599 477173694965787987527309399)
        ·
          refine ⟨715760542448681981290964099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477173694965787987527309399 715760542448681981290964099)
          ·
            refine ⟨1073640813673022971936446149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715760542448681981290964099 1073640813673022971936446149)
            ·
              refine ⟨201307652563691807238083653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1073640813673022971936446149 201307652563691807238083653)
              ·
                refine ⟨37745184855692213857140685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201307652563691807238083653 37745184855692213857140685)
                ·
                  refine ⟨14154444320884580196427757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37745184855692213857140685 14154444320884580196427757)
                  ·
                    refine ⟨5307916620331717573660409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14154444320884580196427757 5307916620331717573660409)
                    ·
                      refine ⟨3980937465248788180245307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5307916620331717573660409 3980937465248788180245307)
                      ·
                        rfl

theorem cell23_7752848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 3, 3, 2].length) (baseStart_7752848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752848 prefixEnd_7752848 := by exact prefixLift 7752848
  have htrace : WordTrace (prefixWord ++ tailWord_7752848) baseStart_7752848 baseEnd_7752848 := by
    simpa [prefixWord, tailWord_7752848, baseEnd_7752848] using wordTrace_append hprefix tailTrace_7752848
  have hstable : (prefixWord ++ tailWord_7752848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752848).length < 2 ^ (prefixWord ++ tailWord_7752848).sum := by decide
  have hdescent : baseEnd_7752848 < baseStart_7752848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752855 : List Nat := [1, 1, 3, 3, 3, 3, 1, 1, 1, 3, 3]
def baseStart_7752855 : Nat := 118140960795 + 7752855 * 2 ^ 59
def prefixEnd_7752855 : Nat := 4983230072969 + 3 ^ 40 * 7752855 * 2
def baseEnd_7752855 : Nat := 3980941059613369652857775

theorem tailTrace_7752855 : CollatzResearch.WordTrace tailWord_7752855 prefixEnd_7752855 3980941059613369652857775 := by
  unfold tailWord_7752855
  simp only [CollatzResearch.WordTrace]
  refine ⟨282769852327737892063540019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188513234885158594709026679 282769852327737892063540019)
  ·
    refine ⟨424154778491606838095310029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282769852327737892063540019 424154778491606838095310029)
    ·
      refine ⟨159058041934352564285741261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424154778491606838095310029 159058041934352564285741261)
      ·
        refine ⟨59646765725382211607152973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159058041934352564285741261 59646765725382211607152973)
        ·
          refine ⟨22367537147018329352682365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59646765725382211607152973 22367537147018329352682365)
          ·
            refine ⟨8387826430131873507255887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22367537147018329352682365 8387826430131873507255887)
            ·
              refine ⟨12581739645197810260883831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8387826430131873507255887 12581739645197810260883831)
              ·
                refine ⟨18872609467796715391325747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12581739645197810260883831 18872609467796715391325747)
                ·
                  refine ⟨28308914201695073086988621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18872609467796715391325747 28308914201695073086988621)
                  ·
                    refine ⟨10615842825635652407620733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28308914201695073086988621 10615842825635652407620733)
                    ·
                      refine ⟨3980941059613369652857775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10615842825635652407620733 3980941059613369652857775)
                      ·
                        rfl

theorem cell23_7752855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_7752855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752855 prefixEnd_7752855 := by exact prefixLift 7752855
  have htrace : WordTrace (prefixWord ++ tailWord_7752855) baseStart_7752855 baseEnd_7752855 := by
    simpa [prefixWord, tailWord_7752855, baseEnd_7752855] using wordTrace_append hprefix tailTrace_7752855
  have hstable : (prefixWord ++ tailWord_7752855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752855).length < 2 ^ (prefixWord ++ tailWord_7752855).sum := by decide
  have hdescent : baseEnd_7752855 < baseStart_7752855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752891 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 4]
def baseStart_7752891 : Nat := 118140960795 + 7752891 * 2 ^ 59
def prefixEnd_7752891 : Nat := 4983230072969 + 3 ^ 40 * 7752891 * 2
def baseEnd_7752891 : Nat := 3980959544916931512007609

theorem tailTrace_7752891 : CollatzResearch.WordTrace tailWord_7752891 prefixEnd_7752891 3980959544916931512007609 := by
  unfold tailWord_7752891
  simp only [CollatzResearch.WordTrace]
  refine ⟨282771165355607470211850527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188514110237071646807900351 282771165355607470211850527)
  ·
    refine ⟨424156748033411205317775791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282771165355607470211850527 424156748033411205317775791)
    ·
      refine ⟨636235122050116807976663687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424156748033411205317775791 636235122050116807976663687)
      ·
        refine ⟨954352683075175211964995531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636235122050116807976663687 954352683075175211964995531)
        ·
          refine ⟨1431529024612762817947493297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 954352683075175211964995531 1431529024612762817947493297)
          ·
            refine ⟨1073646768459572113460619973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1431529024612762817947493297 1073646768459572113460619973)
            ·
              refine ⟨201308769086169771273866245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1073646768459572113460619973 201308769086169771273866245)
              ·
                refine ⟨37745394203656832113849921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201308769086169771273866245 37745394203656832113849921)
                ·
                  refine ⟨28309045652742624085387441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37745394203656832113849921 28309045652742624085387441)
                  ·
                    refine ⟨21231784239556968064040581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28309045652742624085387441 21231784239556968064040581)
                    ·
                      refine ⟨3980959544916931512007609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21231784239556968064040581 3980959544916931512007609)
                      ·
                        rfl

theorem cell23_7752891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 4].length) (baseStart_7752891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752891 prefixEnd_7752891 := by exact prefixLift 7752891
  have htrace : WordTrace (prefixWord ++ tailWord_7752891) baseStart_7752891 baseEnd_7752891 := by
    simpa [prefixWord, tailWord_7752891, baseEnd_7752891] using wordTrace_append hprefix tailTrace_7752891
  have hstable : (prefixWord ++ tailWord_7752891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752891).length < 2 ^ (prefixWord ++ tailWord_7752891).sum := by decide
  have hdescent : baseEnd_7752891 < baseStart_7752891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752895 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 4, 2, 2]
def baseStart_7752895 : Nat := 118140960795 + 7752895 * 2 ^ 59
def prefixEnd_7752895 : Nat := 4983230072969 + 3 ^ 40 * 7752895 * 2
def baseEnd_7752895 : Nat := 3980961598839549496357591

theorem tailTrace_7752895 : CollatzResearch.WordTrace tailWord_7752895 prefixEnd_7752895 3980961598839549496357591 := by
  unfold tailWord_7752895
  simp only [CollatzResearch.WordTrace]
  refine ⟨282771311247592978894996139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188514207498395319263330759 282771311247592978894996139)
  ·
    refine ⟨424156966871389468342494209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282771311247592978894996139 424156966871389468342494209)
    ·
      refine ⟨318117725153542101256870657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424156966871389468342494209 318117725153542101256870657)
      ·
        refine ⟨238588293865156575942652993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318117725153542101256870657 238588293865156575942652993)
        ·
          refine ⟨178941220398867431956989745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238588293865156575942652993 178941220398867431956989745)
          ·
            refine ⟨134205915299150573967742309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178941220398867431956989745 134205915299150573967742309)
            ·
              refine ⟨25163609118590732618951683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134205915299150573967742309 25163609118590732618951683)
              ·
                refine ⟨37745413677886098928427525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25163609118590732618951683 37745413677886098928427525)
                ·
                  refine ⟨7077265064603643549080161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37745413677886098928427525 7077265064603643549080161)
                  ·
                    refine ⟨5307948798452732661810121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7077265064603643549080161 5307948798452732661810121)
                    ·
                      refine ⟨3980961598839549496357591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5307948798452732661810121 3980961598839549496357591)
                      ·
                        rfl

theorem cell23_7752895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 2, 2].length) (baseStart_7752895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752895 prefixEnd_7752895 := by exact prefixLift 7752895
  have htrace : WordTrace (prefixWord ++ tailWord_7752895) baseStart_7752895 baseEnd_7752895 := by
    simpa [prefixWord, tailWord_7752895, baseEnd_7752895] using wordTrace_append hprefix tailTrace_7752895
  have hstable : (prefixWord ++ tailWord_7752895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752895).length < 2 ^ (prefixWord ++ tailWord_7752895).sum := by decide
  have hdescent : baseEnd_7752895 < baseStart_7752895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752916 : List Nat := [2, 4, 1, 4, 1, 2, 1, 2, 1, 3, 2]
def baseStart_7752916 : Nat := 118140960795 + 7752916 * 2 ^ 59
def prefixEnd_7752916 : Nat := 4983230072969 + 3 ^ 40 * 7752916 * 2
def baseEnd_7752916 : Nat := 3980972381933293914194995

theorem tailTrace_7752916 : CollatzResearch.WordTrace tailWord_7752916 prefixEnd_7752916 3980972381933293914194995 := by
  unfold tailWord_7752916
  simp only [CollatzResearch.WordTrace]
  refine ⟨141386038590258449740755301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188514718120344599654340401 141386038590258449740755301)
  ·
    refine ⟨26509882235673459326391619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141386038590258449740755301 26509882235673459326391619)
    ·
      refine ⟨39764823353510188989587429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26509882235673459326391619 39764823353510188989587429)
      ·
        refine ⟨7455904378783160435547643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39764823353510188989587429 7455904378783160435547643)
        ·
          refine ⟨11183856568174740653321465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7455904378783160435547643 11183856568174740653321465)
          ·
            refine ⟨8387892426131055489991099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11183856568174740653321465 8387892426131055489991099)
            ·
              refine ⟨12581838639196583234986649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8387892426131055489991099 12581838639196583234986649)
              ·
                refine ⟨9436378979397437426239987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12581838639196583234986649 9436378979397437426239987)
                ·
                  refine ⟨14154568469096156139359981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9436378979397437426239987 14154568469096156139359981)
                  ·
                    refine ⟨5307963175911058552259993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14154568469096156139359981 5307963175911058552259993)
                    ·
                      refine ⟨3980972381933293914194995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5307963175911058552259993 3980972381933293914194995)
                      ·
                        rfl

theorem cell23_7752916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_7752916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752916 prefixEnd_7752916 := by exact prefixLift 7752916
  have htrace : WordTrace (prefixWord ++ tailWord_7752916) baseStart_7752916 baseEnd_7752916 := by
    simpa [prefixWord, tailWord_7752916, baseEnd_7752916] using wordTrace_append hprefix tailTrace_7752916
  have hstable : (prefixWord ++ tailWord_7752916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752916).length < 2 ^ (prefixWord ++ tailWord_7752916).sum := by decide
  have hdescent : baseEnd_7752916 < baseStart_7752916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7752962 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_7752962 : Nat := 118140960795 + 7752962 * 2 ^ 59
def prefixEnd_7752962 : Nat := 4983230072969 + 3 ^ 40 * 7752962 * 2
def baseEnd_7752962 : Nat := 3980996002043400734219783

theorem tailTrace_7752962 : CollatzResearch.WordTrace tailWord_7752962 prefixEnd_7752962 3980996002043400734219783 := by
  unfold tailWord_7752962
  simp only [CollatzResearch.WordTrace]
  refine ⟨70693438734587562334421285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188515836625566832891790093 70693438734587562334421285)
  ·
    refine ⟨13255019762735167937703991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70693438734587562334421285 13255019762735167937703991)
    ·
      refine ⟨19882529644102751906555987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13255019762735167937703991 19882529644102751906555987)
      ·
        refine ⟨29823794466154127859833981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19882529644102751906555987 29823794466154127859833981)
        ·
          refine ⟨11183922924807797947437743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29823794466154127859833981 11183922924807797947437743)
          ·
            refine ⟨16775884387211696921156615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11183922924807797947437743 16775884387211696921156615)
            ·
              refine ⟨25163826580817545381734923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16775884387211696921156615 25163826580817545381734923)
              ·
                refine ⟨37745739871226318072602385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25163826580817545381734923 37745739871226318072602385)
                ·
                  refine ⟨28309304903419738554451789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37745739871226318072602385 28309304903419738554451789)
                  ·
                    refine ⟨10615989338782401957919421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28309304903419738554451789 10615989338782401957919421)
                    ·
                      refine ⟨3980996002043400734219783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10615989338782401957919421 3980996002043400734219783)
                      ·
                        rfl

theorem cell23_7752962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_7752962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7752962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7752962 prefixEnd_7752962 := by exact prefixLift 7752962
  have htrace : WordTrace (prefixWord ++ tailWord_7752962) baseStart_7752962 baseEnd_7752962 := by
    simpa [prefixWord, tailWord_7752962, baseEnd_7752962] using wordTrace_append hprefix tailTrace_7752962
  have hstable : (prefixWord ++ tailWord_7752962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7752962).length < 2 ^ (prefixWord ++ tailWord_7752962).sum := by decide
  have hdescent : baseEnd_7752962 < baseStart_7752962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7752962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753002 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 2, 4, 2]
def baseStart_7753002 : Nat := 118140960795 + 7753002 * 2 ^ 59
def prefixEnd_7753002 : Nat := 4983230072969 + 3 ^ 40 * 7753002 * 2
def baseEnd_7753002 : Nat := 3981016541269580577719599

theorem tailTrace_7753002 : CollatzResearch.WordTrace tailWord_7753002 prefixEnd_7753002 3981016541269580577719599 := by
  unfold tailWord_7753002
  simp only [CollatzResearch.WordTrace]
  refine ⟨70693803464551334042285315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188516809238803557446094173 70693803464551334042285315)
  ·
    refine ⟨106040705196827001063427973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70693803464551334042285315 106040705196827001063427973)
    ·
      refine ⟨19882632224405062699392745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106040705196827001063427973 19882632224405062699392745)
      ·
        refine ⟨14911974168303797024544559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19882632224405062699392745 14911974168303797024544559)
        ·
          refine ⟨22367961252455695536816839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14911974168303797024544559 22367961252455695536816839)
          ·
            refine ⟨33551941878683543305225259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22367961252455695536816839 33551941878683543305225259)
            ·
              refine ⟨50327912818025314957837889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33551941878683543305225259 50327912818025314957837889)
              ·
                refine ⟨37745934613518986218378417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50327912818025314957837889 37745934613518986218378417)
                ·
                  refine ⟨28309450960139239663783813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37745934613518986218378417 28309450960139239663783813)
                  ·
                    refine ⟨5308022055026107436959465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28309450960139239663783813 5308022055026107436959465)
                    ·
                      refine ⟨3981016541269580577719599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5308022055026107436959465 3981016541269580577719599)
                      ·
                        rfl

theorem cell23_7753002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_7753002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753002 prefixEnd_7753002 := by exact prefixLift 7753002
  have htrace : WordTrace (prefixWord ++ tailWord_7753002) baseStart_7753002 baseEnd_7753002 := by
    simpa [prefixWord, tailWord_7753002, baseEnd_7753002] using wordTrace_append hprefix tailTrace_7753002
  have hstable : (prefixWord ++ tailWord_7753002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753002).length < 2 ^ (prefixWord ++ tailWord_7753002).sum := by decide
  have hdescent : baseEnd_7753002 < baseStart_7753002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753012 : List Nat := [2, 5, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_7753012 : Nat := 118140960795 + 7753012 * 2 ^ 59
def prefixEnd_7753012 : Nat := 4983230072969 + 3 ^ 40 * 7753012 * 2
def baseEnd_7753012 : Nat := 1327007225358708512864851

theorem tailTrace_7753012 : CollatzResearch.WordTrace tailWord_7753012 prefixEnd_7753012 1327007225358708512864851 := by
  unfold tailWord_7753012
  simp only [CollatzResearch.WordTrace]
  refine ⟨141387789294084553938502645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188517052392112738584670193 141387789294084553938502645)
  ·
    refine ⟨13255105246320426931734623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141387789294084553938502645 13255105246320426931734623)
    ·
      refine ⟨19882657869480640397601935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13255105246320426931734623 19882657869480640397601935)
      ·
        refine ⟨29823986804220960596402903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19882657869480640397601935 29823986804220960596402903)
        ·
          refine ⟨44735980206331440894604355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29823986804220960596402903 44735980206331440894604355)
          ·
            refine ⟨67103970309497161341906533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44735980206331440894604355 67103970309497161341906533)
            ·
              refine ⟨12581994433030717751607475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67103970309497161341906533 12581994433030717751607475)
              ·
                refine ⟨18872991649546076627411213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12581994433030717751607475 18872991649546076627411213)
                ·
                  refine ⟨7077371868579778735279205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18872991649546076627411213 7077371868579778735279205)
                  ·
                    refine ⟨1327007225358708512864851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7077371868579778735279205 1327007225358708512864851)
                    ·
                      rfl

theorem cell23_7753012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_7753012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753012 prefixEnd_7753012 := by exact prefixLift 7753012
  have htrace : WordTrace (prefixWord ++ tailWord_7753012) baseStart_7753012 baseEnd_7753012 := by
    simpa [prefixWord, tailWord_7753012, baseEnd_7753012] using wordTrace_append hprefix tailTrace_7753012
  have hstable : (prefixWord ++ tailWord_7753012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753012).length < 2 ^ (prefixWord ++ tailWord_7753012).sum := by decide
  have hdescent : baseEnd_7753012 < baseStart_7753012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753069 : List Nat := [1, 5, 1, 1, 1, 5, 1, 1, 3, 1, 3]
def baseStart_7753069 : Nat := 118140960795 + 7753069 * 2 ^ 59
def prefixEnd_7753069 : Nat := 4983230072969 + 3 ^ 40 * 7753069 * 2
def baseEnd_7753069 : Nat := 3981050944473431815581791

theorem tailTrace_7753069 : CollatzResearch.WordTrace tailWord_7753069 prefixEnd_7753069 3981050944473431815581791 := by
  unfold tailWord_7753069
  simp only [CollatzResearch.WordTrace]
  refine ⟨282777657548962606611830261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188518438365975071074553507 282777657548962606611830261)
  ·
    refine ⟨26510405395215244369859087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 282777657548962606611830261 26510405395215244369859087)
    ·
      refine ⟨39765608092822866554788631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26510405395215244369859087 39765608092822866554788631)
      ·
        refine ⟨59648412139234299832182947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39765608092822866554788631 59648412139234299832182947)
        ·
          refine ⟨89472618208851449748274421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59648412139234299832182947 89472618208851449748274421)
          ·
            refine ⟨8388057957079823413900727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89472618208851449748274421 8388057957079823413900727)
            ·
              refine ⟨12582086935619735120851091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8388057957079823413900727 12582086935619735120851091)
              ·
                refine ⟨18873130403429602681276637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12582086935619735120851091 18873130403429602681276637)
                ·
                  refine ⟨7077423901286101005478739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18873130403429602681276637 7077423901286101005478739)
                  ·
                    refine ⟨10616135851929151508218109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7077423901286101005478739 10616135851929151508218109)
                    ·
                      refine ⟨3981050944473431815581791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10616135851929151508218109 3981050944473431815581791)
                      ·
                        rfl

theorem cell23_7753069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_7753069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753069 prefixEnd_7753069 := by exact prefixLift 7753069
  have htrace : WordTrace (prefixWord ++ tailWord_7753069) baseStart_7753069 baseEnd_7753069 := by
    simpa [prefixWord, tailWord_7753069, baseEnd_7753069] using wordTrace_append hprefix tailTrace_7753069
  have hstable : (prefixWord ++ tailWord_7753069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753069).length < 2 ^ (prefixWord ++ tailWord_7753069).sum := by decide
  have hdescent : baseEnd_7753069 < baseStart_7753069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753088 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 4]
def baseStart_7753088 : Nat := 118140960795 + 7753088 * 2 ^ 59
def prefixEnd_7753088 : Nat := 4983230072969 + 3 ^ 40 * 7753088 * 2
def baseEnd_7753088 : Nat := 3981060700605867241244203

theorem tailTrace_7753088 : CollatzResearch.WordTrace tailWord_7753088 prefixEnd_7753088 3981060700605867241244203 := by
  unfold tailWord_7753088
  simp only [CollatzResearch.WordTrace]
  refine ⟨141389175267946886428385959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188518900357262515237847945 141389175267946886428385959)
  ·
    refine ⟨212083762901920329642578939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141389175267946886428385959 212083762901920329642578939)
    ·
      refine ⟨318125644352880494463868409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212083762901920329642578939 318125644352880494463868409)
      ·
        refine ⟨238594233264660370847901307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318125644352880494463868409 238594233264660370847901307)
        ·
          refine ⟨357891349896990556271851961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238594233264660370847901307 357891349896990556271851961)
          ·
            refine ⟨268418512422742917203888971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357891349896990556271851961 268418512422742917203888971)
            ·
              refine ⟨402627768634114375805833457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268418512422742917203888971 402627768634114375805833457)
              ·
                refine ⟨301970826475585781854375093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402627768634114375805833457 301970826475585781854375093)
                ·
                  refine ⟨28309764982086167048847665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 301970826475585781854375093 28309764982086167048847665)
                  ·
                    refine ⟨21232323736564625286635749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28309764982086167048847665 21232323736564625286635749)
                    ·
                      refine ⟨3981060700605867241244203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21232323736564625286635749 3981060700605867241244203)
                      ·
                        rfl

theorem cell23_7753088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_7753088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753088 prefixEnd_7753088 := by exact prefixLift 7753088
  have htrace : WordTrace (prefixWord ++ tailWord_7753088) baseStart_7753088 baseEnd_7753088 := by
    simpa [prefixWord, tailWord_7753088, baseEnd_7753088] using wordTrace_append hprefix tailTrace_7753088
  have hstable : (prefixWord ++ tailWord_7753088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753088).length < 2 ^ (prefixWord ++ tailWord_7753088).sum := by decide
  have hdescent : baseEnd_7753088 < baseStart_7753088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753089 : List Nat := [1, 2, 4, 3, 2, 2, 1, 2, 1, 5]
def baseStart_7753089 : Nat := 118140960795 + 7753089 * 2 ^ 59
def prefixEnd_7753089 : Nat := 4983230072969 + 3 ^ 40 * 7753089 * 2
def baseEnd_7753089 : Nat := 1327020404695507245777233

theorem tailTrace_7753089 : CollatzResearch.WordTrace tailWord_7753089 prefixEnd_7753089 1327020404695507245777233 := by
  unfold tailWord_7753089
  simp only [CollatzResearch.WordTrace]
  refine ⟨282778387008890150027558321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188518924672593433351705547 282778387008890150027558321)
  ·
    refine ⟨212083790256667612520668741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282778387008890150027558321 212083790256667612520668741)
    ·
      refine ⟨39765710673125177347625389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212083790256667612520668741 39765710673125177347625389)
      ·
        refine ⟨14912141502421941505359521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39765710673125177347625389 14912141502421941505359521)
        ·
          refine ⟨11184106126816456129019641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14912141502421941505359521 11184106126816456129019641)
          ·
            refine ⟨8388079595112342096764731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11184106126816456129019641 8388079595112342096764731)
            ·
              refine ⟨12582119392668513145147097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8388079595112342096764731 12582119392668513145147097)
              ·
                refine ⟨9436589544501384858860323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12582119392668513145147097 9436589544501384858860323)
                ·
                  refine ⟨14154884316752077288290485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9436589544501384858860323 14154884316752077288290485)
                  ·
                    refine ⟨1327020404695507245777233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14154884316752077288290485 1327020404695507245777233)
                    ·
                      rfl

theorem cell23_7753089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_7753089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753089 prefixEnd_7753089 := by exact prefixLift 7753089
  have htrace : WordTrace (prefixWord ++ tailWord_7753089) baseStart_7753089 baseEnd_7753089 := by
    simpa [prefixWord, tailWord_7753089, baseEnd_7753089] using wordTrace_append hprefix tailTrace_7753089
  have hstable : (prefixWord ++ tailWord_7753089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753089).length < 2 ^ (prefixWord ++ tailWord_7753089).sum := by decide
  have hdescent : baseEnd_7753089 < baseStart_7753089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753092 : List Nat := [2, 3, 2, 1, 1, 3, 3, 2, 1, 1, 4]
def baseStart_7753092 : Nat := 118140960795 + 7753092 * 2 ^ 59
def prefixEnd_7753092 : Nat := 4983230072969 + 3 ^ 40 * 7753092 * 2
def baseEnd_7753092 : Nat := 3981062754528485225594185

theorem tailTrace_7753092 : CollatzResearch.WordTrace tailWord_7753092 prefixEnd_7753092 3981062754528485225594185 := by
  unfold tailWord_7753092
  simp only [CollatzResearch.WordTrace]
  refine ⟨141389248213939640769958765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188518997618586187693278353 141389248213939640769958765)
  ·
    refine ⟨53020968080227365288734537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141389248213939640769958765 53020968080227365288734537)
    ·
      refine ⟨39765726060170523966550903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53020968080227365288734537 39765726060170523966550903)
      ·
        refine ⟨59648589090255785949826355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39765726060170523966550903 59648589090255785949826355)
        ·
          refine ⟨89472883635383678924739533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59648589090255785949826355 89472883635383678924739533)
          ·
            refine ⟨33552331363268879596777325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89472883635383678924739533 33552331363268879596777325)
            ·
              refine ⟨12582124261225829848791497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33552331363268879596777325 12582124261225829848791497)
              ·
                refine ⟨9436593195919372386593623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12582124261225829848791497 9436593195919372386593623)
                ·
                  refine ⟨14154889793879058579890435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9436593195919372386593623 14154889793879058579890435)
                  ·
                    refine ⟨21232334690818587869835653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14154889793879058579890435 21232334690818587869835653)
                    ·
                      refine ⟨3981062754528485225594185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21232334690818587869835653 3981062754528485225594185)
                      ·
                        rfl

theorem cell23_7753092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_7753092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753092 prefixEnd_7753092 := by exact prefixLift 7753092
  have htrace : WordTrace (prefixWord ++ tailWord_7753092) baseStart_7753092 baseEnd_7753092 := by
    simpa [prefixWord, tailWord_7753092, baseEnd_7753092] using wordTrace_append hprefix tailTrace_7753092
  have hstable : (prefixWord ++ tailWord_7753092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753092).length < 2 ^ (prefixWord ++ tailWord_7753092).sum := by decide
  have hdescent : baseEnd_7753092 < baseStart_7753092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753102 : List Nat := [4, 1, 1, 4, 2, 1, 1, 2, 1, 6]
def baseStart_7753102 : Nat := 118140960795 + 7753102 * 2 ^ 59
def prefixEnd_7753102 : Nat := 4983230072969 + 3 ^ 40 * 7753102 * 2
def baseEnd_7753102 : Nat := 1327022629778343395489713

theorem tailTrace_7753102 : CollatzResearch.WordTrace tailWord_7753102 prefixEnd_7753102 1327022629778343395489713 := by
  unfold tailWord_7753102
  simp only [CollatzResearch.WordTrace]
  refine ⟨35347357644730381655972695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188519240771895368831854373 35347357644730381655972695)
  ·
    refine ⟨53021036467095572483959043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35347357644730381655972695 53021036467095572483959043)
    ·
      refine ⟨79531554700643358725938565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53021036467095572483959043 79531554700643358725938565)
      ·
        refine ⟨14912166506370629761113481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79531554700643358725938565 14912166506370629761113481)
        ·
          refine ⟨11184124879777972320835111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14912166506370629761113481 11184124879777972320835111)
          ·
            refine ⟨16776187319666958481252667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11184124879777972320835111 16776187319666958481252667)
            ·
              refine ⟨25164280979500437721879001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16776187319666958481252667 25164280979500437721879001)
              ·
                refine ⟨18873210734625328291409251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25164280979500437721879001 18873210734625328291409251)
                ·
                  refine ⟨28309816101937992437113877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18873210734625328291409251 28309816101937992437113877)
                  ·
                    refine ⟨1327022629778343395489713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28309816101937992437113877 1327022629778343395489713)
                    ·
                      rfl

theorem cell23_7753102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_7753102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753102 prefixEnd_7753102 := by exact prefixLift 7753102
  have htrace : WordTrace (prefixWord ++ tailWord_7753102) baseStart_7753102 baseEnd_7753102 := by
    simpa [prefixWord, tailWord_7753102, baseEnd_7753102] using wordTrace_append hprefix tailTrace_7753102
  have hstable : (prefixWord ++ tailWord_7753102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753102).length < 2 ^ (prefixWord ++ tailWord_7753102).sum := by decide
  have hdescent : baseEnd_7753102 < baseStart_7753102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753106 : List Nat := [3, 2, 3, 3, 1, 1, 3, 1, 1, 5]
def baseStart_7753106 : Nat := 118140960795 + 7753106 * 2 ^ 59
def prefixEnd_7753106 : Nat := 4983230072969 + 3 ^ 40 * 7753106 * 2
def baseEnd_7753106 : Nat := 1327023314419216056939707

theorem tailTrace_7753106 : CollatzResearch.WordTrace tailWord_7753106 prefixEnd_7753106 1327023314419216056939707 := by
  unfold tailWord_7753106
  simp only [CollatzResearch.WordTrace]
  refine ⟨70694751762457140482731793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188519338033219041287284781 70694751762457140482731793)
  ·
    refine ⟨53021063821842855362048845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70694751762457140482731793 53021063821842855362048845)
    ·
      refine ⟨19882898933191070760768317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53021063821842855362048845 19882898933191070760768317)
      ·
        refine ⟨7456087099946651535288119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19882898933191070760768317 7456087099946651535288119)
        ·
          refine ⟨11184130649919977302932179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7456087099946651535288119 11184130649919977302932179)
          ·
            refine ⟨16776195974879965954398269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11184130649919977302932179 16776195974879965954398269)
            ·
              refine ⟨6291073490579987232899351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16776195974879965954398269 6291073490579987232899351)
              ·
                refine ⟨9436610235869980849349027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6291073490579987232899351 9436610235869980849349027)
                ·
                  refine ⟨14154915353804971274023541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9436610235869980849349027 14154915353804971274023541)
                  ·
                    refine ⟨1327023314419216056939707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14154915353804971274023541 1327023314419216056939707)
                    ·
                      rfl

theorem cell23_7753106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_7753106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753106 prefixEnd_7753106 := by exact prefixLift 7753106
  have htrace : WordTrace (prefixWord ++ tailWord_7753106) baseStart_7753106 baseEnd_7753106 := by
    simpa [prefixWord, tailWord_7753106, baseEnd_7753106] using wordTrace_append hprefix tailTrace_7753106
  have hstable : (prefixWord ++ tailWord_7753106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753106).length < 2 ^ (prefixWord ++ tailWord_7753106).sum := by decide
  have hdescent : baseEnd_7753106 < baseStart_7753106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753152 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 3, 3, 2]
def baseStart_7753152 : Nat := 118140960795 + 7753152 * 2 ^ 59
def prefixEnd_7753152 : Nat := 4983230072969 + 3 ^ 40 * 7753152 * 2
def baseEnd_7753152 : Nat := 3981093563367754990843909

theorem tailTrace_7753152 : CollatzResearch.WordTrace tailWord_7753152 prefixEnd_7753152 3981093563367754990843909 := by
  unfold tailWord_7753152
  simp only [CollatzResearch.WordTrace]
  refine ⟨141390342403830955893550855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188520456538441274524734473 141390342403830955893550855)
  ·
    refine ⟨212085513605746433840326283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141390342403830955893550855 212085513605746433840326283)
    ·
      refine ⟨318128270408619650760489425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212085513605746433840326283 318128270408619650760489425)
      ·
        refine ⟨238596202806464738070367069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318128270408619650760489425 238596202806464738070367069)
        ·
          refine ⟨89473576052424276776387651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238596202806464738070367069 89473576052424276776387651)
          ·
            refine ⟨134210364078636415164581477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89473576052424276776387651 134210364078636415164581477)
            ·
              refine ⟨25164443264744327843359027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134210364078636415164581477 25164443264744327843359027)
              ·
                refine ⟨37746664897116491765038541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25164443264744327843359027 37746664897116491765038541)
                ·
                  refine ⟨14154999336418684411889453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37746664897116491765038541 14154999336418684411889453)
                  ·
                    refine ⟨5308124751157006654458545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14154999336418684411889453 5308124751157006654458545)
                    ·
                      refine ⟨3981093563367754990843909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5308124751157006654458545 3981093563367754990843909)
                      ·
                        rfl

theorem cell23_7753152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 3, 3, 2].length) (baseStart_7753152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753152 prefixEnd_7753152 := by exact prefixLift 7753152
  have htrace : WordTrace (prefixWord ++ tailWord_7753152) baseStart_7753152 baseEnd_7753152 := by
    simpa [prefixWord, tailWord_7753152, baseEnd_7753152] using wordTrace_append hprefix tailTrace_7753152
  have hstable : (prefixWord ++ tailWord_7753152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753152).length < 2 ^ (prefixWord ++ tailWord_7753152).sum := by decide
  have hdescent : baseEnd_7753152 < baseStart_7753152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
