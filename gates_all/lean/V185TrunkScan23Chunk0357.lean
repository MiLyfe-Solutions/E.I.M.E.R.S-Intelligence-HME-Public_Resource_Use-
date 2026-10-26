import V185TrunkScan23Chunk0356

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2111472 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 4, 3, 2]
def baseStart_2111472 : Nat := 118140960795 + 2111472 * 2 ^ 59
def prefixEnd_2111472 : Nat := 4983230072969 + 3 ^ 40 * 2111472 * 2
def baseEnd_2111472 : Nat := 1084200024510268089789523

theorem tailTrace_2111472 : CollatzResearch.WordTrace tailWord_2111472 prefixEnd_2111472 1084200024510268089789523 := by
  unfold tailWord_2111472
  simp only [CollatzResearch.WordTrace]
  refine ⟨38505855303252514776512335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51341140404336686368683113 38505855303252514776512335)
  ·
    refine ⟨57758782954878772164768503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38505855303252514776512335 57758782954878772164768503)
    ·
      refine ⟨86638174432318158247152755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57758782954878772164768503 86638174432318158247152755)
      ·
        refine ⟨129957261648477237370729133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86638174432318158247152755 129957261648477237370729133)
        ·
          refine ⟨48733973118178964014023425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129957261648477237370729133 48733973118178964014023425)
          ·
            refine ⟨36550479838634223010517569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48733973118178964014023425 36550479838634223010517569)
            ·
              refine ⟨27412859878975667257888177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36550479838634223010517569 27412859878975667257888177)
              ·
                refine ⟨20559644909231750443416133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27412859878975667257888177 20559644909231750443416133)
                ·
                  refine ⟨3854933420480953208140525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20559644909231750443416133 3854933420480953208140525)
                  ·
                    refine ⟨1445600032680357453052697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3854933420480953208140525 1445600032680357453052697)
                    ·
                      refine ⟨1084200024510268089789523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1445600032680357453052697 1084200024510268089789523)
                      ·
                        rfl

theorem cell23_2111472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 4, 3, 2].length) (baseStart_2111472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111472 prefixEnd_2111472 := by exact prefixLift 2111472
  have htrace : WordTrace (prefixWord ++ tailWord_2111472) baseStart_2111472 baseEnd_2111472 := by
    simpa [prefixWord, tailWord_2111472, baseEnd_2111472] using wordTrace_append hprefix tailTrace_2111472
  have hstable : (prefixWord ++ tailWord_2111472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111472).length < 2 ^ (prefixWord ++ tailWord_2111472).sum := by decide
  have hdescent : baseEnd_2111472 < baseStart_2111472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111496 : List Nat := [2, 1, 3, 2, 1, 2, 4, 3, 1, 1, 3]
def baseStart_2111496 : Nat := 118140960795 + 2111496 * 2 ^ 59
def prefixEnd_2111496 : Nat := 4983230072969 + 3 ^ 40 * 2111496 * 2
def baseEnd_2111496 : Nat := 1084212348045975995889413

theorem tailTrace_2111496 : CollatzResearch.WordTrace tailWord_2111496 prefixEnd_2111496 1084212348045975995889413 := by
  unfold tailWord_2111496
  simp only [CollatzResearch.WordTrace]
  refine ⟨38506292979209040825949171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51341723972278721101265561 38506292979209040825949171)
  ·
    refine ⟨57759439468813561238923757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38506292979209040825949171 57759439468813561238923757)
    ·
      refine ⟨21659789800805085464596409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57759439468813561238923757 21659789800805085464596409)
      ·
        refine ⟨16244842350603814098447307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21659789800805085464596409 16244842350603814098447307)
        ·
          refine ⟨24367263525905721147670961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16244842350603814098447307 24367263525905721147670961)
          ·
            refine ⟨18275447644429290860753221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24367263525905721147670961 18275447644429290860753221)
            ·
              refine ⟨3426646433330492036391229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18275447644429290860753221 3426646433330492036391229)
              ·
                refine ⟨1284992412498934513646711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3426646433330492036391229 1284992412498934513646711)
                ·
                  refine ⟨1927488618748401770470067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284992412498934513646711 1927488618748401770470067)
                  ·
                    refine ⟨2891232928122602655705101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1927488618748401770470067 2891232928122602655705101)
                    ·
                      refine ⟨1084212348045975995889413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2891232928122602655705101 1084212348045975995889413)
                      ·
                        rfl

theorem cell23_2111496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_2111496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111496 prefixEnd_2111496 := by exact prefixLift 2111496
  have htrace : WordTrace (prefixWord ++ tailWord_2111496) baseStart_2111496 baseEnd_2111496 := by
    simpa [prefixWord, tailWord_2111496, baseEnd_2111496] using wordTrace_append hprefix tailTrace_2111496
  have hstable : (prefixWord ++ tailWord_2111496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111496).length < 2 ^ (prefixWord ++ tailWord_2111496).sum := by decide
  have hdescent : baseEnd_2111496 < baseStart_2111496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111512 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 4, 4]
def baseStart_2111512 : Nat := 118140960795 + 2111512 * 2 ^ 59
def prefixEnd_2111512 : Nat := 4983230072969 + 3 ^ 40 * 2111512 * 2
def baseEnd_2111512 : Nat := 361406854578815977763113

theorem tailTrace_2111512 : CollatzResearch.WordTrace tailWord_2111512 prefixEnd_2111512 361406854578815977763113 := by
  unfold tailWord_2111512
  simp only [CollatzResearch.WordTrace]
  refine ⟨38506584763180058192240395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51342113017573410922987193 38506584763180058192240395)
  ·
    refine ⟨57759877144770087288360593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38506584763180058192240395 57759877144770087288360593)
    ·
      refine ⟨43319907858577565466270445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57759877144770087288360593 43319907858577565466270445)
      ·
        refine ⟨16244965446966587049851417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43319907858577565466270445 16244965446966587049851417)
        ·
          refine ⟨12183724085224940287388563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16244965446966587049851417 12183724085224940287388563)
          ·
            refine ⟨18275586127837410431082845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12183724085224940287388563 18275586127837410431082845)
            ·
              refine ⟨6853344797939028911656067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18275586127837410431082845 6853344797939028911656067)
              ·
                refine ⟨10280017196908543367484101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6853344797939028911656067 10280017196908543367484101)
                ·
                  refine ⟨1927503224420351881403269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10280017196908543367484101 1927503224420351881403269)
                  ·
                    refine ⟨361406854578815977763113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1927503224420351881403269 361406854578815977763113)
                    ·
                      rfl

theorem cell23_2111512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 4, 4].length) (baseStart_2111512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111512 prefixEnd_2111512 := by exact prefixLift 2111512
  have htrace : WordTrace (prefixWord ++ tailWord_2111512) baseStart_2111512 baseEnd_2111512 := by
    simpa [prefixWord, tailWord_2111512, baseEnd_2111512] using wordTrace_append hprefix tailTrace_2111512
  have hstable : (prefixWord ++ tailWord_2111512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111512).length < 2 ^ (prefixWord ++ tailWord_2111512).sum := by decide
  have hdescent : baseEnd_2111512 < baseStart_2111512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111522 : List Nat := [3, 3, 1, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_2111522 : Nat := 118140960795 + 2111522 * 2 ^ 59
def prefixEnd_2111522 : Nat := 4983230072969 + 3 ^ 40 * 2111522 * 2
def baseEnd_2111522 : Nat := 1084225698542992894164293

theorem tailTrace_2111522 : CollatzResearch.WordTrace tailWord_2111522 prefixEnd_2111522 1084225698542992894164293 := by
  unfold tailWord_2111522
  simp only [CollatzResearch.WordTrace]
  refine ⟨19253383564080972023086205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51342356170882592061563213 19253383564080972023086205)
  ·
    refine ⟨7220018836530364508657327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19253383564080972023086205 7220018836530364508657327)
    ·
      refine ⟨10830028254795546762985991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7220018836530364508657327 10830028254795546762985991)
      ·
        refine ⟨16245042382193320144478987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10830028254795546762985991 16245042382193320144478987)
        ·
          refine ⟨24367563573289980216718481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16245042382193320144478987 24367563573289980216718481)
          ·
            refine ⟨18275672679967485162538861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24367563573289980216718481 18275672679967485162538861)
            ·
              refine ⟨6853377254987806935952073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18275672679967485162538861 6853377254987806935952073)
              ·
                refine ⟨5140032941240855201964055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6853377254987806935952073 5140032941240855201964055)
                ·
                  refine ⟨7710049411861282802946083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5140032941240855201964055 7710049411861282802946083)
                  ·
                    refine ⟨11565074117791924204419125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7710049411861282802946083 11565074117791924204419125)
                    ·
                      refine ⟨1084225698542992894164293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11565074117791924204419125 1084225698542992894164293)
                      ·
                        rfl

theorem cell23_2111522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_2111522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111522 prefixEnd_2111522 := by exact prefixLift 2111522
  have htrace : WordTrace (prefixWord ++ tailWord_2111522) baseStart_2111522 baseEnd_2111522 := by
    simpa [prefixWord, tailWord_2111522, baseEnd_2111522] using wordTrace_append hprefix tailTrace_2111522
  have hstable : (prefixWord ++ tailWord_2111522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111522).length < 2 ^ (prefixWord ++ tailWord_2111522).sum := by decide
  have hdescent : baseEnd_2111522 < baseStart_2111522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111542 : List Nat := [5, 1, 2, 1, 1, 1, 3, 9]
def baseStart_2111542 : Nat := 118140960795 + 2111542 * 2 ^ 59
def prefixEnd_2111542 : Nat := 4983230072969 + 3 ^ 40 * 2111542 * 2
def baseEnd_2111542 : Nat := 40156887709484548737563

theorem tailTrace_2111542 : CollatzResearch.WordTrace tailWord_2111542 prefixEnd_2111542 40156887709484548737563 := by
  unfold tailWord_2111542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4813391482265714469254555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51342842477500954338715253 4813391482265714469254555)
  ·
    refine ⟨7220087223398571703881833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4813391482265714469254555 7220087223398571703881833)
    ·
      refine ⟨5415065417548928777911375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7220087223398571703881833 5415065417548928777911375)
      ·
        refine ⟨8122598126323393166867063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5415065417548928777911375 8122598126323393166867063)
        ·
          refine ⟨12183897189485089750300595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8122598126323393166867063 12183897189485089750300595)
          ·
            refine ⟨18275845784227634625450893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12183897189485089750300595 18275845784227634625450893)
            ·
              refine ⟨6853442169085362984544085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18275845784227634625450893 6853442169085362984544085)
              ·
                refine ⟨40156887709484548737563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6853442169085362984544085 40156887709484548737563)
                ·
                  rfl

theorem cell23_2111542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_2111542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111542 prefixEnd_2111542 := by exact prefixLift 2111542
  have htrace : WordTrace (prefixWord ++ tailWord_2111542) baseStart_2111542 baseEnd_2111542 := by
    simpa [prefixWord, tailWord_2111542, baseEnd_2111542] using wordTrace_append hprefix tailTrace_2111542
  have hstable : (prefixWord ++ tailWord_2111542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111542).length < 2 ^ (prefixWord ++ tailWord_2111542).sum := by decide
  have hdescent : baseEnd_2111542 < baseStart_2111542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111569 : List Nat := [1, 2, 2, 1, 3, 1, 1, 6, 2, 1, 3]
def baseStart_2111569 : Nat := 118140960795 + 2111569 * 2 ^ 59
def prefixEnd_2111569 : Nat := 4983230072969 + 3 ^ 40 * 2111569 * 2
def baseEnd_2111569 : Nat := 1084249832133754210276577

theorem tailTrace_2111569 : CollatzResearch.WordTrace tailWord_2111569 prefixEnd_2111569 1084249832133754210276577 := by
  unfold tailWord_2111569
  simp only [CollatzResearch.WordTrace]
  refine ⟨77015248487153615119305761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51343498991435743412870507 77015248487153615119305761)
  ·
    refine ⟨57761436365365211339479321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77015248487153615119305761 57761436365365211339479321)
    ·
      refine ⟨43321077274023908504609491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57761436365365211339479321 43321077274023908504609491)
      ·
        refine ⟨64981615911035862756914237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43321077274023908504609491 64981615911035862756914237)
        ·
          refine ⟨24368105966638448533842839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64981615911035862756914237 24368105966638448533842839)
          ·
            refine ⟨36552158949957672800764259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24368105966638448533842839 36552158949957672800764259)
            ·
              refine ⟨54828238424936509201146389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36552158949957672800764259 54828238424936509201146389)
              ·
                refine ⟨2570073676168898868803737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54828238424936509201146389 2570073676168898868803737)
                ·
                  refine ⟨1927555257126674151602803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2570073676168898868803737 1927555257126674151602803)
                  ·
                    refine ⟨2891332885690011227404205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1927555257126674151602803 2891332885690011227404205)
                    ·
                      refine ⟨1084249832133754210276577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2891332885690011227404205 1084249832133754210276577)
                      ·
                        rfl

theorem cell23_2111569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 1, 3].length) (baseStart_2111569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111569 prefixEnd_2111569 := by exact prefixLift 2111569
  have htrace : WordTrace (prefixWord ++ tailWord_2111569) baseStart_2111569 baseEnd_2111569 := by
    simpa [prefixWord, tailWord_2111569, baseEnd_2111569] using wordTrace_append hprefix tailTrace_2111569
  have hstable : (prefixWord ++ tailWord_2111569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111569).length < 2 ^ (prefixWord ++ tailWord_2111569).sum := by decide
  have hdescent : baseEnd_2111569 < baseStart_2111569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111570 : List Nat := [3, 2, 2, 1, 5, 1, 1, 1, 3, 2, 2]
def baseStart_2111570 : Nat := 118140960795 + 2111570 * 2 ^ 59
def prefixEnd_2111570 : Nat := 4983230072969 + 3 ^ 40 * 2111570 * 2
def baseEnd_2111570 : Nat := 1084250345614408706364073

theorem tailTrace_2111570 : CollatzResearch.WordTrace tailWord_2111570 prefixEnd_2111570 1084250345614408706364073 := by
  unfold tailWord_2111570
  simp only [CollatzResearch.WordTrace]
  refine ⟨19253821240037498072523041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51343523306766661526728109 19253821240037498072523041)
  ·
    refine ⟨14440365930028123554392281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19253821240037498072523041 14440365930028123554392281)
    ·
      refine ⟨10830274447521092665794211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14440365930028123554392281 10830274447521092665794211)
      ·
        refine ⟨16245411671281638998691317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10830274447521092665794211 16245411671281638998691317)
        ·
          refine ⟨1523007344182653656127311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16245411671281638998691317 1523007344182653656127311)
          ·
            refine ⟨2284511016273980484190967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1523007344182653656127311 2284511016273980484190967)
            ·
              refine ⟨3426766524410970726286451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2284511016273980484190967 3426766524410970726286451)
              ·
                refine ⟨5140149786616456089429677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3426766524410970726286451 5140149786616456089429677)
                ·
                  refine ⟨1927556169981171033536129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5140149786616456089429677 1927556169981171033536129)
                  ·
                    refine ⟨1445667127485878275152097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1927556169981171033536129 1445667127485878275152097)
                    ·
                      refine ⟨1084250345614408706364073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1445667127485878275152097 1084250345614408706364073)
                      ·
                        rfl

theorem cell23_2111570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_2111570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111570 prefixEnd_2111570 := by exact prefixLift 2111570
  have htrace : WordTrace (prefixWord ++ tailWord_2111570) baseStart_2111570 baseEnd_2111570 := by
    simpa [prefixWord, tailWord_2111570, baseEnd_2111570] using wordTrace_append hprefix tailTrace_2111570
  have hstable : (prefixWord ++ tailWord_2111570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111570).length < 2 ^ (prefixWord ++ tailWord_2111570).sum := by decide
  have hdescent : baseEnd_2111570 < baseStart_2111570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111585 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 1, 8]
def baseStart_2111585 : Nat := 118140960795 + 2111585 * 2 ^ 59
def prefixEnd_2111585 : Nat := 4983230072969 + 3 ^ 40 * 2111585 * 2
def baseEnd_2111585 : Nat := 361419349274742049225501

theorem tailTrace_2111585 : CollatzResearch.WordTrace tailWord_2111585 prefixEnd_2111585 361419349274742049225501 := by
  unfold tailWord_2111585
  simp only [CollatzResearch.WordTrace]
  refine ⟨77015832055095649851888209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51343888036730433234592139 77015832055095649851888209)
  ·
    refine ⟨57761874041321737388916157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77015832055095649851888209 57761874041321737388916157)
    ·
      refine ⟨21660702765495651520843559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57761874041321737388916157 21660702765495651520843559)
      ·
        refine ⟨32491054148243477281265339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21660702765495651520843559 32491054148243477281265339)
        ·
          refine ⟨48736581222365215921898009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32491054148243477281265339 48736581222365215921898009)
          ·
            refine ⟨36552435916773911941423507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48736581222365215921898009 36552435916773911941423507)
            ·
              refine ⟨54828653875160867912135261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36552435916773911941423507 54828653875160867912135261)
              ·
                refine ⟨20560745203185325467050723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54828653875160867912135261 20560745203185325467050723)
                ·
                  refine ⟨30841117804777988200576085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20560745203185325467050723 30841117804777988200576085)
                  ·
                    refine ⟨361419349274742049225501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30841117804777988200576085 361419349274742049225501)
                    ·
                      rfl

theorem cell23_2111585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_2111585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111585 prefixEnd_2111585 := by exact prefixLift 2111585
  have htrace : WordTrace (prefixWord ++ tailWord_2111585) baseStart_2111585 baseEnd_2111585 := by
    simpa [prefixWord, tailWord_2111585, baseEnd_2111585] using wordTrace_append hprefix tailTrace_2111585
  have hstable : (prefixWord ++ tailWord_2111585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111585).length < 2 ^ (prefixWord ++ tailWord_2111585).sum := by decide
  have hdescent : baseEnd_2111585 < baseStart_2111585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111596 : List Nat := [2, 2, 1, 1, 3, 3, 3, 2, 1, 3, 2]
def baseStart_2111596 : Nat := 118140960795 + 2111596 * 2 ^ 59
def prefixEnd_2111596 : Nat := 4983230072969 + 3 ^ 40 * 2111596 * 2
def baseEnd_2111596 : Nat := 1084263696111425604638953

theorem tailTrace_2111596 : CollatzResearch.WordTrace tailWord_2111596 prefixEnd_2111596 1084263696111425604638953 := by
  unfold tailWord_2111596
  simp only [CollatzResearch.WordTrace]
  refine ⟨38508116629027899365269321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51344155505370532487025761 38508116629027899365269321)
  ·
    refine ⟨28881087471770924523951991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38508116629027899365269321 28881087471770924523951991)
    ·
      refine ⟨43321631207656386785927987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28881087471770924523951991 43321631207656386785927987)
      ·
        refine ⟨64982446811484580178891981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43321631207656386785927987 64982446811484580178891981)
        ·
          refine ⟨24368417554306717567084493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64982446811484580178891981 24368417554306717567084493)
          ·
            refine ⟨9138156582865019087656685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24368417554306717567084493 9138156582865019087656685)
            ·
              refine ⟨3426808718574382157871257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9138156582865019087656685 3426808718574382157871257)
              ·
                refine ⟨2570106538930786618403443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3426808718574382157871257 2570106538930786618403443)
                ·
                  refine ⟨3855159808396179927605165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2570106538930786618403443 3855159808396179927605165)
                  ·
                    refine ⟨1445684928148567472851937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3855159808396179927605165 1445684928148567472851937)
                    ·
                      refine ⟨1084263696111425604638953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1445684928148567472851937 1084263696111425604638953)
                      ·
                        rfl

theorem cell23_2111596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 3, 2].length) (baseStart_2111596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111596 prefixEnd_2111596 := by exact prefixLift 2111596
  have htrace : WordTrace (prefixWord ++ tailWord_2111596) baseStart_2111596 baseEnd_2111596 := by
    simpa [prefixWord, tailWord_2111596, baseEnd_2111596] using wordTrace_append hprefix tailTrace_2111596
  have hstable : (prefixWord ++ tailWord_2111596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111596).length < 2 ^ (prefixWord ++ tailWord_2111596).sum := by decide
  have hdescent : baseEnd_2111596 < baseStart_2111596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111609 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 3, 4, 2]
def baseStart_2111609 : Nat := 118140960795 + 2111609 * 2 ^ 59
def prefixEnd_2111609 : Nat := 4983230072969 + 3 ^ 40 * 2111609 * 2
def baseEnd_2111609 : Nat := 1084270371359934053776393

theorem tailTrace_2111609 : CollatzResearch.WordTrace tailWord_2111609 prefixEnd_2111609 1084270371359934053776393 := by
  unfold tailWord_2111609
  simp only [CollatzResearch.WordTrace]
  refine ⟨77016707407008701950761881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51344471604672467967174587 77016707407008701950761881)
  ·
    refine ⟨57762530555256526463071411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77016707407008701950761881 57762530555256526463071411)
    ·
      refine ⟨86643795832884789694607117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57762530555256526463071411 86643795832884789694607117)
      ·
        refine ⟨32491423437331796135477669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86643795832884789694607117 32491423437331796135477669)
        ·
          refine ⟨6092141894499711775402063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32491423437331796135477669 6092141894499711775402063)
          ·
            refine ⟨9138212841749567663103095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6092141894499711775402063 9138212841749567663103095)
            ·
              refine ⟨13707319262624351494654643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9138212841749567663103095 13707319262624351494654643)
              ·
                refine ⟨20560978893936527241981965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13707319262624351494654643 20560978893936527241981965)
                ·
                  refine ⟨7710367085226197715743237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20560978893936527241981965 7710367085226197715743237)
                  ·
                    refine ⟨1445693828479912071701857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7710367085226197715743237 1445693828479912071701857)
                    ·
                      refine ⟨1084270371359934053776393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1445693828479912071701857 1084270371359934053776393)
                      ·
                        rfl

theorem cell23_2111609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 4, 2].length) (baseStart_2111609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111609 prefixEnd_2111609 := by exact prefixLift 2111609
  have htrace : WordTrace (prefixWord ++ tailWord_2111609) baseStart_2111609 baseEnd_2111609 := by
    simpa [prefixWord, tailWord_2111609, baseEnd_2111609] using wordTrace_append hprefix tailTrace_2111609
  have hstable : (prefixWord ++ tailWord_2111609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111609).length < 2 ^ (prefixWord ++ tailWord_2111609).sum := by decide
  have hdescent : baseEnd_2111609 < baseStart_2111609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111612 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 2, 1, 5]
def baseStart_2111612 : Nat := 118140960795 + 2111612 * 2 ^ 59
def prefixEnd_2111612 : Nat := 4983230072969 + 3 ^ 40 * 2111612 * 2
def baseEnd_2111612 : Nat := 1084271911801897542038879

theorem tailTrace_2111612 : CollatzResearch.WordTrace tailWord_2111612 prefixEnd_2111612 1084271911801897542038879 := by
  unfold tailWord_2111612
  simp only [CollatzResearch.WordTrace]
  refine ⟨38508408412998916731560545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51344544550665222308747393 38508408412998916731560545)
  ·
    refine ⟨28881306309749187548670409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38508408412998916731560545 28881306309749187548670409)
    ·
      refine ⟨21660979732311890661502807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28881306309749187548670409 21660979732311890661502807)
      ·
        refine ⟨32491469598467835992254211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21660979732311890661502807 32491469598467835992254211)
        ·
          refine ⟨48737204397701753988381317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32491469598467835992254211 48737204397701753988381317)
          ·
            refine ⟨9138225824569078872821497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48737204397701753988381317 9138225824569078872821497)
            ·
              refine ⟨6853669368426809154616123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9138225824569078872821497 6853669368426809154616123)
              ·
                refine ⟨10280504052640213731924185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6853669368426809154616123 10280504052640213731924185)
                ·
                  refine ⟨7710378039480160298943139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10280504052640213731924185 7710378039480160298943139)
                  ·
                    refine ⟨11565567059220240448414709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7710378039480160298943139 11565567059220240448414709)
                    ·
                      refine ⟨1084271911801897542038879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11565567059220240448414709 1084271911801897542038879)
                      ·
                        rfl

theorem cell23_2111612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_2111612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111612 prefixEnd_2111612 := by exact prefixLift 2111612
  have htrace : WordTrace (prefixWord ++ tailWord_2111612) baseStart_2111612 baseEnd_2111612 := by
    simpa [prefixWord, tailWord_2111612, baseEnd_2111612] using wordTrace_append hprefix tailTrace_2111612
  have hstable : (prefixWord ++ tailWord_2111612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111612).length < 2 ^ (prefixWord ++ tailWord_2111612).sum := by decide
  have hdescent : baseEnd_2111612 < baseStart_2111612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111613 : List Nat := [1, 4, 1, 1, 3, 3, 3, 1, 1, 3, 2]
def baseStart_2111613 : Nat := 118140960795 + 2111613 * 2 ^ 59
def prefixEnd_2111613 : Nat := 4983230072969 + 3 ^ 40 * 2111613 * 2
def baseEnd_2111613 : Nat := 1084272425282552038126375

theorem tailTrace_2111613 : CollatzResearch.WordTrace tailWord_2111613 prefixEnd_2111613 1084272425282552038126375 := by
  unfold tailWord_2111613
  simp only [CollatzResearch.WordTrace]
  refine ⟨77016853298994210633907493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51344568865996140422604995 77016853298994210633907493)
  ·
    refine ⟨14440659993561414493857655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77016853298994210633907493 14440659993561414493857655)
    ·
      refine ⟨21660989990342121740786483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14440659993561414493857655 21660989990342121740786483)
      ·
        refine ⟨32491484985513182611179725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21660989990342121740786483 32491484985513182611179725)
        ·
          refine ⟨12184306869567443479192397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32491484985513182611179725 12184306869567443479192397)
          ·
            refine ⟨4569115076087791304697149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12184306869567443479192397 4569115076087791304697149)
            ·
              refine ⟨1713418153532921739261431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4569115076087791304697149 1713418153532921739261431)
              ·
                refine ⟨2570127230299382608892147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1713418153532921739261431 2570127230299382608892147)
                ·
                  refine ⟨3855190845449073913338221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2570127230299382608892147 3855190845449073913338221)
                  ·
                    refine ⟨1445696567043402717501833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3855190845449073913338221 1445696567043402717501833)
                    ·
                      refine ⟨1084272425282552038126375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1445696567043402717501833 1084272425282552038126375)
                      ·
                        rfl

theorem cell23_2111613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 1, 3, 2].length) (baseStart_2111613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111613 prefixEnd_2111613 := by exact prefixLift 2111613
  have htrace : WordTrace (prefixWord ++ tailWord_2111613) baseStart_2111613 baseEnd_2111613 := by
    simpa [prefixWord, tailWord_2111613, baseEnd_2111613] using wordTrace_append hprefix tailTrace_2111613
  have hstable : (prefixWord ++ tailWord_2111613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111613).length < 2 ^ (prefixWord ++ tailWord_2111613).sum := by decide
  have hdescent : baseEnd_2111613 < baseStart_2111613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111635 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 8]
def baseStart_2111635 : Nat := 118140960795 + 2111635 * 2 ^ 59
def prefixEnd_2111635 : Nat := 4983230072969 + 3 ^ 40 * 2111635 * 2
def baseEnd_2111635 : Nat := 1084283721856950952051273

theorem tailTrace_2111635 : CollatzResearch.WordTrace tailWord_2111635 prefixEnd_2111635 1084283721856950952051273 := by
  unfold tailWord_2111635
  simp only [CollatzResearch.WordTrace]
  refine ⟨77017655704914508391208359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51345103803276338927472239 77017655704914508391208359)
  ·
    refine ⟨115526483557371762586812539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77017655704914508391208359 115526483557371762586812539)
    ·
      refine ⟨173289725336057643880218809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115526483557371762586812539 173289725336057643880218809)
      ·
        refine ⟨129967294002043232910164107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173289725336057643880218809 129967294002043232910164107)
        ·
          refine ⟨194950941003064849365246161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129967294002043232910164107 194950941003064849365246161)
          ·
            refine ⟨146213205752298637023934621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194950941003064849365246161 146213205752298637023934621)
            ·
              refine ⟨54829952157111988883975483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146213205752298637023934621 54829952157111988883975483)
              ·
                refine ⟨82244928235667983325963225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54829952157111988883975483 82244928235667983325963225)
                ·
                  refine ⟨61683696176750987494472419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82244928235667983325963225 61683696176750987494472419)
                  ·
                    refine ⟨92525544265126481241708629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61683696176750987494472419 92525544265126481241708629)
                    ·
                      refine ⟨1084283721856950952051273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 92525544265126481241708629 1084283721856950952051273)
                      ·
                        rfl

theorem cell23_2111635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_2111635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111635 prefixEnd_2111635 := by exact prefixLift 2111635
  have htrace : WordTrace (prefixWord ++ tailWord_2111635) baseStart_2111635 baseEnd_2111635 := by
    simpa [prefixWord, tailWord_2111635, baseEnd_2111635] using wordTrace_append hprefix tailTrace_2111635
  have hstable : (prefixWord ++ tailWord_2111635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111635).length < 2 ^ (prefixWord ++ tailWord_2111635).sum := by decide
  have hdescent : baseEnd_2111635 < baseStart_2111635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111636 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 2, 6]
def baseStart_2111636 : Nat := 118140960795 + 2111636 * 2 ^ 59
def prefixEnd_2111636 : Nat := 4983230072969 + 3 ^ 40 * 2111636 * 2
def baseEnd_2111636 : Nat := 361428078445868482712923

theorem tailTrace_2111636 : CollatzResearch.WordTrace tailWord_2111636 prefixEnd_2111636 361428078445868482712923 := by
  unfold tailWord_2111636
  simp only [CollatzResearch.WordTrace]
  refine ⟨38508846088955442780997381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51345128118607257041329841 38508846088955442780997381)
  ·
    refine ⟨7220408641679145521437009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38508846088955442780997381 7220408641679145521437009)
    ·
      refine ⟨5415306481259359141077757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7220408641679145521437009 5415306481259359141077757)
      ·
        refine ⟨2030739930472259677904159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5415306481259359141077757 2030739930472259677904159)
        ·
          refine ⟨3046109895708389516856239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2030739930472259677904159 3046109895708389516856239)
          ·
            refine ⟨4569164843562584275284359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3046109895708389516856239 4569164843562584275284359)
            ·
              refine ⟨6853747265343876412926539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4569164843562584275284359 6853747265343876412926539)
              ·
                refine ⟨10280620898015814619389809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6853747265343876412926539 10280620898015814619389809)
                ·
                  refine ⟨7710465673511860964542357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10280620898015814619389809 7710465673511860964542357)
                  ·
                    refine ⟨361428078445868482712923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7710465673511860964542357 361428078445868482712923)
                    ·
                      rfl

theorem cell23_2111636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_2111636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111636 prefixEnd_2111636 := by exact prefixLift 2111636
  have htrace : WordTrace (prefixWord ++ tailWord_2111636) baseStart_2111636 baseEnd_2111636 := by
    simpa [prefixWord, tailWord_2111636, baseEnd_2111636] using wordTrace_append hprefix tailTrace_2111636
  have hstable : (prefixWord ++ tailWord_2111636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111636).length < 2 ^ (prefixWord ++ tailWord_2111636).sum := by decide
  have hdescent : baseEnd_2111636 < baseStart_2111636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111639 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 4]
def baseStart_2111639 : Nat := 118140960795 + 2111639 * 2 ^ 59
def prefixEnd_2111639 : Nat := 4983230072969 + 3 ^ 40 * 2111639 * 2
def baseEnd_2111639 : Nat := 1084285775779568936401255

theorem tailTrace_2111639 : CollatzResearch.WordTrace tailWord_2111639 prefixEnd_2111639 1084285775779568936401255 := by
  unfold tailWord_2111639
  simp only [CollatzResearch.WordTrace]
  refine ⟨77017801596900017074353971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51345201064600011382902647 77017801596900017074353971)
  ·
    refine ⟨115526702395350025611530957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77017801596900017074353971 115526702395350025611530957)
    ·
      refine ⟨43322513398256259604324109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115526702395350025611530957 43322513398256259604324109)
      ·
        refine ⟨16245942524346097351621541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43322513398256259604324109 16245942524346097351621541)
        ·
          refine ⟨3046114223314893253429039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16245942524346097351621541 3046114223314893253429039)
          ·
            refine ⟨4569171334972339880143559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3046114223314893253429039 4569171334972339880143559)
            ·
              refine ⟨6853757002458509820215339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4569171334972339880143559 6853757002458509820215339)
              ·
                refine ⟨10280635503687764730323009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6853757002458509820215339 10280635503687764730323009)
                ·
                  refine ⟨7710476627765823547742257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10280635503687764730323009 7710476627765823547742257)
                  ·
                    refine ⟨5782857470824367660806693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7710476627765823547742257 5782857470824367660806693)
                    ·
                      refine ⟨1084285775779568936401255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5782857470824367660806693 1084285775779568936401255)
                      ·
                        rfl

theorem cell23_2111639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_2111639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111639 prefixEnd_2111639 := by exact prefixLift 2111639
  have htrace : WordTrace (prefixWord ++ tailWord_2111639) baseStart_2111639 baseEnd_2111639 := by
    simpa [prefixWord, tailWord_2111639, baseEnd_2111639] using wordTrace_append hprefix tailTrace_2111639
  have hstable : (prefixWord ++ tailWord_2111639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111639).length < 2 ^ (prefixWord ++ tailWord_2111639).sum := by decide
  have hdescent : baseEnd_2111639 < baseStart_2111639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111712 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 4]
def baseStart_2111712 : Nat := 118140960795 + 2111712 * 2 ^ 59
def prefixEnd_2111712 : Nat := 4983230072969 + 3 ^ 40 * 2111712 * 2
def baseEnd_2111712 : Nat := 1084323259867347150788419

theorem tailTrace_2111712 : CollatzResearch.WordTrace tailWord_2111712 prefixEnd_2111712 1084323259867347150788419 := by
  unfold tailWord_2111712
  simp only [CollatzResearch.WordTrace]
  refine ⟨38510232062817775270880695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51346976083757033694507593 38510232062817775270880695)
  ·
    refine ⟨57765348094226662906321043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38510232062817775270880695 57765348094226662906321043)
    ·
      refine ⟨86648022141339994359481565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57765348094226662906321043 86648022141339994359481565)
      ·
        refine ⟨32493008303002497884805587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86648022141339994359481565 32493008303002497884805587)
        ·
          refine ⟨48739512454503746827208381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32493008303002497884805587 48739512454503746827208381)
          ·
            refine ⟨18277317170438905060203143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48739512454503746827208381 18277317170438905060203143)
            ·
              refine ⟨27415975755658357590304715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18277317170438905060203143 27415975755658357590304715)
              ·
                refine ⟨41123963633487536385457073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27415975755658357590304715 41123963633487536385457073)
                ·
                  refine ⟨30842972725115652289092805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41123963633487536385457073 30842972725115652289092805)
                  ·
                    refine ⟨5783057385959184804204901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30842972725115652289092805 5783057385959184804204901)
                    ·
                      refine ⟨1084323259867347150788419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5783057385959184804204901 1084323259867347150788419)
                      ·
                        rfl

theorem cell23_2111712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_2111712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111712 prefixEnd_2111712 := by exact prefixLift 2111712
  have htrace : WordTrace (prefixWord ++ tailWord_2111712) baseStart_2111712 baseEnd_2111712 := by
    simpa [prefixWord, tailWord_2111712, baseEnd_2111712] using wordTrace_append hprefix tailTrace_2111712
  have hstable : (prefixWord ++ tailWord_2111712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111712).length < 2 ^ (prefixWord ++ tailWord_2111712).sum := by decide
  have hdescent : baseEnd_2111712 < baseStart_2111712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111722 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 10]
def baseStart_2111722 : Nat := 118140960795 + 2111722 * 2 ^ 59
def prefixEnd_2111722 : Nat := 4983230072969 + 3 ^ 40 * 2111722 * 2
def baseEnd_2111722 : Nat := 120480932741543567962597

theorem tailTrace_2111722 : CollatzResearch.WordTrace tailWord_2111722 prefixEnd_2111722 120480932741543567962597 := by
  unfold tailWord_2111722
  simp only [CollatzResearch.WordTrace]
  refine ⟨19255207213899830562406355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51347219237066214833083613 19255207213899830562406355)
  ·
    refine ⟨28882810820849745843609533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19255207213899830562406355 28882810820849745843609533)
    ·
      refine ⟨10831054057818654691353575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28882810820849745843609533 10831054057818654691353575)
      ·
        refine ⟨16246581086727982037030363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10831054057818654691353575 16246581086727982037030363)
        ·
          refine ⟨24369871630091973055545545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16246581086727982037030363 24369871630091973055545545)
          ·
            refine ⟨18277403722568979791659159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24369871630091973055545545 18277403722568979791659159)
            ·
              refine ⟨27416105583853469687488739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18277403722568979791659159 27416105583853469687488739)
              ·
                refine ⟨41124158375780204531233109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27416105583853469687488739 41124158375780204531233109)
                ·
                  refine ⟨120480932741543567962597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 41124158375780204531233109 120480932741543567962597)
                  ·
                    rfl

theorem cell23_2111722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 10].length) (baseStart_2111722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111722 prefixEnd_2111722 := by exact prefixLift 2111722
  have htrace : WordTrace (prefixWord ++ tailWord_2111722) baseStart_2111722 baseEnd_2111722 := by
    simpa [prefixWord, tailWord_2111722, baseEnd_2111722] using wordTrace_append hprefix tailTrace_2111722
  have hstable : (prefixWord ++ tailWord_2111722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111722).length < 2 ^ (prefixWord ++ tailWord_2111722).sum := by decide
  have hdescent : baseEnd_2111722 < baseStart_2111722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111743 : List Nat := [1, 1, 2, 2, 1, 4, 5, 2, 1, 4]
def baseStart_2111743 : Nat := 118140960795 + 2111743 * 2 ^ 59
def prefixEnd_2111743 : Nat := 4983230072969 + 3 ^ 40 * 2111743 * 2
def baseEnd_2111743 : Nat := 361446392589212176500259

theorem tailTrace_2111743 : CollatzResearch.WordTrace tailWord_2111743 prefixEnd_2111743 361446392589212176500259 := by
  unfold tailWord_2111743
  simp only [CollatzResearch.WordTrace]
  refine ⟨77021594788523242836139883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51347729859015495224093255 77021594788523242836139883)
  ·
    refine ⟨115532392182784864254209825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77021594788523242836139883 115532392182784864254209825)
    ·
      refine ⟨86649294137088648190657369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115532392182784864254209825 86649294137088648190657369)
      ·
        refine ⟨64986970602816486142993027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86649294137088648190657369 64986970602816486142993027)
        ·
          refine ⟨97480455904224729214489541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64986970602816486142993027 97480455904224729214489541)
          ·
            refine ⟨18277585482042136727716789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97480455904224729214489541 18277585482042136727716789)
            ·
              refine ⟨1713523638941450318223449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18277585482042136727716789 1713523638941450318223449)
              ·
                refine ⟨1285142729206087738667587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1713523638941450318223449 1285142729206087738667587)
                ·
                  refine ⟨1927714093809131608001381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1285142729206087738667587 1927714093809131608001381)
                  ·
                    refine ⟨361446392589212176500259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1927714093809131608001381 361446392589212176500259)
                    ·
                      rfl

theorem cell23_2111743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 1, 4].length) (baseStart_2111743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111743 prefixEnd_2111743 := by exact prefixLift 2111743
  have htrace : WordTrace (prefixWord ++ tailWord_2111743) baseStart_2111743 baseEnd_2111743 := by
    simpa [prefixWord, tailWord_2111743, baseEnd_2111743] using wordTrace_append hprefix tailTrace_2111743
  have hstable : (prefixWord ++ tailWord_2111743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111743).length < 2 ^ (prefixWord ++ tailWord_2111743).sum := by decide
  have hdescent : baseEnd_2111743 < baseStart_2111743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111759 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 3, 5, 2]
def baseStart_2111759 : Nat := 118140960795 + 2111759 * 2 ^ 59
def prefixEnd_2111759 : Nat := 4983230072969 + 3 ^ 40 * 2111759 * 2
def baseEnd_2111759 : Nat := 1084347393458108466900703

theorem tailTrace_2111759 : CollatzResearch.WordTrace tailWord_2111759 prefixEnd_2111759 1084347393458108466900703 := by
  unfold tailWord_2111759
  simp only [CollatzResearch.WordTrace]
  refine ⟨77022178356465277568722331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51348118904310185045814887 77022178356465277568722331)
  ·
    refine ⟨115533267534697916353083497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77022178356465277568722331 115533267534697916353083497)
    ·
      refine ⟨86649950651023437264812623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115533267534697916353083497 86649950651023437264812623)
      ·
        refine ⟨129974925976535155897218935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86649950651023437264812623 129974925976535155897218935)
        ·
          refine ⟨194962388964802733845828403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129974925976535155897218935 194962388964802733845828403)
          ·
            refine ⟨292443583447204100768742605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194962388964802733845828403 292443583447204100768742605)
            ·
              refine ⟨109666343792701537788278477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 292443583447204100768742605 109666343792701537788278477)
              ·
                refine ⟨41124878922263076670604429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109666343792701537788278477 41124878922263076670604429)
                ·
                  refine ⟨15421829595848653751476661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41124878922263076670604429 15421829595848653751476661)
                  ·
                    refine ⟨1445796524610811289200937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15421829595848653751476661 1445796524610811289200937)
                    ·
                      refine ⟨1084347393458108466900703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1445796524610811289200937 1084347393458108466900703)
                      ·
                        rfl

theorem cell23_2111759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 5, 2].length) (baseStart_2111759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111759 prefixEnd_2111759 := by exact prefixLift 2111759
  have htrace : WordTrace (prefixWord ++ tailWord_2111759) baseStart_2111759 baseEnd_2111759 := by
    simpa [prefixWord, tailWord_2111759, baseEnd_2111759] using wordTrace_append hprefix tailTrace_2111759
  have hstable : (prefixWord ++ tailWord_2111759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111759).length < 2 ^ (prefixWord ++ tailWord_2111759).sum := by decide
  have hdescent : baseEnd_2111759 < baseStart_2111759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111799 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 4, 4]
def baseStart_2111799 : Nat := 118140960795 + 2111799 * 2 ^ 59
def prefixEnd_2111799 : Nat := 4983230072969 + 3 ^ 40 * 2111799 * 2
def baseEnd_2111799 : Nat := 361455977561429436800173

theorem tailTrace_2111799 : CollatzResearch.WordTrace tailWord_2111799 prefixEnd_2111799 361455977561429436800173 := by
  unfold tailWord_2111799
  simp only [CollatzResearch.WordTrace]
  refine ⟨77023637276320364400178451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51349091517546909600118967 77023637276320364400178451)
  ·
    refine ⟨115535455914480546600267677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77023637276320364400178451 115535455914480546600267677)
    ·
      refine ⟨43325795967930204975100379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115535455914480546600267677 43325795967930204975100379)
      ·
        refine ⟨64988693951895307462650569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43325795967930204975100379 64988693951895307462650569)
        ·
          refine ⟨48741520463921480596987927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64988693951895307462650569 48741520463921480596987927)
          ·
            refine ⟨73112280695882220895481891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48741520463921480596987927 73112280695882220895481891)
            ·
              refine ⟨109668421043823331343222837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73112280695882220895481891 109668421043823331343222837)
              ·
                refine ⟨10281414472858437313427141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109668421043823331343222837 10281414472858437313427141)
                ·
                  refine ⟨1927765213660956996267589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10281414472858437313427141 1927765213660956996267589)
                  ·
                    refine ⟨361455977561429436800173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1927765213660956996267589 361455977561429436800173)
                    ·
                      rfl

theorem cell23_2111799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 4].length) (baseStart_2111799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111799 prefixEnd_2111799 := by exact prefixLift 2111799
  have htrace : WordTrace (prefixWord ++ tailWord_2111799) baseStart_2111799 baseEnd_2111799 := by
    simpa [prefixWord, tailWord_2111799, baseEnd_2111799] using wordTrace_append hprefix tailTrace_2111799
  have hstable : (prefixWord ++ tailWord_2111799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111799).length < 2 ^ (prefixWord ++ tailWord_2111799).sum := by decide
  have hdescent : baseEnd_2111799 < baseStart_2111799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111800 : List Nat := [2, 1, 2, 1, 3, 1, 6, 2, 1, 1, 3]
def baseStart_2111800 : Nat := 118140960795 + 2111800 * 2 ^ 59
def prefixEnd_2111800 : Nat := 4983230072969 + 3 ^ 40 * 2111800 * 2
def baseEnd_2111800 : Nat := 1084368446164942806488015

theorem tailTrace_2111800 : CollatzResearch.WordTrace tailWord_2111800 prefixEnd_2111800 1084368446164942806488015 := by
  unfold tailWord_2111800
  simp only [CollatzResearch.WordTrace]
  refine ⟨38511836874658370785482427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51349115832877827713976569 38511836874658370785482427)
  ·
    refine ⟨57767755311987556178223641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38511836874658370785482427 57767755311987556178223641)
    ·
      refine ⟨43325816483990667133667731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57767755311987556178223641 43325816483990667133667731)
      ·
        refine ⟨64988724725986000700501597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43325816483990667133667731 64988724725986000700501597)
        ·
          refine ⟨24370771772244750262688099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64988724725986000700501597 24370771772244750262688099)
          ·
            refine ⟨36556157658367125394032149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24370771772244750262688099 36556157658367125394032149)
            ·
              refine ⟨1713569890235959002845257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36556157658367125394032149 1713569890235959002845257)
              ·
                refine ⟨1285177417676969252133943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1713569890235959002845257 1285177417676969252133943)
                ·
                  refine ⟨1927766126515453878200915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1285177417676969252133943 1927766126515453878200915)
                  ·
                    refine ⟨2891649189773180817301373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1927766126515453878200915 2891649189773180817301373)
                    ·
                      refine ⟨1084368446164942806488015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2891649189773180817301373 1084368446164942806488015)
                      ·
                        rfl

theorem cell23_2111800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 1, 1, 3].length) (baseStart_2111800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111800 prefixEnd_2111800 := by exact prefixLift 2111800
  have htrace : WordTrace (prefixWord ++ tailWord_2111800) baseStart_2111800 baseEnd_2111800 := by
    simpa [prefixWord, tailWord_2111800, baseEnd_2111800] using wordTrace_append hprefix tailTrace_2111800
  have hstable : (prefixWord ++ tailWord_2111800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111800).length < 2 ^ (prefixWord ++ tailWord_2111800).sum := by decide
  have hdescent : baseEnd_2111800 < baseStart_2111800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111806 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_2111806 : Nat := 118140960795 + 2111806 * 2 ^ 59
def prefixEnd_2111806 : Nat := 4983230072969 + 3 ^ 40 * 2111806 * 2
def baseEnd_2111806 : Nat := 1084371527048869783012987

theorem tailTrace_2111806 : CollatzResearch.WordTrace tailWord_2111806 prefixEnd_2111806 1084371527048869783012987 := by
  unfold tailWord_2111806
  simp only [CollatzResearch.WordTrace]
  refine ⟨9627986573411875574460409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51349261724863336397122181 9627986573411875574460409)
  ·
    refine ⟨7220989930058906680845307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9627986573411875574460409 7220989930058906680845307)
    ·
      refine ⟨10831484895088360021267961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7220989930058906680845307 10831484895088360021267961)
      ·
        refine ⟨8123613671316270015950971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10831484895088360021267961 8123613671316270015950971)
        ·
          refine ⟨12185420506974405023926457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8123613671316270015950971 12185420506974405023926457)
          ·
            refine ⟨9139065380230803767944843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12185420506974405023926457 9139065380230803767944843)
            ·
              refine ⟨13708598070346205651917265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9139065380230803767944843 13708598070346205651917265)
              ·
                refine ⟨10281448552759654238937949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13708598070346205651917265 10281448552759654238937949)
                ·
                  refine ⟨3855543207284870339601731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10281448552759654238937949 3855543207284870339601731)
                  ·
                    refine ⟨5783314810927305509402597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3855543207284870339601731 5783314810927305509402597)
                    ·
                      refine ⟨1084371527048869783012987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5783314810927305509402597 1084371527048869783012987)
                      ·
                        rfl

theorem cell23_2111806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_2111806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111806 prefixEnd_2111806 := by exact prefixLift 2111806
  have htrace : WordTrace (prefixWord ++ tailWord_2111806) baseStart_2111806 baseEnd_2111806 := by
    simpa [prefixWord, tailWord_2111806, baseEnd_2111806] using wordTrace_append hprefix tailTrace_2111806
  have hstable : (prefixWord ++ tailWord_2111806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111806).length < 2 ^ (prefixWord ++ tailWord_2111806).sum := by decide
  have hdescent : baseEnd_2111806 < baseStart_2111806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111816 : List Nat := [2, 1, 3, 1, 1, 2, 4, 3, 2, 4]
def baseStart_2111816 : Nat := 118140960795 + 2111816 * 2 ^ 59
def prefixEnd_2111816 : Nat := 4983230072969 + 3 ^ 40 * 2111816 * 2
def baseEnd_2111816 : Nat := 361458887285138247962647

theorem tailTrace_2111816 : CollatzResearch.WordTrace tailWord_2111816 prefixEnd_2111816 361458887285138247962647 := by
  unfold tailWord_2111816
  simp only [CollatzResearch.WordTrace]
  refine ⟨38512128658629388151773651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51349504878172517535698201 38512128658629388151773651)
  ·
    refine ⟨57768192987944082227660477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38512128658629388151773651 57768192987944082227660477)
    ·
      refine ⟨21663072370479030835372679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57768192987944082227660477 21663072370479030835372679)
      ·
        refine ⟨32494608555718546253059019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21663072370479030835372679 32494608555718546253059019)
        ·
          refine ⟨48741912833577819379588529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32494608555718546253059019 48741912833577819379588529)
          ·
            refine ⟨36556434625183364534691397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48741912833577819379588529 36556434625183364534691397)
            ·
              refine ⟨6854331492221880850254637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36556434625183364534691397 6854331492221880850254637)
              ·
                refine ⟨2570374309583205318845489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6854331492221880850254637 2570374309583205318845489)
                ·
                  refine ⟨1927780732187403989134117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2570374309583205318845489 1927780732187403989134117)
                  ·
                    refine ⟨361458887285138247962647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1927780732187403989134117 361458887285138247962647)
                    ·
                      rfl

theorem cell23_2111816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_2111816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111816 prefixEnd_2111816 := by exact prefixLift 2111816
  have htrace : WordTrace (prefixWord ++ tailWord_2111816) baseStart_2111816 baseEnd_2111816 := by
    simpa [prefixWord, tailWord_2111816, baseEnd_2111816] using wordTrace_append hprefix tailTrace_2111816
  have hstable : (prefixWord ++ tailWord_2111816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111816).length < 2 ^ (prefixWord ++ tailWord_2111816).sum := by decide
  have hdescent : baseEnd_2111816 < baseStart_2111816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111826 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3]
def baseStart_2111826 : Nat := 118140960795 + 2111826 * 2 ^ 59
def prefixEnd_2111826 : Nat := 4983230072969 + 3 ^ 40 * 2111826 * 2
def baseEnd_2111826 : Nat := 1084381796661959704762895

theorem tailTrace_2111826 : CollatzResearch.WordTrace tailWord_2111826 prefixEnd_2111826 1084381796661959704762895 := by
  unfold tailWord_2111826
  simp only [CollatzResearch.WordTrace]
  refine ⟨19256155511805637002852833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51349748031481698674274221 19256155511805637002852833)
  ·
    refine ⟨14442116633854227752139625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19256155511805637002852833 14442116633854227752139625)
    ·
      refine ⟨10831587475390670814104719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14442116633854227752139625 10831587475390670814104719)
      ·
        refine ⟨16247381213086006221157079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10831587475390670814104719 16247381213086006221157079)
        ·
          refine ⟨24371071819629009331735619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16247381213086006221157079 24371071819629009331735619)
          ·
            refine ⟨36556607729443513997603429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24371071819629009331735619 36556607729443513997603429)
            ·
              refine ⟨6854363949270658874550643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36556607729443513997603429 6854363949270658874550643)
              ·
                refine ⟨10281545923905988311825965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6854363949270658874550643 10281545923905988311825965)
                ·
                  refine ⟨3855579721464745616934737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10281545923905988311825965 3855579721464745616934737)
                  ·
                    refine ⟨2891684791098559212701053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3855579721464745616934737 2891684791098559212701053)
                    ·
                      refine ⟨1084381796661959704762895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2891684791098559212701053 1084381796661959704762895)
                      ·
                        rfl

theorem cell23_2111826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_2111826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111826 prefixEnd_2111826 := by exact prefixLift 2111826
  have htrace : WordTrace (prefixWord ++ tailWord_2111826) baseStart_2111826 baseEnd_2111826 := by
    simpa [prefixWord, tailWord_2111826, baseEnd_2111826] using wordTrace_append hprefix tailTrace_2111826
  have hstable : (prefixWord ++ tailWord_2111826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111826).length < 2 ^ (prefixWord ++ tailWord_2111826).sum := by decide
  have hdescent : baseEnd_2111826 < baseStart_2111826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111840 : List Nat := [2, 1, 1, 3, 5, 2, 2, 1, 1, 1, 4]
def baseStart_2111840 : Nat := 118140960795 + 2111840 * 2 ^ 59
def prefixEnd_2111840 : Nat := 4983230072969 + 3 ^ 40 * 2111840 * 2
def baseEnd_2111840 : Nat := 1084388985391122649987831

theorem tailTrace_2111840 : CollatzResearch.WordTrace tailWord_2111840 prefixEnd_2111840 1084388985391122649987831 := by
  unfold tailWord_2111840
  simp only [CollatzResearch.WordTrace]
  refine ⟨38512566334585914201210487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51350088446114552268280649 38512566334585914201210487)
  ·
    refine ⟨57768849501878871301815731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38512566334585914201210487 57768849501878871301815731)
    ·
      refine ⟨86653274252818306952723597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57768849501878871301815731 86653274252818306952723597)
      ·
        refine ⟨32494977844806865107271349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86653274252818306952723597 32494977844806865107271349)
        ·
          refine ⟨3046404172950643603806689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32494977844806865107271349 3046404172950643603806689)
          ·
            refine ⟨2284803129712982702855017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3046404172950643603806689 2284803129712982702855017)
            ·
              refine ⟨1713602347284737027141263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2284803129712982702855017 1713602347284737027141263)
              ·
                refine ⟨2570403520927105540711895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1713602347284737027141263 2570403520927105540711895)
                ·
                  refine ⟨3855605281390658311067843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2570403520927105540711895 3855605281390658311067843)
                  ·
                    refine ⟨5783407922085987466601765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3855605281390658311067843 5783407922085987466601765)
                    ·
                      refine ⟨1084388985391122649987831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5783407922085987466601765 1084388985391122649987831)
                      ·
                        rfl

theorem cell23_2111840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 1, 1, 4].length) (baseStart_2111840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111840 prefixEnd_2111840 := by exact prefixLift 2111840
  have htrace : WordTrace (prefixWord ++ tailWord_2111840) baseStart_2111840 baseEnd_2111840 := by
    simpa [prefixWord, tailWord_2111840, baseEnd_2111840] using wordTrace_append hprefix tailTrace_2111840
  have hstable : (prefixWord ++ tailWord_2111840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111840).length < 2 ^ (prefixWord ++ tailWord_2111840).sum := by decide
  have hdescent : baseEnd_2111840 < baseStart_2111840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111850 : List Nat := [3, 1, 3, 3, 1, 3, 1, 2, 2, 4]
def baseStart_2111850 : Nat := 118140960795 + 2111850 * 2 ^ 59
def prefixEnd_2111850 : Nat := 4983230072969 + 3 ^ 40 * 2111850 * 2
def baseEnd_2111850 : Nat := 361464706732555870287595

theorem tailTrace_2111850 : CollatzResearch.WordTrace tailWord_2111850 prefixEnd_2111850 361464706732555870287595 := by
  unfold tailWord_2111850
  simp only [CollatzResearch.WordTrace]
  refine ⟨19256374349783900027571251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51350331599423733406856669 19256374349783900027571251)
  ·
    refine ⟨28884561524675850041356877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19256374349783900027571251 28884561524675850041356877)
    ·
      refine ⟨10831710571753443765508829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28884561524675850041356877 10831710571753443765508829)
      ·
        refine ⟨4061891464407541412065811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10831710571753443765508829 4061891464407541412065811)
        ·
          refine ⟨6092837196611312118098717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4061891464407541412065811 6092837196611312118098717)
          ·
            refine ⟨2284813948729242044287019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6092837196611312118098717 2284813948729242044287019)
            ·
              refine ⟨3427220923093863066430529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2284813948729242044287019 3427220923093863066430529)
              ·
                refine ⟨2570415692320397299822897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3427220923093863066430529 2570415692320397299822897)
                ·
                  refine ⟨1927811769240297974867173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2570415692320397299822897 1927811769240297974867173)
                  ·
                    refine ⟨361464706732555870287595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1927811769240297974867173 361464706732555870287595)
                    ·
                      rfl

theorem cell23_2111850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_2111850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111850 prefixEnd_2111850 := by exact prefixLift 2111850
  have htrace : WordTrace (prefixWord ++ tailWord_2111850) baseStart_2111850 baseEnd_2111850 := by
    simpa [prefixWord, tailWord_2111850, baseEnd_2111850] using wordTrace_append hprefix tailTrace_2111850
  have hstable : (prefixWord ++ tailWord_2111850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111850).length < 2 ^ (prefixWord ++ tailWord_2111850).sum := by decide
  have hdescent : baseEnd_2111850 < baseStart_2111850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111873 : List Nat := [1, 2, 4, 3, 1, 1, 3, 1, 1, 3, 3]
def baseStart_2111873 : Nat := 118140960795 + 2111873 * 2 ^ 59
def prefixEnd_2111873 : Nat := 4983230072969 + 3 ^ 40 * 2111873 * 2
def baseEnd_2111873 : Nat := 1084405930252721020875179

theorem tailTrace_2111873 : CollatzResearch.WordTrace tailWord_2111873 prefixEnd_2111873 1084405930252721020875179 := by
  unfold tailWord_2111873
  simp only [CollatzResearch.WordTrace]
  refine ⟨77026336278052275038372273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51350890852034850025581515 77026336278052275038372273)
  ·
    refine ⟨57769752208539206278779205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77026336278052275038372273 57769752208539206278779205)
    ·
      refine ⟨10831828539101101177271101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57769752208539206278779205 10831828539101101177271101)
      ·
        refine ⟨4061935702162912941476663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10831828539101101177271101 4061935702162912941476663)
        ·
          refine ⟨6092903553244369412214995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4061935702162912941476663 6092903553244369412214995)
          ·
            refine ⟨9139355329866554118322493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6092903553244369412214995 9139355329866554118322493)
            ·
              refine ⟨3427258248699957794370935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9139355329866554118322493 3427258248699957794370935)
              ·
                refine ⟨5140887373049936691556403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3427258248699957794370935 5140887373049936691556403)
                ·
                  refine ⟨7711331059574905037334605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5140887373049936691556403 7711331059574905037334605)
                  ·
                    refine ⟨2891749147340589389000477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7711331059574905037334605 2891749147340589389000477)
                    ·
                      refine ⟨1084405930252721020875179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2891749147340589389000477 1084405930252721020875179)
                      ·
                        rfl

theorem cell23_2111873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_2111873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111873 prefixEnd_2111873 := by exact prefixLift 2111873
  have htrace : WordTrace (prefixWord ++ tailWord_2111873) baseStart_2111873 baseEnd_2111873 := by
    simpa [prefixWord, tailWord_2111873, baseEnd_2111873] using wordTrace_append hprefix tailTrace_2111873
  have hstable : (prefixWord ++ tailWord_2111873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111873).length < 2 ^ (prefixWord ++ tailWord_2111873).sum := by decide
  have hdescent : baseEnd_2111873 < baseStart_2111873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111883 : List Nat := [1, 1, 1, 1, 4, 4, 1, 4, 1, 3, 2]
def baseStart_2111883 : Nat := 118140960795 + 2111883 * 2 ^ 59
def prefixEnd_2111883 : Nat := 4983230072969 + 3 ^ 40 * 2111883 * 2
def baseEnd_2111883 : Nat := 1084411065059265981750133

theorem tailTrace_2111883 : CollatzResearch.WordTrace tailWord_2111883 prefixEnd_2111883 1084411065059265981750133 := by
  unfold tailWord_2111883
  simp only [CollatzResearch.WordTrace]
  refine ⟨77026701008016046746236303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51351134005344031164157535 77026701008016046746236303)
  ·
    refine ⟨115540051512024070119354455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77026701008016046746236303 115540051512024070119354455)
    ·
      refine ⟨173310077268036105179031683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115540051512024070119354455 173310077268036105179031683)
      ·
        refine ⟨259965115902054157768547525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173310077268036105179031683 259965115902054157768547525)
        ·
          refine ⟨48743459231635154581602661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 259965115902054157768547525 48743459231635154581602661)
          ·
            refine ⟨9139398605931591484050499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48743459231635154581602661 9139398605931591484050499)
            ·
              refine ⟨13709097908897387226075749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9139398605931591484050499 13709097908897387226075749)
              ·
                refine ⟨2570455857918260104889203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13709097908897387226075749 2570455857918260104889203)
                ·
                  refine ⟨3855683786877390157333805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2570455857918260104889203 3855683786877390157333805)
                  ·
                    refine ⟨1445881420079021309000177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3855683786877390157333805 1445881420079021309000177)
                    ·
                      refine ⟨1084411065059265981750133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1445881420079021309000177 1084411065059265981750133)
                      ·
                        rfl

theorem cell23_2111883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 3, 2].length) (baseStart_2111883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111883 prefixEnd_2111883 := by exact prefixLift 2111883
  have htrace : WordTrace (prefixWord ++ tailWord_2111883) baseStart_2111883 baseEnd_2111883 := by
    simpa [prefixWord, tailWord_2111883, baseEnd_2111883] using wordTrace_append hprefix tailTrace_2111883
  have hstable : (prefixWord ++ tailWord_2111883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111883).length < 2 ^ (prefixWord ++ tailWord_2111883).sum := by decide
  have hdescent : baseEnd_2111883 < baseStart_2111883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111886 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5]
def baseStart_2111886 : Nat := 118140960795 + 2111886 * 2 ^ 59
def prefixEnd_2111886 : Nat := 4983230072969 + 3 ^ 40 * 2111886 * 2
def baseEnd_2111886 : Nat := 1084412605501229470012619

theorem tailTrace_2111886 : CollatzResearch.WordTrace tailWord_2111886 prefixEnd_2111886 1084412605501229470012619 := by
  unfold tailWord_2111886
  simp only [CollatzResearch.WordTrace]
  refine ⟨9628351303375647282324439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51351206951336785505730341 9628351303375647282324439)
  ·
    refine ⟨14442526955063470923486659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9628351303375647282324439 14442526955063470923486659)
    ·
      refine ⟨21663790432595206385229989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14442526955063470923486659 21663790432595206385229989)
      ·
        refine ⟨4061960706111601197230623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21663790432595206385229989 4061960706111601197230623)
        ·
          refine ⟨6092941059167401795845935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4061960706111601197230623 6092941059167401795845935)
          ·
            refine ⟨9139411588751102693768903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6092941059167401795845935 9139411588751102693768903)
            ·
              refine ⟨13709117383126654040653355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9139411588751102693768903 13709117383126654040653355)
              ·
                refine ⟨20563676074689981060980033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13709117383126654040653355 20563676074689981060980033)
                ·
                  refine ⟨15422757056017485795735025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20563676074689981060980033 15422757056017485795735025)
                  ·
                    refine ⟨11567067792013114346801269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15422757056017485795735025 11567067792013114346801269)
                    ·
                      refine ⟨1084412605501229470012619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11567067792013114346801269 1084412605501229470012619)
                      ·
                        rfl

theorem cell23_2111886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_2111886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111886 prefixEnd_2111886 := by exact prefixLift 2111886
  have htrace : WordTrace (prefixWord ++ tailWord_2111886) baseStart_2111886 baseEnd_2111886 := by
    simpa [prefixWord, tailWord_2111886, baseEnd_2111886] using wordTrace_append hprefix tailTrace_2111886
  have hstable : (prefixWord ++ tailWord_2111886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111886).length < 2 ^ (prefixWord ++ tailWord_2111886).sum := by decide
  have hdescent : baseEnd_2111886 < baseStart_2111886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111924 : List Nat := [2, 5, 2, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_2111924 : Nat := 118140960795 + 2111924 * 2 ^ 59
def prefixEnd_2111924 : Nat := 4983230072969 + 3 ^ 40 * 2111924 * 2
def baseEnd_2111924 : Nat := 1084432117766100321337445

theorem tailTrace_2111924 : CollatzResearch.WordTrace tailWord_2111924 prefixEnd_2111924 1084432117766100321337445 := by
  unfold tailWord_2111924
  simp only [CollatzResearch.WordTrace]
  refine ⟨38514098200433755374239413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51352130933911673832319217 38514098200433755374239413)
  ·
    refine ⟨3610696706290664566334945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38514098200433755374239413 3610696706290664566334945)
    ·
      refine ⟨2708022529717998424751209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3610696706290664566334945 2708022529717998424751209)
      ·
        refine ⟨2031016897288498818563407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2708022529717998424751209 2031016897288498818563407)
        ·
          refine ⟨3046525345932748227845111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2031016897288498818563407 3046525345932748227845111)
          ·
            refine ⟨4569788018899122341767667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3046525345932748227845111 4569788018899122341767667)
            ·
              refine ⟨6854682028348683512651501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4569788018899122341767667 6854682028348683512651501)
              ·
                refine ⟨2570505760630756317244313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6854682028348683512651501 2570505760630756317244313)
                ·
                  refine ⟨1927879320473067237933235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2570505760630756317244313 1927879320473067237933235)
                  ·
                    refine ⟨2891818980709600856899853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1927879320473067237933235 2891818980709600856899853)
                    ·
                      refine ⟨1084432117766100321337445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2891818980709600856899853 1084432117766100321337445)
                      ·
                        rfl

theorem cell23_2111924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_2111924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111924 prefixEnd_2111924 := by exact prefixLift 2111924
  have htrace : WordTrace (prefixWord ++ tailWord_2111924) baseStart_2111924 baseEnd_2111924 := by
    simpa [prefixWord, tailWord_2111924, baseEnd_2111924] using wordTrace_append hprefix tailTrace_2111924
  have hstable : (prefixWord ++ tailWord_2111924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111924).length < 2 ^ (prefixWord ++ tailWord_2111924).sum := by decide
  have hdescent : baseEnd_2111924 < baseStart_2111924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111976 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_2111976 : Nat := 118140960795 + 2111976 * 2 ^ 59
def prefixEnd_2111976 : Nat := 4983230072969 + 3 ^ 40 * 2111976 * 2
def baseEnd_2111976 : Nat := 1084458818760134117887205

theorem tailTrace_2111976 : CollatzResearch.WordTrace tailWord_2111976 prefixEnd_2111976 1084458818760134117887205 := by
  unfold tailWord_2111976
  simp only [CollatzResearch.WordTrace]
  refine ⟨38515046498339561814685891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51353395331119415752914521 38515046498339561814685891)
  ·
    refine ⟨57772569747509342722028837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38515046498339561814685891 57772569747509342722028837)
    ·
      refine ⟨10832356827658001760380407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57772569747509342722028837 10832356827658001760380407)
      ·
        refine ⟨16248535241487002640570611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10832356827658001760380407 16248535241487002640570611)
        ·
          refine ⟨24372802862230503960855917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16248535241487002640570611 24372802862230503960855917)
          ·
            refine ⟨9139801073336438985320969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24372802862230503960855917 9139801073336438985320969)
            ·
              refine ⟨6854850805002329238990727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9139801073336438985320969 6854850805002329238990727)
              ·
                refine ⟨10282276207503493858486091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6854850805002329238990727 10282276207503493858486091)
                ·
                  refine ⟨15423414311255240787729137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10282276207503493858486091 15423414311255240787729137)
                  ·
                    refine ⟨11567560733441430590796853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15423414311255240787729137 11567560733441430590796853)
                    ·
                      refine ⟨1084458818760134117887205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11567560733441430590796853 1084458818760134117887205)
                      ·
                        rfl

theorem cell23_2111976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_2111976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111976 prefixEnd_2111976 := by exact prefixLift 2111976
  have htrace : WordTrace (prefixWord ++ tailWord_2111976) baseStart_2111976 baseEnd_2111976 := by
    simpa [prefixWord, tailWord_2111976, baseEnd_2111976] using wordTrace_append hprefix tailTrace_2111976
  have hstable : (prefixWord ++ tailWord_2111976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111976).length < 2 ^ (prefixWord ++ tailWord_2111976).sum := by decide
  have hdescent : baseEnd_2111976 < baseStart_2111976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112063 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 1, 5, 2]
def baseStart_2112063 : Nat := 118140960795 + 2112063 * 2 ^ 59
def prefixEnd_2112063 : Nat := 4983230072969 + 3 ^ 40 * 2112063 * 2
def baseEnd_2112063 : Nat := 1084503491577075277499305

theorem tailTrace_2112063 : CollatzResearch.WordTrace tailWord_2112063 prefixEnd_2112063 1084503491577075277499305 := by
  unfold tailWord_2112063
  simp only [CollatzResearch.WordTrace]
  refine ⟨77033266147363937487788843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51355510764909291658525895 77033266147363937487788843)
  ·
    refine ⟨115549899221045906231683265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77033266147363937487788843 115549899221045906231683265)
    ·
      refine ⟨86662424415784429673762449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115549899221045906231683265 86662424415784429673762449)
      ·
        refine ⟨64996818311838322255321837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86662424415784429673762449 64996818311838322255321837)
        ·
          refine ⟨24373806866939370845745689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64996818311838322255321837 24373806866939370845745689)
          ·
            refine ⟨18280355150204528134309267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24373806866939370845745689 18280355150204528134309267)
            ·
              refine ⟨27420532725306792201463901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18280355150204528134309267 27420532725306792201463901)
              ·
                refine ⟨10282699771990047075548963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27420532725306792201463901 10282699771990047075548963)
                ·
                  refine ⟨15424049657985070613323445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10282699771990047075548963 15424049657985070613323445)
                  ·
                    refine ⟨1446004655436100369999073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15424049657985070613323445 1446004655436100369999073)
                    ·
                      refine ⟨1084503491577075277499305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1446004655436100369999073 1084503491577075277499305)
                      ·
                        rfl

theorem cell23_2112063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 5, 2].length) (baseStart_2112063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112063 prefixEnd_2112063 := by exact prefixLift 2112063
  have htrace : WordTrace (prefixWord ++ tailWord_2112063) baseStart_2112063 baseEnd_2112063 := by
    simpa [prefixWord, tailWord_2112063, baseEnd_2112063] using wordTrace_append hprefix tailTrace_2112063
  have hstable : (prefixWord ++ tailWord_2112063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112063).length < 2 ^ (prefixWord ++ tailWord_2112063).sum := by decide
  have hdescent : baseEnd_2112063 < baseStart_2112063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112094 : List Nat := [4, 4, 1, 2, 1, 1, 1, 3, 6]
def baseStart_2112094 : Nat := 118140960795 + 2112094 * 2 ^ 59
def prefixEnd_2112094 : Nat := 4983230072969 + 3 ^ 40 * 2112094 * 2
def baseEnd_2112094 : Nat := 120502156608596072912407

theorem tailTrace_2112094 : CollatzResearch.WordTrace tailWord_2112094 prefixEnd_2112094 120502156608596072912407 := by
  unfold tailWord_2112094
  simp only [CollatzResearch.WordTrace]
  refine ⟨9629299601281453722770917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51356264540167753188111557 9629299601281453722770917)
  ·
    refine ⟨1805493675240272573019547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9629299601281453722770917 1805493675240272573019547)
    ·
      refine ⟨2708240512860408859529321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1805493675240272573019547 2708240512860408859529321)
      ·
        refine ⟨2031180384645306644646991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2708240512860408859529321 2031180384645306644646991)
        ·
          refine ⟨3046770576967959966970487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2031180384645306644646991 3046770576967959966970487)
          ·
            refine ⟨4570155865451939950455731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3046770576967959966970487 4570155865451939950455731)
            ·
              refine ⟨6855233798177909925683597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4570155865451939950455731 6855233798177909925683597)
              ·
                refine ⟨2570712674316716222131349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6855233798177909925683597 2570712674316716222131349)
                ·
                  refine ⟨120502156608596072912407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2570712674316716222131349 120502156608596072912407)
                  ·
                    rfl

theorem cell23_2112094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_2112094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112094 prefixEnd_2112094 := by exact prefixLift 2112094
  have htrace : WordTrace (prefixWord ++ tailWord_2112094) baseStart_2112094 baseEnd_2112094 := by
    simpa [prefixWord, tailWord_2112094, baseEnd_2112094] using wordTrace_append hprefix tailTrace_2112094
  have hstable : (prefixWord ++ tailWord_2112094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112094).length < 2 ^ (prefixWord ++ tailWord_2112094).sum := by decide
  have hdescent : baseEnd_2112094 < baseStart_2112094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112110 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_2112110 : Nat := 118140960795 + 2112110 * 2 ^ 59
def prefixEnd_2112110 : Nat := 4983230072969 + 3 ^ 40 * 2112110 * 2
def baseEnd_2112110 : Nat := 1084527625167836593611589

theorem tailTrace_2112110 : CollatzResearch.WordTrace tailWord_2112110 prefixEnd_2112110 1084527625167836593611589 := by
  unfold tailWord_2112110
  simp only [CollatzResearch.WordTrace]
  refine ⟨9629372547274208064343723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51356653585462443009833189 9629372547274208064343723)
  ·
    refine ⟨14444058820911312096515585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9629372547274208064343723 14444058820911312096515585)
    ·
      refine ⟨10833044115683484072386689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14444058820911312096515585 10833044115683484072386689)
      ·
        refine ⟨8124783086762613054290017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10833044115683484072386689 8124783086762613054290017)
        ·
          refine ⟨6093587315071959790717513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8124783086762613054290017 6093587315071959790717513)
          ·
            refine ⟨4570190486303969843038135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6093587315071959790717513 4570190486303969843038135)
            ·
              refine ⟨6855285729455954764557203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4570190486303969843038135 6855285729455954764557203)
              ·
                refine ⟨10282928594183932146835805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6855285729455954764557203 10282928594183932146835805)
                ·
                  refine ⟨3856098222818974555063427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10282928594183932146835805 3856098222818974555063427)
                  ·
                    refine ⟨5784147334228461832595141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3856098222818974555063427 5784147334228461832595141)
                    ·
                      refine ⟨1084527625167836593611589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5784147334228461832595141 1084527625167836593611589)
                      ·
                        rfl

theorem cell23_2112110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_2112110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112110 prefixEnd_2112110 := by exact prefixLift 2112110
  have htrace : WordTrace (prefixWord ++ tailWord_2112110) baseStart_2112110 baseEnd_2112110 := by
    simpa [prefixWord, tailWord_2112110, baseEnd_2112110] using wordTrace_append hprefix tailTrace_2112110
  have hstable : (prefixWord ++ tailWord_2112110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112110).length < 2 ^ (prefixWord ++ tailWord_2112110).sum := by decide
  have hdescent : baseEnd_2112110 < baseStart_2112110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112138 : List Nat := [3, 1, 2, 3, 4, 1, 2, 2, 1, 1, 3]
def baseStart_2112138 : Nat := 118140960795 + 2112138 * 2 ^ 59
def prefixEnd_2112138 : Nat := 4983230072969 + 3 ^ 40 * 2112138 * 2
def baseEnd_2112138 : Nat := 1084542002626162484061461

theorem tailTrace_2112138 : CollatzResearch.WordTrace tailWord_2112138 prefixEnd_2112138 1084542002626162484061461 := by
  unfold tailWord_2112138
  simp only [CollatzResearch.WordTrace]
  refine ⟨19259000405523056324192267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51357334414728150197846045 19259000405523056324192267)
  ·
    refine ⟨28888500608284584486288401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19259000405523056324192267 28888500608284584486288401)
    ·
      refine ⟨21666375456213438364716301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28888500608284584486288401 21666375456213438364716301)
      ·
        refine ⟨8124890796080039386768613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21666375456213438364716301 8124890796080039386768613)
        ·
          refine ⟨1523417024265007385019115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8124890796080039386768613 1523417024265007385019115)
          ·
            refine ⟨2285125536397511077528673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1523417024265007385019115 2285125536397511077528673)
            ·
              refine ⟨1713844152298133308146505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2285125536397511077528673 1713844152298133308146505)
              ·
                refine ⟨1285383114223599981109879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1713844152298133308146505 1285383114223599981109879)
                ·
                  refine ⟨1928074671335399971664819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1285383114223599981109879 1928074671335399971664819)
                  ·
                    refine ⟨2892112007003099957497229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1928074671335399971664819 2892112007003099957497229)
                    ·
                      refine ⟨1084542002626162484061461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2892112007003099957497229 1084542002626162484061461)
                      ·
                        rfl

theorem cell23_2112138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_2112138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112138 prefixEnd_2112138 := by exact prefixLift 2112138
  have htrace : WordTrace (prefixWord ++ tailWord_2112138) baseStart_2112138 baseEnd_2112138 := by
    simpa [prefixWord, tailWord_2112138, baseEnd_2112138] using wordTrace_append hprefix tailTrace_2112138
  have hstable : (prefixWord ++ tailWord_2112138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112138).length < 2 ^ (prefixWord ++ tailWord_2112138).sum := by decide
  have hdescent : baseEnd_2112138 < baseStart_2112138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112167 : List Nat := [1, 1, 6, 3, 1, 1, 3, 7]
def baseStart_2112167 : Nat := 118140960795 + 2112167 * 2 ^ 59
def prefixEnd_2112167 : Nat := 4983230072969 + 3 ^ 40 * 2112167 * 2
def baseEnd_2112167 : Nat := 40168773835746032244401

theorem tailTrace_2112167 : CollatzResearch.WordTrace tailWord_2112167 prefixEnd_2112167 40168773835746032244401 := by
  unfold tailWord_2112167
  simp only [CollatzResearch.WordTrace]
  refine ⟨77037059338987163249574755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51358039559324775499716503 77037059338987163249574755)
  ·
    refine ⟨115555589008480744874362133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77037059338987163249574755 115555589008480744874362133)
    ·
      refine ⟨5416668234772534915985725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 115555589008480744874362133 5416668234772534915985725)
      ·
        refine ⟨2031250588039700593494647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5416668234772534915985725 2031250588039700593494647)
        ·
          refine ⟨3046875882059550890241971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2031250588039700593494647 3046875882059550890241971)
          ·
            refine ⟨4570313823089326335362957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3046875882059550890241971 4570313823089326335362957)
            ·
              refine ⟨1713867683658497375761109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4570313823089326335362957 1713867683658497375761109)
              ·
                refine ⟨40168773835746032244401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1713867683658497375761109 40168773835746032244401)
                ·
                  rfl

theorem cell23_2112167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 7].length) (baseStart_2112167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112167 prefixEnd_2112167 := by exact prefixLift 2112167
  have htrace : WordTrace (prefixWord ++ tailWord_2112167) baseStart_2112167 baseEnd_2112167 := by
    simpa [prefixWord, tailWord_2112167, baseEnd_2112167] using wordTrace_append hprefix tailTrace_2112167
  have hstable : (prefixWord ++ tailWord_2112167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112167).length < 2 ^ (prefixWord ++ tailWord_2112167).sum := by decide
  have hdescent : baseEnd_2112167 < baseStart_2112167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112176 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 3, 8]
def baseStart_2112176 : Nat := 118140960795 + 2112176 * 2 ^ 59
def prefixEnd_2112176 : Nat := 4983230072969 + 3 ^ 40 * 2112176 * 2
def baseEnd_2112176 : Nat := 361520504963677778462095

theorem tailTrace_2112176 : CollatzResearch.WordTrace tailWord_2112176 prefixEnd_2112176 361520504963677778462095 := by
  unfold tailWord_2112176
  simp only [CollatzResearch.WordTrace]
  refine ⟨38518693797977278893326191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51358258397303038524434921 38518693797977278893326191)
  ·
    refine ⟨57778040696965918339989287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38518693797977278893326191 57778040696965918339989287)
    ·
      refine ⟨86667061045448877509983931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57778040696965918339989287 86667061045448877509983931)
      ·
        refine ⟨130000591568173316264975897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86667061045448877509983931 130000591568173316264975897)
        ·
          refine ⟨97500443676129987198731923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130000591568173316264975897 97500443676129987198731923)
          ·
            refine ⟨146250665514194980798097885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97500443676129987198731923 146250665514194980798097885)
            ·
              refine ⟨54843999567823117799286707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146250665514194980798097885 54843999567823117799286707)
              ·
                refine ⟨82265999351734676698930061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54843999567823117799286707 82265999351734676698930061)
                ·
                  refine ⟨30849749756900503762098773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82265999351734676698930061 30849749756900503762098773)
                  ·
                    refine ⟨361520504963677778462095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30849749756900503762098773 361520504963677778462095)
                    ·
                      rfl

theorem cell23_2112176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 8].length) (baseStart_2112176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112176 prefixEnd_2112176 := by exact prefixLift 2112176
  have htrace : WordTrace (prefixWord ++ tailWord_2112176) baseStart_2112176 baseEnd_2112176 := by
    simpa [prefixWord, tailWord_2112176, baseEnd_2112176] using wordTrace_append hprefix tailTrace_2112176
  have hstable : (prefixWord ++ tailWord_2112176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112176).length < 2 ^ (prefixWord ++ tailWord_2112176).sum := by decide
  have hdescent : baseEnd_2112176 < baseStart_2112176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112223 : List Nat := [1, 1, 2, 3, 2, 3, 2, 2, 7]
def baseStart_2112223 : Nat := 118140960795 + 2112223 * 2 ^ 59
def prefixEnd_2112223 : Nat := 4983230072969 + 3 ^ 40 * 2112223 * 2
def baseEnd_2112223 : Nat := 120509516497977183499841

theorem tailTrace_2112223 : CollatzResearch.WordTrace tailWord_2112223 prefixEnd_2112223 120509516497977183499841 := by
  unfold tailWord_2112223
  simp only [CollatzResearch.WordTrace]
  refine ⟨77039101826784284813613323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51359401217856189875742215 77039101826784284813613323)
  ·
    refine ⟨115558652740176427220419985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77039101826784284813613323 115558652740176427220419985)
    ·
      refine ⟨86668989555132320415314989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115558652740176427220419985 86668989555132320415314989)
      ·
        refine ⟨32500871083174620155743121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86668989555132320415314989 32500871083174620155743121)
        ·
          refine ⟨24375653312380965116807341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32500871083174620155743121 24375653312380965116807341)
          ·
            refine ⟨9140869992142861918802753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24375653312380965116807341 9140869992142861918802753)
            ·
              refine ⟨6855652494107146439102065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9140869992142861918802753 6855652494107146439102065)
              ·
                refine ⟨5141739370580359829326549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6855652494107146439102065 5141739370580359829326549)
                ·
                  refine ⟨120509516497977183499841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5141739370580359829326549 120509516497977183499841)
                  ·
                    rfl

theorem cell23_2112223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 7].length) (baseStart_2112223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112223 prefixEnd_2112223 := by exact prefixLift 2112223
  have htrace : WordTrace (prefixWord ++ tailWord_2112223) baseStart_2112223 baseEnd_2112223 := by
    simpa [prefixWord, tailWord_2112223, baseEnd_2112223] using wordTrace_append hprefix tailTrace_2112223
  have hstable : (prefixWord ++ tailWord_2112223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112223).length < 2 ^ (prefixWord ++ tailWord_2112223).sum := by decide
  have hdescent : baseEnd_2112223 < baseStart_2112223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112233 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 1, 5, 3]
def baseStart_2112233 : Nat := 118140960795 + 2112233 * 2 ^ 59
def prefixEnd_2112233 : Nat := 4983230072969 + 3 ^ 40 * 2112233 * 2
def baseEnd_2112233 : Nat := 1084590783288339612373523

theorem tailTrace_2112233 : CollatzResearch.WordTrace tailWord_2112233 prefixEnd_2112233 1084590783288339612373523 := by
  unfold tailWord_2112233
  simp only [CollatzResearch.WordTrace]
  refine ⟨77039466556748056521477353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51359644371165371014318235 77039466556748056521477353)
  ·
    refine ⟨57779599917561042391108015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77039466556748056521477353 57779599917561042391108015)
    ·
      refine ⟨86669399876341563586662023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57779599917561042391108015 86669399876341563586662023)
      ·
        refine ⟨130004099814512345379993035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86669399876341563586662023 130004099814512345379993035)
        ·
          refine ⟨195006149721768518069989553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130004099814512345379993035 195006149721768518069989553)
          ·
            refine ⟨146254612291326388552492165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195006149721768518069989553 146254612291326388552492165)
            ·
              refine ⟨27422739804623697853592281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146254612291326388552492165 27422739804623697853592281)
              ·
                refine ⟨20567054853467773390194211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27422739804623697853592281 20567054853467773390194211)
                ·
                  refine ⟨30850582280201660085291317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20567054853467773390194211 30850582280201660085291317)
                  ·
                    refine ⟨2892242088768905632996061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30850582280201660085291317 2892242088768905632996061)
                    ·
                      refine ⟨1084590783288339612373523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2892242088768905632996061 1084590783288339612373523)
                      ·
                        rfl

theorem cell23_2112233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 5, 3].length) (baseStart_2112233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112233 prefixEnd_2112233 := by exact prefixLift 2112233
  have htrace : WordTrace (prefixWord ++ tailWord_2112233) baseStart_2112233 baseEnd_2112233 := by
    simpa [prefixWord, tailWord_2112233, baseEnd_2112233] using wordTrace_append hprefix tailTrace_2112233
  have hstable : (prefixWord ++ tailWord_2112233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112233).length < 2 ^ (prefixWord ++ tailWord_2112233).sum := by decide
  have hdescent : baseEnd_2112233 < baseStart_2112233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112273 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 4]
def baseStart_2112273 : Nat := 118140960795 + 2112273 * 2 ^ 59
def prefixEnd_2112273 : Nat := 4983230072969 + 3 ^ 40 * 2112273 * 2
def baseEnd_2112273 : Nat := 1084611322514519455873339

theorem tailTrace_2112273 : CollatzResearch.WordTrace tailWord_2112273 prefixEnd_2112273 1084611322514519455873339 := by
  unfold tailWord_2112273
  simp only [CollatzResearch.WordTrace]
  refine ⟨77040925476603143352933473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51360616984402095568622315 77040925476603143352933473)
  ·
    refine ⟨57780694107452357514700105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77040925476603143352933473 57780694107452357514700105)
    ·
      refine ⟨43335520580589268136025079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57780694107452357514700105 43335520580589268136025079)
      ·
        refine ⟨65003280870883902204037619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43335520580589268136025079 65003280870883902204037619)
        ·
          refine ⟨97504921306325853306056429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65003280870883902204037619 97504921306325853306056429)
          ·
            refine ⟨36564345489872194989771161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97504921306325853306056429 36564345489872194989771161)
            ·
              refine ⟨27423259117404146242328371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36564345489872194989771161 27423259117404146242328371)
              ·
                refine ⟨41134888676106219363492557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27423259117404146242328371 41134888676106219363492557)
                ·
                  refine ⟨15425583253539832261309709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41134888676106219363492557 15425583253539832261309709)
                  ·
                    refine ⟨5784593720077437097991141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15425583253539832261309709 5784593720077437097991141)
                    ·
                      refine ⟨1084611322514519455873339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5784593720077437097991141 1084611322514519455873339)
                      ·
                        rfl

theorem cell23_2112273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_2112273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112273 prefixEnd_2112273 := by exact prefixLift 2112273
  have htrace : WordTrace (prefixWord ++ tailWord_2112273) baseStart_2112273 baseEnd_2112273 := by
    simpa [prefixWord, tailWord_2112273, baseEnd_2112273] using wordTrace_append hprefix tailTrace_2112273
  have hstable : (prefixWord ++ tailWord_2112273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112273).length < 2 ^ (prefixWord ++ tailWord_2112273).sum := by decide
  have hdescent : baseEnd_2112273 < baseStart_2112273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112308 : List Nat := [2, 5, 1, 1, 4, 1, 2, 2, 5]
def baseStart_2112308 : Nat := 118140960795 + 2112308 * 2 ^ 59
def prefixEnd_2112308 : Nat := 4983230072969 + 3 ^ 40 * 2112308 * 2
def baseEnd_2112308 : Nat := 120514366037491868770631

theorem tailTrace_2112308 : CollatzResearch.WordTrace tailWord_2112308 prefixEnd_2112308 120514366037491868770631 := by
  unfold tailWord_2112308
  simp only [CollatzResearch.WordTrace]
  refine ⟨38521101015738172165228789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51361468020984229553638385 38521101015738172165228789)
  ·
    refine ⟨3611353220225453640490199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38521101015738172165228789 3611353220225453640490199)
    ·
      refine ⟨5417029830338180460735299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3611353220225453640490199 5417029830338180460735299)
      ·
        refine ⟨8125544745507270691102949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5417029830338180460735299 8125544745507270691102949)
        ·
          refine ⟨1523539639782613254581803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8125544745507270691102949 1523539639782613254581803)
          ·
            refine ⟨2285309459673919881872705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1523539639782613254581803 2285309459673919881872705)
            ·
              refine ⟨1713982094755439911404529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2285309459673919881872705 1713982094755439911404529)
              ·
                refine ⟨1285486571066579933553397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1713982094755439911404529 1285486571066579933553397)
                ·
                  refine ⟨120514366037491868770631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1285486571066579933553397 120514366037491868770631)
                  ·
                    rfl

theorem cell23_2112308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_2112308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112308 prefixEnd_2112308 := by exact prefixLift 2112308
  have htrace : WordTrace (prefixWord ++ tailWord_2112308) baseStart_2112308 baseEnd_2112308 := by
    simpa [prefixWord, tailWord_2112308, baseEnd_2112308] using wordTrace_append hprefix tailTrace_2112308
  have hstable : (prefixWord ++ tailWord_2112308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112308).length < 2 ^ (prefixWord ++ tailWord_2112308).sum := by decide
  have hdescent : baseEnd_2112308 < baseStart_2112308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112367 : List Nat := [1, 1, 2, 1, 3, 1, 1, 6, 2, 3, 2]
def baseStart_2112367 : Nat := 118140960795 + 2112367 * 2 ^ 59
def prefixEnd_2112367 : Nat := 4983230072969 + 3 ^ 40 * 2112367 * 2
def baseEnd_2112367 : Nat := 1084659589696042088097907

theorem tailTrace_2112367 : CollatzResearch.WordTrace tailWord_2112367 prefixEnd_2112367 1084659589696042088097907 := by
  unfold tailWord_2112367
  simp only [CollatzResearch.WordTrace]
  refine ⟨77044353938262597406855355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51362902625508398271236903 77044353938262597406855355)
  ·
    refine ⟨115566530907393896110283033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77044353938262597406855355 115566530907393896110283033)
    ·
      refine ⟨86674898180545422082712275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115566530907393896110283033 86674898180545422082712275)
      ·
        refine ⟨130012347270818133124068413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86674898180545422082712275 130012347270818133124068413)
        ·
          refine ⟨48754630226556799921525655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130012347270818133124068413 48754630226556799921525655)
          ·
            refine ⟨73131945339835199882288483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48754630226556799921525655 73131945339835199882288483)
            ·
              refine ⟨109697918009752799823432725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73131945339835199882288483 109697918009752799823432725)
              ·
                refine ⟨5142089906707162491723409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 109697918009752799823432725 5142089906707162491723409)
                ·
                  refine ⟨3856567430030371868792557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5142089906707162491723409 3856567430030371868792557)
                  ·
                    refine ⟨1446212786261389450797209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3856567430030371868792557 1446212786261389450797209)
                    ·
                      refine ⟨1084659589696042088097907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1446212786261389450797209 1084659589696042088097907)
                      ·
                        rfl

theorem cell23_2112367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 3, 2].length) (baseStart_2112367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112367 prefixEnd_2112367 := by exact prefixLift 2112367
  have htrace : WordTrace (prefixWord ++ tailWord_2112367) baseStart_2112367 baseEnd_2112367 := by
    simpa [prefixWord, tailWord_2112367, baseEnd_2112367] using wordTrace_append hprefix tailTrace_2112367
  have hstable : (prefixWord ++ tailWord_2112367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112367).length < 2 ^ (prefixWord ++ tailWord_2112367).sum := by decide
  have hdescent : baseEnd_2112367 < baseStart_2112367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112380 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 5, 1, 4]
def baseStart_2112380 : Nat := 118140960795 + 2112380 * 2 ^ 59
def prefixEnd_2112380 : Nat := 4983230072969 + 3 ^ 40 * 2112380 * 2
def baseEnd_2112380 : Nat := 1084666264944550537235347

theorem tailTrace_2112380 : CollatzResearch.WordTrace tailWord_2112380 prefixEnd_2112380 1084666264944550537235347 := by
  unfold tailWord_2112380
  simp only [CollatzResearch.WordTrace]
  refine ⟨38522414043607750313539297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51363218724810333751385729 38522414043607750313539297)
  ·
    refine ⟨28891810532705812735154473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38522414043607750313539297 28891810532705812735154473)
    ·
      refine ⟨21668857899529359551365855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28891810532705812735154473 21668857899529359551365855)
      ·
        refine ⟨32503286849294039327048783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21668857899529359551365855 32503286849294039327048783)
        ·
          refine ⟨48754930273941058990573175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32503286849294039327048783 48754930273941058990573175)
          ·
            refine ⟨73132395410911588485859763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48754930273941058990573175 73132395410911588485859763)
            ·
              refine ⟨109698593116367382728789645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73132395410911588485859763 109698593116367382728789645)
              ·
                refine ⟨41136972418637768523296117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109698593116367382728789645 41136972418637768523296117)
                ·
                  refine ⟨3856591164247290799059011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41136972418637768523296117 3856591164247290799059011)
                  ·
                    refine ⟨5784886746370936198588517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3856591164247290799059011 5784886746370936198588517)
                    ·
                      refine ⟨1084666264944550537235347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5784886746370936198588517 1084666264944550537235347)
                      ·
                        rfl

theorem cell23_2112380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_2112380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112380 prefixEnd_2112380 := by exact prefixLift 2112380
  have htrace : WordTrace (prefixWord ++ tailWord_2112380) baseStart_2112380 baseEnd_2112380 := by
    simpa [prefixWord, tailWord_2112380, baseEnd_2112380] using wordTrace_append hprefix tailTrace_2112380
  have hstable : (prefixWord ++ tailWord_2112380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112380).length < 2 ^ (prefixWord ++ tailWord_2112380).sum := by decide
  have hdescent : baseEnd_2112380 < baseStart_2112380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112394 : List Nat := [3, 1, 2, 4, 1, 2, 2, 2, 1, 5]
def baseStart_2112394 : Nat := 118140960795 + 2112394 * 2 ^ 59
def prefixEnd_2112394 : Nat := 4983230072969 + 3 ^ 40 * 2112394 * 2
def baseEnd_2112394 : Nat := 361557817891237827486761

theorem tailTrace_2112394 : CollatzResearch.WordTrace tailWord_2112394 prefixEnd_2112394 361557817891237827486761 := by
  unfold tailWord_2112394
  simp only [CollatzResearch.WordTrace]
  refine ⟨19261334677291195254522059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51363559139443187345392157 19261334677291195254522059)
  ·
    refine ⟨28892002015936792881783089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19261334677291195254522059 28892002015936792881783089)
    ·
      refine ⟨21669001511952594661337317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28892002015936792881783089 21669001511952594661337317)
      ·
        refine ⟨4062937783491111499000747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21669001511952594661337317 4062937783491111499000747)
        ·
          refine ⟨6094406675236667248501121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4062937783491111499000747 6094406675236667248501121)
          ·
            refine ⟨4570805006427500436375841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6094406675236667248501121 4570805006427500436375841)
            ·
              refine ⟨3428103754820625327281881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4570805006427500436375841 3428103754820625327281881)
              ·
                refine ⟨2571077816115468995461411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3428103754820625327281881 2571077816115468995461411)
                ·
                  refine ⟨3856616724173203493192117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2571077816115468995461411 3856616724173203493192117)
                  ·
                    refine ⟨361557817891237827486761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3856616724173203493192117 361557817891237827486761)
                    ·
                      rfl

theorem cell23_2112394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_2112394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112394 prefixEnd_2112394 := by exact prefixLift 2112394
  have htrace : WordTrace (prefixWord ++ tailWord_2112394) baseStart_2112394 baseEnd_2112394 := by
    simpa [prefixWord, tailWord_2112394, baseEnd_2112394] using wordTrace_append hprefix tailTrace_2112394
  have hstable : (prefixWord ++ tailWord_2112394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112394).length < 2 ^ (prefixWord ++ tailWord_2112394).sum := by decide
  have hdescent : baseEnd_2112394 < baseStart_2112394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112417 : List Nat := [1, 2, 3, 4, 1, 1, 1, 3, 1, 1, 5]
def baseStart_2112417 : Nat := 118140960795 + 2112417 * 2 ^ 59
def prefixEnd_2112417 : Nat := 4983230072969 + 3 ^ 40 * 2112417 * 2
def baseEnd_2112417 : Nat := 1084685263728766892472677

theorem tailTrace_2112417 : CollatzResearch.WordTrace tailWord_2112417 prefixEnd_2112417 1084685263728766892472677 := by
  unfold tailWord_2112417
  simp only [CollatzResearch.WordTrace]
  refine ⟨77046177588081455946175505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51364118392054303964117003 77046177588081455946175505)
  ·
    refine ⟨57784633191061091959631629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77046177588081455946175505 57784633191061091959631629)
    ·
      refine ⟨21669237446647909484861861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57784633191061091959631629 21669237446647909484861861)
      ·
        refine ⟨4062982021246483028411599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21669237446647909484861861 4062982021246483028411599)
        ·
          refine ⟨6094473031869724542617399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4062982021246483028411599 6094473031869724542617399)
          ·
            refine ⟨9141709547804586813926099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6094473031869724542617399 9141709547804586813926099)
            ·
              refine ⟨13712564321706880220889149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9141709547804586813926099 13712564321706880220889149)
              ·
                refine ⟨5142211620640080082833431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13712564321706880220889149 5142211620640080082833431)
                ·
                  refine ⟨7713317430960120124250147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5142211620640080082833431 7713317430960120124250147)
                  ·
                    refine ⟨11569976146440180186375221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7713317430960120124250147 11569976146440180186375221)
                    ·
                      refine ⟨1084685263728766892472677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11569976146440180186375221 1084685263728766892472677)
                      ·
                        rfl

theorem cell23_2112417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_2112417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112417 prefixEnd_2112417 := by exact prefixLift 2112417
  have htrace : WordTrace (prefixWord ++ tailWord_2112417) baseStart_2112417 baseEnd_2112417 := by
    simpa [prefixWord, tailWord_2112417, baseEnd_2112417] using wordTrace_append hprefix tailTrace_2112417
  have hstable : (prefixWord ++ tailWord_2112417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112417).length < 2 ^ (prefixWord ++ tailWord_2112417).sum := by decide
  have hdescent : baseEnd_2112417 < baseStart_2112417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112441 : List Nat := [1, 2, 1, 4, 2, 4, 2, 1, 2, 4]
def baseStart_2112441 : Nat := 118140960795 + 2112441 * 2 ^ 59
def prefixEnd_2112441 : Nat := 4983230072969 + 3 ^ 40 * 2112441 * 2
def baseEnd_2112441 : Nat := 361565862421491599524189

theorem tailTrace_2112441 : CollatzResearch.WordTrace tailWord_2112441 prefixEnd_2112441 361565862421491599524189 := by
  unfold tailWord_2112441
  simp only [CollatzResearch.WordTrace]
  refine ⟨77047052939994508045049177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51364701959996338696699451 77047052939994508045049177)
  ·
    refine ⟨57785289704995881033786883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77047052939994508045049177 57785289704995881033786883)
    ·
      refine ⟨86677934557493821550680325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57785289704995881033786883 86677934557493821550680325)
      ·
        refine ⟨16252112729530091540752561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86677934557493821550680325 16252112729530091540752561)
        ·
          refine ⟨12189084547147568655564421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16252112729530091540752561 12189084547147568655564421)
          ·
            refine ⟨2285453352590169122918329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12189084547147568655564421 2285453352590169122918329)
            ·
              refine ⟨1714090014442626842188747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2285453352590169122918329 1714090014442626842188747)
              ·
                refine ⟨2571135021663940263283121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1714090014442626842188747 2571135021663940263283121)
                ·
                  refine ⟨1928351266247955197462341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2571135021663940263283121 1928351266247955197462341)
                  ·
                    refine ⟨361565862421491599524189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1928351266247955197462341 361565862421491599524189)
                    ·
                      rfl

theorem cell23_2112441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 2, 4].length) (baseStart_2112441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112441 prefixEnd_2112441 := by exact prefixLift 2112441
  have htrace : WordTrace (prefixWord ++ tailWord_2112441) baseStart_2112441 baseEnd_2112441 := by
    simpa [prefixWord, tailWord_2112441, baseEnd_2112441] using wordTrace_append hprefix tailTrace_2112441
  have hstable : (prefixWord ++ tailWord_2112441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112441).length < 2 ^ (prefixWord ++ tailWord_2112441).sum := by decide
  have hdescent : baseEnd_2112441 < baseStart_2112441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112447 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 6, 1, 3]
def baseStart_2112447 : Nat := 118140960795 + 2112447 * 2 ^ 59
def prefixEnd_2112447 : Nat := 4983230072969 + 3 ^ 40 * 2112447 * 2
def baseEnd_2112447 : Nat := 1084700668148401775097539

theorem tailTrace_2112447 : CollatzResearch.WordTrace tailWord_2112447 prefixEnd_2112447 1084700668148401775097539 := by
  unfold tailWord_2112447
  simp only [CollatzResearch.WordTrace]
  refine ⟨77047271777972771069767595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51364847851981847379845063 77047271777972771069767595)
  ·
    refine ⟨115570907666959156604651393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77047271777972771069767595 115570907666959156604651393)
    ·
      refine ⟨86678180750219367453488545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115570907666959156604651393 86678180750219367453488545)
      ·
        refine ⟨65008635562664525590116409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86678180750219367453488545 65008635562664525590116409)
        ·
          refine ⟨48756476671998394192587307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65008635562664525590116409 48756476671998394192587307)
          ·
            refine ⟨73134715007997591288880961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48756476671998394192587307 73134715007997591288880961)
            ·
              refine ⟨54851036255998193466660721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73134715007997591288880961 54851036255998193466660721)
              ·
                refine ⟨41138277191998645099995541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54851036255998193466660721 41138277191998645099995541)
                ·
                  refine ⟨1928356743374936489062291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41138277191998645099995541 1928356743374936489062291)
                  ·
                    refine ⟨2892535115062404733593437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1928356743374936489062291 2892535115062404733593437)
                    ·
                      refine ⟨1084700668148401775097539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2892535115062404733593437 1084700668148401775097539)
                      ·
                        rfl

theorem cell23_2112447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 1, 3].length) (baseStart_2112447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112447 prefixEnd_2112447 := by exact prefixLift 2112447
  have htrace : WordTrace (prefixWord ++ tailWord_2112447) baseStart_2112447 baseEnd_2112447 := by
    simpa [prefixWord, tailWord_2112447, baseEnd_2112447] using wordTrace_append hprefix tailTrace_2112447
  have hstable : (prefixWord ++ tailWord_2112447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112447).length < 2 ^ (prefixWord ++ tailWord_2112447).sum := by decide
  have hdescent : baseEnd_2112447 < baseStart_2112447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112482 : List Nat := [3, 3, 3, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_2112482 : Nat := 118140960795 + 2112482 * 2 ^ 59
def prefixEnd_2112482 : Nat := 4983230072969 + 3 ^ 40 * 2112482 * 2
def baseEnd_2112482 : Nat := 1084718639971309138159879

theorem tailTrace_2112482 : CollatzResearch.WordTrace tailWord_2112482 prefixEnd_2112482 1084718639971309138159879 := by
  unfold tailWord_2112482
  simp only [CollatzResearch.WordTrace]
  refine ⟨19262137083211493011822925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51365698888563981364861133 19262137083211493011822925)
  ·
    refine ⟨7223301406204309879433597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19262137083211493011822925 7223301406204309879433597)
    ·
      refine ⟨2708738027326616204787599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7223301406204309879433597 2708738027326616204787599)
      ·
        refine ⟨4063107040989924307181399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2708738027326616204787599 4063107040989924307181399)
        ·
          refine ⟨6094660561484886460772099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4063107040989924307181399 6094660561484886460772099)
          ·
            refine ⟨9141990842227329691158149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6094660561484886460772099 9141990842227329691158149)
            ·
              refine ⟨1714123282917624317092153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9141990842227329691158149 1714123282917624317092153)
              ·
                refine ⟨1285592462188218237819115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1714123282917624317092153 1285592462188218237819115)
                ·
                  refine ⟨1928388693282327356728673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1285592462188218237819115 1928388693282327356728673)
                  ·
                    refine ⟨1446291519961745517546505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1928388693282327356728673 1446291519961745517546505)
                    ·
                      refine ⟨1084718639971309138159879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1446291519961745517546505 1084718639971309138159879)
                      ·
                        rfl

theorem cell23_2112482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_2112482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112482 prefixEnd_2112482 := by exact prefixLift 2112482
  have htrace : WordTrace (prefixWord ++ tailWord_2112482) baseStart_2112482 baseEnd_2112482 := by
    simpa [prefixWord, tailWord_2112482, baseEnd_2112482] using wordTrace_append hprefix tailTrace_2112482
  have hstable : (prefixWord ++ tailWord_2112482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112482).length < 2 ^ (prefixWord ++ tailWord_2112482).sum := by decide
  have hdescent : baseEnd_2112482 < baseStart_2112482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112487 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_2112487 : Nat := 118140960795 + 2112487 * 2 ^ 59
def prefixEnd_2112487 : Nat := 4983230072969 + 3 ^ 40 * 2112487 * 2
def baseEnd_2112487 : Nat := 1084721207374581618597355

theorem tailTrace_2112487 : CollatzResearch.WordTrace tailWord_2112487 prefixEnd_2112487 1084721207374581618597355 := by
  unfold tailWord_2112487
  simp only [CollatzResearch.WordTrace]
  refine ⟨77048730697827857901223715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51365820465218571934149143 77048730697827857901223715)
  ·
    refine ⟨115573096046741786851835573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77048730697827857901223715 115573096046741786851835573)
    ·
      refine ⟨10834977754382042517359585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115573096046741786851835573 10834977754382042517359585)
      ·
        refine ⟨8126233315786531888019689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10834977754382042517359585 8126233315786531888019689)
        ·
          refine ⟨6094674986839898916014767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8126233315786531888019689 6094674986839898916014767)
          ·
            refine ⟨9142012480259848374022151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6094674986839898916014767 9142012480259848374022151)
            ·
              refine ⟨13713018720389772561033227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9142012480259848374022151 13713018720389772561033227)
              ·
                refine ⟨20569528080584658841549841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13713018720389772561033227 20569528080584658841549841)
                ·
                  refine ⟨15427146060438494131162381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20569528080584658841549841 15427146060438494131162381)
                  ·
                    refine ⟨5785179772664435299185893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15427146060438494131162381 5785179772664435299185893)
                    ·
                      refine ⟨1084721207374581618597355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5785179772664435299185893 1084721207374581618597355)
                      ·
                        rfl

theorem cell23_2112487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_2112487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112487 prefixEnd_2112487 := by exact prefixLift 2112487
  have htrace : WordTrace (prefixWord ++ tailWord_2112487) baseStart_2112487 baseEnd_2112487 := by
    simpa [prefixWord, tailWord_2112487, baseEnd_2112487] using wordTrace_append hprefix tailTrace_2112487
  have hstable : (prefixWord ++ tailWord_2112487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112487).length < 2 ^ (prefixWord ++ tailWord_2112487).sum := by decide
  have hdescent : baseEnd_2112487 < baseStart_2112487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112497 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 2, 6]
def baseStart_2112497 : Nat := 118140960795 + 2112497 * 2 ^ 59
def prefixEnd_2112497 : Nat := 4983230072969 + 3 ^ 40 * 2112497 * 2
def baseEnd_2112497 : Nat := 361575447393708859824103

theorem tailTrace_2112497 : CollatzResearch.WordTrace tailWord_2112497 prefixEnd_2112497 361575447393708859824103 := by
  unfold tailWord_2112497
  simp only [CollatzResearch.WordTrace]
  refine ⟨77049095427791629609087745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51366063618527753072725163 77049095427791629609087745)
  ·
    refine ⟨57786821570843722206815809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77049095427791629609087745 57786821570843722206815809)
    ·
      refine ⟨43340116178132791655111857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57786821570843722206815809 43340116178132791655111857)
      ·
        refine ⟨32505087133599593741333893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43340116178132791655111857 32505087133599593741333893)
        ·
          refine ⟨6094703837549923826500105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32505087133599593741333893 6094703837549923826500105)
          ·
            refine ⟨4571027878162442869875079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6094703837549923826500105 4571027878162442869875079)
            ·
              refine ⟨6856541817243664304812619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4571027878162442869875079 6856541817243664304812619)
              ·
                refine ⟨10284812725865496457218929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6856541817243664304812619 10284812725865496457218929)
                ·
                  refine ⟨7713609544399122342914197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10284812725865496457218929 7713609544399122342914197)
                  ·
                    refine ⟨361575447393708859824103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7713609544399122342914197 361575447393708859824103)
                    ·
                      rfl

theorem cell23_2112497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_2112497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112497 prefixEnd_2112497 := by exact prefixLift 2112497
  have htrace : WordTrace (prefixWord ++ tailWord_2112497) baseStart_2112497 baseEnd_2112497 := by
    simpa [prefixWord, tailWord_2112497, baseEnd_2112497] using wordTrace_append hprefix tailTrace_2112497
  have hstable : (prefixWord ++ tailWord_2112497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112497).length < 2 ^ (prefixWord ++ tailWord_2112497).sum := by decide
  have hdescent : baseEnd_2112497 < baseStart_2112497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112504 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 6, 2, 2]
def baseStart_2112504 : Nat := 118140960795 + 2112504 * 2 ^ 59
def prefixEnd_2112504 : Nat := 4983230072969 + 3 ^ 40 * 2112504 * 2
def baseEnd_2112504 : Nat := 1084729936545708052084777

theorem tailTrace_2112504 : CollatzResearch.WordTrace tailWord_2112504 prefixEnd_2112504 1084729936545708052084777 := by
  unfold tailWord_2112504
  simp only [CollatzResearch.WordTrace]
  refine ⟨38524675369383134902296283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51366233825844179869728377 38524675369383134902296283)
  ·
    refine ⟨57787013054074702353444425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38524675369383134902296283 57787013054074702353444425)
    ·
      refine ⟨43340259790556026765083319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57787013054074702353444425 43340259790556026765083319)
      ·
        refine ⟨65010389685834040147624979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43340259790556026765083319 65010389685834040147624979)
        ·
          refine ⟨97515584528751060221437469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65010389685834040147624979 97515584528751060221437469)
          ·
            refine ⟨36568344198281647583039051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97515584528751060221437469 36568344198281647583039051)
            ·
              refine ⟨54852516297422471374558577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36568344198281647583039051 54852516297422471374558577)
              ·
                refine ⟨41139387223066853530918933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54852516297422471374558577 41139387223066853530918933)
                ·
                  refine ⟨1928408776081258759261825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41139387223066853530918933 1928408776081258759261825)
                  ·
                    refine ⟨1446306582060944069446369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1928408776081258759261825 1446306582060944069446369)
                    ·
                      refine ⟨1084729936545708052084777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1446306582060944069446369 1084729936545708052084777)
                      ·
                        rfl

theorem cell23_2112504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 6, 2, 2].length) (baseStart_2112504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112504 prefixEnd_2112504 := by exact prefixLift 2112504
  have htrace : WordTrace (prefixWord ++ tailWord_2112504) baseStart_2112504 baseEnd_2112504 := by
    simpa [prefixWord, tailWord_2112504, baseEnd_2112504] using wordTrace_append hprefix tailTrace_2112504
  have hstable : (prefixWord ++ tailWord_2112504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112504).length < 2 ^ (prefixWord ++ tailWord_2112504).sum := by decide
  have hdescent : baseEnd_2112504 < baseStart_2112504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112537 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 2, 3, 3]
def baseStart_2112537 : Nat := 118140960795 + 2112537 * 2 ^ 59
def prefixEnd_2112537 : Nat := 4983230072969 + 3 ^ 40 * 2112537 * 2
def baseEnd_2112537 : Nat := 1084746881407306422972125

theorem tailTrace_2112537 : CollatzResearch.WordTrace tailWord_2112537 prefixEnd_2112537 1084746881407306422972125 := by
  unfold tailWord_2112537
  simp only [CollatzResearch.WordTrace]
  refine ⟨77050554347646716440543865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51367036231764477627029243 77050554347646716440543865)
  ·
    refine ⟨57787915760735037330407899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77050554347646716440543865 57787915760735037330407899)
    ·
      refine ⟨86681873641102555995611849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57787915760735037330407899 86681873641102555995611849)
      ·
        refine ⟨65011405230826916996708887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86681873641102555995611849 65011405230826916996708887)
        ·
          refine ⟨97517107846240375495063331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65011405230826916996708887 97517107846240375495063331)
          ·
            refine ⟨146275661769360563242594997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97517107846240375495063331 146275661769360563242594997)
            ·
              refine ⟨13713343290877552803993281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 146275661769360563242594997 13713343290877552803993281)
              ·
                refine ⟨10285007468158164602994961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13713343290877552803993281 10285007468158164602994961)
                ·
                  refine ⟨7713755601118623452246221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10285007468158164602994961 7713755601118623452246221)
                  ·
                    refine ⟨2892658350419483794592333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7713755601118623452246221 2892658350419483794592333)
                    ·
                      refine ⟨1084746881407306422972125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2892658350419483794592333 1084746881407306422972125)
                      ·
                        rfl

theorem cell23_2112537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 3, 3].length) (baseStart_2112537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112537 prefixEnd_2112537 := by exact prefixLift 2112537
  have htrace : WordTrace (prefixWord ++ tailWord_2112537) baseStart_2112537 baseEnd_2112537 := by
    simpa [prefixWord, tailWord_2112537, baseEnd_2112537] using wordTrace_append hprefix tailTrace_2112537
  have hstable : (prefixWord ++ tailWord_2112537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112537).length < 2 ^ (prefixWord ++ tailWord_2112537).sum := by decide
  have hdescent : baseEnd_2112537 < baseStart_2112537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112574 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 1, 7]
def baseStart_2112574 : Nat := 118140960795 + 2112574 * 2 ^ 59
def prefixEnd_2112574 : Nat := 4983230072969 + 3 ^ 40 * 2112574 * 2
def baseEnd_2112574 : Nat := 361588626730507592736485

theorem tailTrace_2112574 : CollatzResearch.WordTrace tailWord_2112574 prefixEnd_2112574 361588626730507592736485 := by
  unfold tailWord_2112574
  simp only [CollatzResearch.WordTrace]
  refine ⟨9631487981064083969955097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51367935899008447839760517 9631487981064083969955097)
  ·
    refine ⟨7223615985798062977466323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9631487981064083969955097 7223615985798062977466323)
    ·
      refine ⟨10835423978697094466199485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7223615985798062977466323 10835423978697094466199485)
      ·
        refine ⟨4063283992011410424824807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10835423978697094466199485 4063283992011410424824807)
        ·
          refine ⟨6094925988017115637237211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4063283992011410424824807 6094925988017115637237211)
          ·
            refine ⟨9142388982025673455855817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6094925988017115637237211 9142388982025673455855817)
            ·
              refine ⟨6856791736519255091891863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9142388982025673455855817 6856791736519255091891863)
              ·
                refine ⟨10285187604778882637837795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6856791736519255091891863 10285187604778882637837795)
                ·
                  refine ⟨15427781407168323956756693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10285187604778882637837795 15427781407168323956756693)
                  ·
                    refine ⟨361588626730507592736485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15427781407168323956756693 361588626730507592736485)
                    ·
                      rfl

theorem cell23_2112574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_2112574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112574 prefixEnd_2112574 := by exact prefixLift 2112574
  have htrace : WordTrace (prefixWord ++ tailWord_2112574) baseStart_2112574 baseEnd_2112574 := by
    simpa [prefixWord, tailWord_2112574, baseEnd_2112574] using wordTrace_append hprefix tailTrace_2112574
  have hstable : (prefixWord ++ tailWord_2112574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112574).length < 2 ^ (prefixWord ++ tailWord_2112574).sum := by decide
  have hdescent : baseEnd_2112574 < baseStart_2112574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112594 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_2112594 : Nat := 118140960795 + 2112594 * 2 ^ 59
def prefixEnd_2112594 : Nat := 4983230072969 + 3 ^ 40 * 2112594 * 2
def baseEnd_2112594 : Nat := 1084776149804612699959363

theorem tailTrace_2112594 : CollatzResearch.WordTrace tailWord_2112594 prefixEnd_2112594 1084776149804612699959363 := by
  unfold tailWord_2112594
  simp only [CollatzResearch.WordTrace]
  refine ⟨19263158327110053793842209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51368422205626810116912557 19263158327110053793842209)
  ·
    refine ⟨14447368745332540345381657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19263158327110053793842209 14447368745332540345381657)
    ·
      refine ⟨10835526558999405259036243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14447368745332540345381657 10835526558999405259036243)
      ·
        refine ⟨16253289838499107888554365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10835526558999405259036243 16253289838499107888554365)
        ·
          refine ⟨6094983689437165458207887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16253289838499107888554365 6094983689437165458207887)
          ·
            refine ⟨9142475534155748187311831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6094983689437165458207887 9142475534155748187311831)
            ·
              refine ⟨13713713301233622280967747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9142475534155748187311831 13713713301233622280967747)
              ·
                refine ⟨20570569951850433421451621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13713713301233622280967747 20570569951850433421451621)
                ·
                  refine ⟨3856981865971956266522179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20570569951850433421451621 3856981865971956266522179)
                  ·
                    refine ⟨5785472798957934399783269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3856981865971956266522179 5785472798957934399783269)
                    ·
                      refine ⟨1084776149804612699959363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5785472798957934399783269 1084776149804612699959363)
                      ·
                        rfl

theorem cell23_2112594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_2112594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112594 prefixEnd_2112594 := by exact prefixLift 2112594
  have htrace : WordTrace (prefixWord ++ tailWord_2112594) baseStart_2112594 baseEnd_2112594 := by
    simpa [prefixWord, tailWord_2112594, baseEnd_2112594] using wordTrace_append hprefix tailTrace_2112594
  have hstable : (prefixWord ++ tailWord_2112594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112594).length < 2 ^ (prefixWord ++ tailWord_2112594).sum := by decide
  have hdescent : baseEnd_2112594 < baseStart_2112594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112664 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 3, 5]
def baseStart_2112664 : Nat := 118140960795 + 2112664 * 2 ^ 59
def prefixEnd_2112664 : Nat := 4983230072969 + 3 ^ 40 * 2112664 * 2
def baseEnd_2112664 : Nat := 361604031150142475361347

theorem tailTrace_2112664 : CollatzResearch.WordTrace tailWord_2112664 prefixEnd_2112664 361604031150142475361347 := by
  unfold tailWord_2112664
  simp only [CollatzResearch.WordTrace]
  refine ⟨38527593209093308565208523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51370124278791078086944697 38527593209093308565208523)
  ·
    refine ⟨57791389813639962847812785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38527593209093308565208523 57791389813639962847812785)
    ·
      refine ⟨43343542360229972135859589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57791389813639962847812785 43343542360229972135859589)
      ·
        refine ⟨8126914192543119775473673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43343542360229972135859589 8126914192543119775473673)
        ·
          refine ⟨6095185644407339831605255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8126914192543119775473673 6095185644407339831605255)
          ·
            refine ⟨9142778466611009747407883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6095185644407339831605255 9142778466611009747407883)
            ·
              refine ⟨13714167699916514621111825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9142778466611009747407883 13714167699916514621111825)
              ·
                refine ⟨10285625774937385965833869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13714167699916514621111825 10285625774937385965833869)
                ·
                  refine ⟨3857109665601519737187701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10285625774937385965833869 3857109665601519737187701)
                  ·
                    refine ⟨361604031150142475361347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3857109665601519737187701 361604031150142475361347)
                    ·
                      rfl

theorem cell23_2112664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_2112664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112664 prefixEnd_2112664 := by exact prefixLift 2112664
  have htrace : WordTrace (prefixWord ++ tailWord_2112664) baseStart_2112664 baseEnd_2112664 := by
    simpa [prefixWord, tailWord_2112664, baseEnd_2112664] using wordTrace_append hprefix tailTrace_2112664
  have hstable : (prefixWord ++ tailWord_2112664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112664).length < 2 ^ (prefixWord ++ tailWord_2112664).sum := by decide
  have hdescent : baseEnd_2112664 < baseStart_2112664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112684 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 1, 8, 2]
def baseStart_2112684 : Nat := 118140960795 + 2112684 * 2 ^ 59
def prefixEnd_2112684 : Nat := 4983230072969 + 3 ^ 40 * 2112684 * 2
def baseEnd_2112684 : Nat := 1084822363063517347833949

theorem tailTrace_2112684 : CollatzResearch.WordTrace tailWord_2112684 prefixEnd_2112684 1084822363063517347833949 := by
  unfold tailWord_2112684
  simp only [CollatzResearch.WordTrace]
  refine ⟨38527957939057080273072553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51370610585409440364096737 38527957939057080273072553)
  ·
    refine ⟨28895968454292810204804415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38527957939057080273072553 28895968454292810204804415)
    ·
      refine ⟨43343952681439215307206623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28895968454292810204804415 43343952681439215307206623)
      ·
        refine ⟨65015929022158822960809935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43343952681439215307206623 65015929022158822960809935)
        ·
          refine ⟨97523893533238234441214903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65015929022158822960809935 97523893533238234441214903)
          ·
            refine ⟨146285840299857351661822355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97523893533238234441214903 146285840299857351661822355)
            ·
              refine ⟨219428760449786027492733533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146285840299857351661822355 219428760449786027492733533)
              ·
                refine ⟨82285785168669760309775075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 219428760449786027492733533 82285785168669760309775075)
                ·
                  refine ⟨123428677753004640464662613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82285785168669760309775075 123428677753004640464662613)
                  ·
                    refine ⟨1446429817418023130445265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 123428677753004640464662613 1446429817418023130445265)
                    ·
                      refine ⟨1084822363063517347833949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1446429817418023130445265 1084822363063517347833949)
                      ·
                        rfl

theorem cell23_2112684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 8, 2].length) (baseStart_2112684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112684 prefixEnd_2112684 := by exact prefixLift 2112684
  have htrace : WordTrace (prefixWord ++ tailWord_2112684) baseStart_2112684 baseEnd_2112684 := by
    simpa [prefixWord, tailWord_2112684, baseEnd_2112684] using wordTrace_append hprefix tailTrace_2112684
  have hstable : (prefixWord ++ tailWord_2112684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112684).length < 2 ^ (prefixWord ++ tailWord_2112684).sum := by decide
  have hdescent : baseEnd_2112684 < baseStart_2112684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112728 : List Nat := [2, 1, 2, 2, 6, 1, 1, 1, 1, 6]
def baseStart_2112728 : Nat := 118140960795 + 2112728 * 2 ^ 59
def prefixEnd_2112728 : Nat := 4983230072969 + 3 ^ 40 * 2112728 * 2
def baseEnd_2112728 : Nat := 361614985404105058561249

theorem tailTrace_2112728 : CollatzResearch.WordTrace tailWord_2112728 prefixEnd_2112728 361614985404105058561249 := by
  unfold tailWord_2112728
  simp only [CollatzResearch.WordTrace]
  refine ⟨38528760344977378030373419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51371680459969837373831225 38528760344977378030373419)
  ·
    refine ⟨57793140517466067045560129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38528760344977378030373419 57793140517466067045560129)
    ·
      refine ⟨43344855388099550284170097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57793140517466067045560129 43344855388099550284170097)
      ·
        refine ⟨32508641541074662713127573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43344855388099550284170097 32508641541074662713127573)
        ·
          refine ⟨1523842572237874814677855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32508641541074662713127573 1523842572237874814677855)
          ·
            refine ⟨2285763858356812222016783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1523842572237874814677855 2285763858356812222016783)
            ·
              refine ⟨3428645787535218333025175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2285763858356812222016783 3428645787535218333025175)
              ·
                refine ⟨5142968681302827499537763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3428645787535218333025175 5142968681302827499537763)
                ·
                  refine ⟨7714453021954241249306645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5142968681302827499537763 7714453021954241249306645)
                  ·
                    refine ⟨361614985404105058561249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7714453021954241249306645 361614985404105058561249)
                    ·
                      rfl

theorem cell23_2112728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 1, 6].length) (baseStart_2112728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112728 prefixEnd_2112728 := by exact prefixLift 2112728
  have htrace : WordTrace (prefixWord ++ tailWord_2112728) baseStart_2112728 baseEnd_2112728 := by
    simpa [prefixWord, tailWord_2112728, baseEnd_2112728] using wordTrace_append hprefix tailTrace_2112728
  have hstable : (prefixWord ++ tailWord_2112728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112728).length < 2 ^ (prefixWord ++ tailWord_2112728).sum := by decide
  have hdescent : baseEnd_2112728 < baseStart_2112728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112808 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 3, 4, 2]
def baseStart_2112808 : Nat := 118140960795 + 2112808 * 2 ^ 59
def prefixEnd_2112808 : Nat := 4983230072969 + 3 ^ 40 * 2112808 * 2
def baseEnd_2112808 : Nat := 1084886034664674862683379

theorem tailTrace_2112808 : CollatzResearch.WordTrace tailWord_2112808 prefixEnd_2112808 1084886034664674862683379 := by
  unfold tailWord_2112808
  simp only [CollatzResearch.WordTrace]
  refine ⟨38530219264832464861829539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51373625686443286482439385 38530219264832464861829539)
  ·
    refine ⟨57795328897248697292744309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38530219264832464861829539 57795328897248697292744309)
    ·
      refine ⟨5418312084117065371194779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57795328897248697292744309 5418312084117065371194779)
      ·
        refine ⟨8127468126175598056792169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5418312084117065371194779 8127468126175598056792169)
        ·
          refine ⟨6095601094631698542594127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8127468126175598056792169 6095601094631698542594127)
          ·
            refine ⟨9143401641947547813891191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6095601094631698542594127 9143401641947547813891191)
            ·
              refine ⟨13715102462921321720836787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9143401641947547813891191 13715102462921321720836787)
              ·
                refine ⟨20572653694381982581255181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13715102462921321720836787 20572653694381982581255181)
                ·
                  refine ⟨7714745135393243467970693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20572653694381982581255181 7714745135393243467970693)
                  ·
                    refine ⟨1446514712886233150244505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7714745135393243467970693 1446514712886233150244505)
                    ·
                      refine ⟨1084886034664674862683379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1446514712886233150244505 1084886034664674862683379)
                      ·
                        rfl

theorem cell23_2112808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_2112808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112808 prefixEnd_2112808 := by exact prefixLift 2112808
  have htrace : WordTrace (prefixWord ++ tailWord_2112808) baseStart_2112808 baseEnd_2112808 := by
    simpa [prefixWord, tailWord_2112808, baseEnd_2112808] using wordTrace_append hprefix tailTrace_2112808
  have hstable : (prefixWord ++ tailWord_2112808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112808).length < 2 ^ (prefixWord ++ tailWord_2112808).sum := by decide
  have hdescent : baseEnd_2112808 < baseStart_2112808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112851 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 2, 5, 2]
def baseStart_2112851 : Nat := 118140960795 + 2112851 * 2 ^ 59
def prefixEnd_2112851 : Nat := 4983230072969 + 3 ^ 40 * 2112851 * 2
def baseEnd_2112851 : Nat := 1084908114332818194445681

theorem tailTrace_2112851 : CollatzResearch.WordTrace tailWord_2112851 prefixEnd_2112851 1084908114332818194445681 := by
  unfold tailWord_2112851
  simp only [CollatzResearch.WordTrace]
  refine ⟨77062006868509148067474407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51374671245672765378316271 77062006868509148067474407)
  ·
    refine ⟨115593010302763722101211611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77062006868509148067474407 115593010302763722101211611)
    ·
      refine ⟨173389515454145583151817417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115593010302763722101211611 173389515454145583151817417)
      ·
        refine ⟨130042136590609187363863063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173389515454145583151817417 130042136590609187363863063)
        ·
          refine ⟨195063204885913781045794595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130042136590609187363863063 195063204885913781045794595)
          ·
            refine ⟨292594807328870671568691893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195063204885913781045794595 292594807328870671568691893)
            ·
              refine ⟨27430763187081625459564865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 292594807328870671568691893 27430763187081625459564865)
              ·
                refine ⟨20573072390311219094673649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27430763187081625459564865 20573072390311219094673649)
                ·
                  refine ⟨15429804292733414321005237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20573072390311219094673649 15429804292733414321005237)
                  ·
                    refine ⟨1446544152443757592594241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15429804292733414321005237 1446544152443757592594241)
                    ·
                      refine ⟨1084908114332818194445681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1446544152443757592594241 1084908114332818194445681)
                      ·
                        rfl

theorem cell23_2112851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 5, 2].length) (baseStart_2112851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112851 prefixEnd_2112851 := by exact prefixLift 2112851
  have htrace : WordTrace (prefixWord ++ tailWord_2112851) baseStart_2112851 baseEnd_2112851 := by
    simpa [prefixWord, tailWord_2112851, baseEnd_2112851] using wordTrace_append hprefix tailTrace_2112851
  have hstable : (prefixWord ++ tailWord_2112851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112851).length < 2 ^ (prefixWord ++ tailWord_2112851).sum := by decide
  have hdescent : baseEnd_2112851 < baseStart_2112851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112881 : List Nat := [1, 2, 2, 2, 1, 2, 2, 4, 2, 1, 4]
def baseStart_2112881 : Nat := 118140960795 + 2112881 * 2 ^ 59
def prefixEnd_2112881 : Nat := 4983230072969 + 3 ^ 40 * 2112881 * 2
def baseEnd_2112881 : Nat := 1084923518752453077070543

theorem tailTrace_2112881 : CollatzResearch.WordTrace tailWord_2112881 prefixEnd_2112881 1084923518752453077070543 := by
  unfold tailWord_2112881
  simp only [CollatzResearch.WordTrace]
  refine ⟨77063101058400463191066497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51375400705600308794044331 77063101058400463191066497)
  ·
    refine ⟨57797325793800347393299873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77063101058400463191066497 57797325793800347393299873)
    ·
      refine ⟨43347994345350260544974905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57797325793800347393299873 43347994345350260544974905)
      ·
        refine ⟨32510995759012695408731179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43347994345350260544974905 32510995759012695408731179)
        ·
          refine ⟨48766493638519043113096769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32510995759012695408731179 48766493638519043113096769)
          ·
            refine ⟨36574870228889282334822577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48766493638519043113096769 36574870228889282334822577)
            ·
              refine ⟨27431152671666961751116933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36574870228889282334822577 27431152671666961751116933)
              ·
                refine ⟨5143341125937555328334425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27431152671666961751116933 5143341125937555328334425)
                ·
                  refine ⟨3857505844453166496250819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5143341125937555328334425 3857505844453166496250819)
                  ·
                    refine ⟨5786258766679749744376229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3857505844453166496250819 5786258766679749744376229)
                    ·
                      refine ⟨1084923518752453077070543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5786258766679749744376229 1084923518752453077070543)
                      ·
                        rfl

theorem cell23_2112881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_2112881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112881 prefixEnd_2112881 := by exact prefixLift 2112881
  have htrace : WordTrace (prefixWord ++ tailWord_2112881) baseStart_2112881 baseEnd_2112881 := by
    simpa [prefixWord, tailWord_2112881, baseEnd_2112881] using wordTrace_append hprefix tailTrace_2112881
  have hstable : (prefixWord ++ tailWord_2112881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112881).length < 2 ^ (prefixWord ++ tailWord_2112881).sum := by decide
  have hdescent : baseEnd_2112881 < baseStart_2112881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112901 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 1, 4, 3]
def baseStart_2112901 : Nat := 118140960795 + 2112901 * 2 ^ 59
def prefixEnd_2112901 : Nat := 4983230072969 + 3 ^ 40 * 2112901 * 2
def baseEnd_2112901 : Nat := 1084933788365542998820451

theorem tailTrace_2112901 : CollatzResearch.WordTrace tailWord_2112901 prefixEnd_2112901 1084933788365542998820451 := by
  unfold tailWord_2112901
  simp only [CollatzResearch.WordTrace]
  refine ⟨77063830518328006606794557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51375887012218671071196371 77063830518328006606794557)
  ·
    refine ⟨28898936444373002477547959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77063830518328006606794557 28898936444373002477547959)
    ·
      refine ⟨43348404666559503716321939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28898936444373002477547959 43348404666559503716321939)
      ·
        refine ⟨65022606999839255574482909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43348404666559503716321939 65022606999839255574482909)
        ·
          refine ⟨24383477624939720840431091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65022606999839255574482909 24383477624939720840431091)
          ·
            refine ⟨36575216437409581260646637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24383477624939720840431091 36575216437409581260646637)
            ·
              refine ⟨13715706164028592972742489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36575216437409581260646637 13715706164028592972742489)
              ·
                refine ⟨10286779623021444729556867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13715706164028592972742489 10286779623021444729556867)
                ·
                  refine ⟨15430169434532167094335301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10286779623021444729556867 15430169434532167094335301)
                  ·
                    refine ⟨2893156768974781330187869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15430169434532167094335301 2893156768974781330187869)
                    ·
                      refine ⟨1084933788365542998820451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2893156768974781330187869 1084933788365542998820451)
                      ·
                        rfl

theorem cell23_2112901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 4, 3].length) (baseStart_2112901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112901 prefixEnd_2112901 := by exact prefixLift 2112901
  have htrace : WordTrace (prefixWord ++ tailWord_2112901) baseStart_2112901 baseEnd_2112901 := by
    simpa [prefixWord, tailWord_2112901, baseEnd_2112901] using wordTrace_append hprefix tailTrace_2112901
  have hstable : (prefixWord ++ tailWord_2112901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112901).length < 2 ^ (prefixWord ++ tailWord_2112901).sum := by decide
  have hdescent : baseEnd_2112901 < baseStart_2112901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112951 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 3, 5]
def baseStart_2112951 : Nat := 118140960795 + 2112951 * 2 ^ 59
def prefixEnd_2112951 : Nat := 4983230072969 + 3 ^ 40 * 2112951 * 2
def baseEnd_2112951 : Nat := 361653154132755934398407

theorem tailTrace_2112951 : CollatzResearch.WordTrace tailWord_2112951 prefixEnd_2112951 361653154132755934398407 := by
  unfold tailWord_2112951
  simp only [CollatzResearch.WordTrace]
  refine ⟨77065654168146865146114707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51377102778764576764076471 77065654168146865146114707)
  ·
    refine ⟨115598481252220297719172061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77065654168146865146114707 115598481252220297719172061)
    ·
      refine ⟨43349430469582611644689523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115598481252220297719172061 43349430469582611644689523)
      ·
        refine ⟨65024145704373917467034285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43349430469582611644689523 65024145704373917467034285)
        ·
          refine ⟨24384054639140219050137857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65024145704373917467034285 24384054639140219050137857)
          ·
            refine ⟨18288040979355164287603393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24384054639140219050137857 18288040979355164287603393)
            ·
              refine ⟨13716030734516373215702545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18288040979355164287603393 13716030734516373215702545)
              ·
                refine ⟨10287023050887279911776909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13716030734516373215702545 10287023050887279911776909)
                ·
                  refine ⟨3857633644082729966916341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10287023050887279911776909 3857633644082729966916341)
                  ·
                    refine ⟨361653154132755934398407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3857633644082729966916341 361653154132755934398407)
                    ·
                      rfl

theorem cell23_2112951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_2112951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112951 prefixEnd_2112951 := by exact prefixLift 2112951
  have htrace : WordTrace (prefixWord ++ tailWord_2112951) baseStart_2112951 baseEnd_2112951 := by
    simpa [prefixWord, tailWord_2112951, baseEnd_2112951] using wordTrace_append hprefix tailTrace_2112951
  have hstable : (prefixWord ++ tailWord_2112951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112951).length < 2 ^ (prefixWord ++ tailWord_2112951).sum := by decide
  have hdescent : baseEnd_2112951 < baseStart_2112951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112985 : List Nat := [1, 2, 1, 2, 4, 3, 3, 1, 1, 5]
def baseStart_2112985 : Nat := 118140960795 + 2112985 * 2 ^ 59
def prefixEnd_2112985 : Nat := 4983230072969 + 3 ^ 40 * 2112985 * 2
def baseEnd_2112985 : Nat := 361658973580173556723355

theorem tailTrace_2112985 : CollatzResearch.WordTrace tailWord_2112985 prefixEnd_2112985 361658973580173556723355 := by
  unfold tailWord_2112985
  simp only [CollatzResearch.WordTrace]
  refine ⟨77066894250023688952852409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51377929500015792635234939 77066894250023688952852409)
  ·
    refine ⟨57800170687517766714639307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77066894250023688952852409 57800170687517766714639307)
    ·
      refine ⟨86700256031276650071958961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57800170687517766714639307 86700256031276650071958961)
      ·
        refine ⟨65025192023457487553969221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86700256031276650071958961 65025192023457487553969221)
        ·
          refine ⟨12192223504398278916369229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65025192023457487553969221 12192223504398278916369229)
          ·
            refine ⟨4572083814149354593638461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12192223504398278916369229 4572083814149354593638461)
            ·
              refine ⟨1714531430306007972614423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4572083814149354593638461 1714531430306007972614423)
              ·
                refine ⟨2571797145459011958921635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1714531430306007972614423 2571797145459011958921635)
                ·
                  refine ⟨3857695718188517938382453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2571797145459011958921635 3857695718188517938382453)
                  ·
                    refine ⟨361658973580173556723355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3857695718188517938382453 361658973580173556723355)
                    ·
                      rfl

theorem cell23_2112985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 1, 5].length) (baseStart_2112985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112985 prefixEnd_2112985 := by exact prefixLift 2112985
  have htrace : WordTrace (prefixWord ++ tailWord_2112985) baseStart_2112985 baseEnd_2112985 := by
    simpa [prefixWord, tailWord_2112985, baseEnd_2112985] using wordTrace_append hprefix tailTrace_2112985
  have hstable : (prefixWord ++ tailWord_2112985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112985).length < 2 ^ (prefixWord ++ tailWord_2112985).sum := by decide
  have hdescent : baseEnd_2112985 < baseStart_2112985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112999 : List Nat := [1, 1, 5, 2, 1, 2, 4, 2, 1, 1, 3]
def baseStart_2112999 : Nat := 118140960795 + 2112999 * 2 ^ 59
def prefixEnd_2112999 : Nat := 4983230072969 + 3 ^ 40 * 2112999 * 2
def baseEnd_2112999 : Nat := 1084984109469683615395001

theorem tailTrace_2112999 : CollatzResearch.WordTrace tailWord_2112999 prefixEnd_2112999 1084984109469683615395001 := by
  unfold tailWord_2112999
  simp only [CollatzResearch.WordTrace]
  refine ⟨77067404871972969343862051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51378269914648646229241367 77067404871972969343862051)
  ·
    refine ⟨115601107307959454015793077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77067404871972969343862051 115601107307959454015793077)
    ·
      refine ⟨10837603810121198813980601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115601107307959454015793077 10837603810121198813980601)
      ·
        refine ⟨8128202857590899110485451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10837603810121198813980601 8128202857590899110485451)
        ·
          refine ⟨12192304286386348665728177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8128202857590899110485451 12192304286386348665728177)
          ·
            refine ⟨9144228214789761499296133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12192304286386348665728177 9144228214789761499296133)
            ·
              refine ⟨1714542790273080281118025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9144228214789761499296133 1714542790273080281118025)
              ·
                refine ⟨1285907092704810210838519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1714542790273080281118025 1285907092704810210838519)
                ·
                  refine ⟨1928860639057215316257779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1285907092704810210838519 1928860639057215316257779)
                  ·
                    refine ⟨2893290958585822974386669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1928860639057215316257779 2893290958585822974386669)
                    ·
                      refine ⟨1084984109469683615395001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2893290958585822974386669 1084984109469683615395001)
                      ·
                        rfl

theorem cell23_2112999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_2112999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112999 prefixEnd_2112999 := by exact prefixLift 2112999
  have htrace : WordTrace (prefixWord ++ tailWord_2112999) baseStart_2112999 baseEnd_2112999 := by
    simpa [prefixWord, tailWord_2112999, baseEnd_2112999] using wordTrace_append hprefix tailTrace_2112999
  have hstable : (prefixWord ++ tailWord_2112999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112999).length < 2 ^ (prefixWord ++ tailWord_2112999).sum := by decide
  have hdescent : baseEnd_2112999 < baseStart_2112999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113008 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 3]
def baseStart_2113008 : Nat := 118140960795 + 2113008 * 2 ^ 59
def prefixEnd_2113008 : Nat := 4983230072969 + 3 ^ 40 * 2113008 * 2
def baseEnd_2113008 : Nat := 1084988730795574080182459

theorem tailTrace_2113008 : CollatzResearch.WordTrace tailWord_2113008 prefixEnd_2113008 1084988730795574080182459 := by
  unfold tailWord_2113008
  simp only [CollatzResearch.WordTrace]
  refine ⟨38533866564470181940469839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51378488752626909253959785 38533866564470181940469839)
  ·
    refine ⟨57800799846705272910704759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38533866564470181940469839 57800799846705272910704759)
    ·
      refine ⟨86701199770057909366057139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57800799846705272910704759 86701199770057909366057139)
      ·
        refine ⟨130051799655086864049085709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86701199770057909366057139 130051799655086864049085709)
        ·
          refine ⟨48769424870657574018407141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130051799655086864049085709 48769424870657574018407141)
          ·
            refine ⟨9144267163248295128451339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48769424870657574018407141 9144267163248295128451339)
            ·
              refine ⟨13716400744872442692677009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9144267163248295128451339 13716400744872442692677009)
              ·
                refine ⟨10287300558654332019507757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13716400744872442692677009 10287300558654332019507757)
                ·
                  refine ⟨3857737709495374507315409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10287300558654332019507757 3857737709495374507315409)
                  ·
                    refine ⟨2893303282121530880486557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3857737709495374507315409 2893303282121530880486557)
                    ·
                      refine ⟨1084988730795574080182459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2893303282121530880486557 1084988730795574080182459)
                      ·
                        rfl

theorem cell23_2113008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 3].length) (baseStart_2113008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113008 prefixEnd_2113008 := by exact prefixLift 2113008
  have htrace : WordTrace (prefixWord ++ tailWord_2113008) baseStart_2113008 baseEnd_2113008 := by
    simpa [prefixWord, tailWord_2113008, baseEnd_2113008] using wordTrace_append hprefix tailTrace_2113008
  have hstable : (prefixWord ++ tailWord_2113008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113008).length < 2 ^ (prefixWord ++ tailWord_2113008).sum := by decide
  have hdescent : baseEnd_2113008 < baseStart_2113008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113018 : List Nat := [3, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4]
def baseStart_2113018 : Nat := 118140960795 + 2113018 * 2 ^ 59
def prefixEnd_2113018 : Nat := 4983230072969 + 3 ^ 40 * 2113018 * 2
def baseEnd_2113018 : Nat := 1084993865602119041057413

theorem tailTrace_2113018 : CollatzResearch.WordTrace tailWord_2113018 prefixEnd_2113018 1084993865602119041057413 := by
  unfold tailWord_2113018
  simp only [CollatzResearch.WordTrace]
  refine ⟨19267024464726033897200927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51378731905936090392535805 19267024464726033897200927)
  ·
    refine ⟨28900536697089050845801391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19267024464726033897200927 28900536697089050845801391)
    ·
      refine ⟨43350805045633576268702087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28900536697089050845801391 43350805045633576268702087)
      ·
        refine ⟨65026207568450364403053131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43350805045633576268702087 65026207568450364403053131)
        ·
          refine ⟨97539311352675546604579697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65026207568450364403053131 97539311352675546604579697)
          ·
            refine ⟨73154483514506659953434773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97539311352675546604579697 73154483514506659953434773)
            ·
              refine ⟨3429116414742499685317255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73154483514506659953434773 3429116414742499685317255)
              ·
                refine ⟨5143674622113749527975883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3429116414742499685317255 5143674622113749527975883)
                ·
                  refine ⟨7715511933170624291963825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5143674622113749527975883 7715511933170624291963825)
                  ·
                    refine ⟨5786633949877968218972869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7715511933170624291963825 5786633949877968218972869)
                    ·
                      refine ⟨1084993865602119041057413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5786633949877968218972869 1084993865602119041057413)
                      ·
                        rfl

theorem cell23_2113018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4].length) (baseStart_2113018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113018 prefixEnd_2113018 := by exact prefixLift 2113018
  have htrace : WordTrace (prefixWord ++ tailWord_2113018) baseStart_2113018 baseEnd_2113018 := by
    simpa [prefixWord, tailWord_2113018, baseEnd_2113018] using wordTrace_append hprefix tailTrace_2113018
  have hstable : (prefixWord ++ tailWord_2113018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113018).length < 2 ^ (prefixWord ++ tailWord_2113018).sum := by decide
  have hdescent : baseEnd_2113018 < baseStart_2113018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113082 : List Nat := [3, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2]
def baseStart_2113082 : Nat := 118140960795 + 2113082 * 2 ^ 59
def prefixEnd_2113082 : Nat := 4983230072969 + 3 ^ 40 * 2113082 * 2
def baseEnd_2113082 : Nat := 1085026728364006790657119

theorem tailTrace_2113082 : CollatzResearch.WordTrace tailWord_2113082 prefixEnd_2113082 1085026728364006790657119 := by
  unfold tailWord_2113082
  simp only [CollatzResearch.WordTrace]
  refine ⟨19267608032668068629783375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51380288087114849679422333 19267608032668068629783375)
  ·
    refine ⟨28901412049002102944675063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19267608032668068629783375 28901412049002102944675063)
    ·
      refine ⟨43352118073503154417012595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28901412049002102944675063 43352118073503154417012595)
      ·
        refine ⟨65028177110254731625518893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43352118073503154417012595 65028177110254731625518893)
        ·
          refine ⟨24385566416345524359569585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65028177110254731625518893 24385566416345524359569585)
          ·
            refine ⟨18289174812259143269677189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24385566416345524359569585 18289174812259143269677189)
            ·
              refine ⟨3429220277298589363064473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18289174812259143269677189 3429220277298589363064473)
              ·
                refine ⟨2571915207973942022298355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3429220277298589363064473 2571915207973942022298355)
                ·
                  refine ⟨3857872811960913033447533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2571915207973942022298355 3857872811960913033447533)
                  ·
                    refine ⟨1446702304485342387542825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3857872811960913033447533 1446702304485342387542825)
                    ·
                      refine ⟨1085026728364006790657119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1446702304485342387542825 1085026728364006790657119)
                      ·
                        rfl

theorem cell23_2113082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2].length) (baseStart_2113082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113082 prefixEnd_2113082 := by exact prefixLift 2113082
  have htrace : WordTrace (prefixWord ++ tailWord_2113082) baseStart_2113082 baseEnd_2113082 := by
    simpa [prefixWord, tailWord_2113082, baseEnd_2113082] using wordTrace_append hprefix tailTrace_2113082
  have hstable : (prefixWord ++ tailWord_2113082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113082).length < 2 ^ (prefixWord ++ tailWord_2113082).sum := by decide
  have hdescent : baseEnd_2113082 < baseStart_2113082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113098 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 2, 1, 5]
def baseStart_2113098 : Nat := 118140960795 + 2113098 * 2 ^ 59
def prefixEnd_2113098 : Nat := 4983230072969 + 3 ^ 40 * 2113098 * 2
def baseEnd_2113098 : Nat := 1085034944054478728057045

theorem tailTrace_2113098 : CollatzResearch.WordTrace tailWord_2113098 prefixEnd_2113098 1085034944054478728057045 := by
  unfold tailWord_2113098
  simp only [CollatzResearch.WordTrace]
  refine ⟨19267753924653577312928987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51380677132409539501143965 19267753924653577312928987)
  ·
    refine ⟨28901630886980365969393481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19267753924653577312928987 28901630886980365969393481)
    ·
      refine ⟨21676223165235274477045111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28901630886980365969393481 21676223165235274477045111)
      ·
        refine ⟨32514334747852911715567667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21676223165235274477045111 32514334747852911715567667)
        ·
          refine ⟨48771502121779367573351501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32514334747852911715567667 48771502121779367573351501)
          ·
            refine ⟨18289313295667262840006813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48771502121779367573351501 18289313295667262840006813)
            ·
              refine ⟨6858492485875223565002555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18289313295667262840006813 6858492485875223565002555)
              ·
                refine ⟨10287738728812835347503833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6858492485875223565002555 10287738728812835347503833)
                ·
                  refine ⟨7715804046609626510627875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10287738728812835347503833 7715804046609626510627875)
                  ·
                    refine ⟨11573706069914439765941813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7715804046609626510627875 11573706069914439765941813)
                    ·
                      refine ⟨1085034944054478728057045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11573706069914439765941813 1085034944054478728057045)
                      ·
                        rfl

theorem cell23_2113098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_2113098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113098 prefixEnd_2113098 := by exact prefixLift 2113098
  have htrace : WordTrace (prefixWord ++ tailWord_2113098) baseStart_2113098 baseEnd_2113098 := by
    simpa [prefixWord, tailWord_2113098, baseEnd_2113098] using wordTrace_append hprefix tailTrace_2113098
  have hstable : (prefixWord ++ tailWord_2113098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113098).length < 2 ^ (prefixWord ++ tailWord_2113098).sum := by decide
  have hdescent : baseEnd_2113098 < baseStart_2113098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113112 : List Nat := [2, 1, 2, 2, 1, 2, 1, 6, 2, 2, 2]
def baseStart_2113112 : Nat := 118140960795 + 2113112 * 2 ^ 59
def prefixEnd_2113112 : Nat := 4983230072969 + 3 ^ 40 * 2113112 * 2
def baseEnd_2113112 : Nat := 1085042132783641673281981

theorem tailTrace_2113112 : CollatzResearch.WordTrace tailWord_2113112 prefixEnd_2113112 1085042132783641673281981 := by
  unfold tailWord_2113112
  simp only [CollatzResearch.WordTrace]
  refine ⟨38535763160281794821362795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51381017547042393095150393 38535763160281794821362795)
  ·
    refine ⟨57803644740422692232044193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38535763160281794821362795 57803644740422692232044193)
    ·
      refine ⟨43352733555317019174033145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57803644740422692232044193 43352733555317019174033145)
      ·
        refine ⟨32514550166487764380524859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43352733555317019174033145 32514550166487764380524859)
        ·
          refine ⟨48771825249731646570787289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32514550166487764380524859 48771825249731646570787289)
          ·
            refine ⟨36578868937298734928090467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48771825249731646570787289 36578868937298734928090467)
            ·
              refine ⟨54868303405948102392135701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36578868937298734928090467 54868303405948102392135701)
              ·
                refine ⟨2571951722153817299631361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54868303405948102392135701 2571951722153817299631361)
                ·
                  refine ⟨1928963791615362974723521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2571951722153817299631361 1928963791615362974723521)
                  ·
                    refine ⟨1446722843711522231042641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1928963791615362974723521 1446722843711522231042641)
                    ·
                      refine ⟨1085042132783641673281981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1446722843711522231042641 1085042132783641673281981)
                      ·
                        rfl

theorem cell23_2113112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 2, 2, 2].length) (baseStart_2113112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113112 prefixEnd_2113112 := by exact prefixLift 2113112
  have htrace : WordTrace (prefixWord ++ tailWord_2113112) baseStart_2113112 baseEnd_2113112 := by
    simpa [prefixWord, tailWord_2113112, baseEnd_2113112] using wordTrace_append hprefix tailTrace_2113112
  have hstable : (prefixWord ++ tailWord_2113112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113112).length < 2 ^ (prefixWord ++ tailWord_2113112).sum := by decide
  have hdescent : baseEnd_2113112 < baseStart_2113112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113129 : List Nat := [1, 2, 1, 1, 1, 4, 6, 1, 2, 2, 2]
def baseStart_2113129 : Nat := 118140960795 + 2113129 * 2 ^ 59
def prefixEnd_2113129 : Nat := 4983230072969 + 3 ^ 40 * 2113129 * 2
def baseEnd_2113129 : Nat := 1085050861954768106769403

theorem tailTrace_2113129 : CollatzResearch.WordTrace tailWord_2113129 prefixEnd_2113129 1085050861954768106769403 := by
  unfold tailWord_2113129
  simp only [CollatzResearch.WordTrace]
  refine ⟨77072146361502001546094441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51381430907668001030729627 77072146361502001546094441)
  ·
    refine ⟨57804109771126501159570831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77072146361502001546094441 57804109771126501159570831)
    ·
      refine ⟨86706164656689751739356247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57804109771126501159570831 86706164656689751739356247)
      ·
        refine ⟨130059246985034627609034371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86706164656689751739356247 130059246985034627609034371)
        ·
          refine ⟨195088870477551941413551557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130059246985034627609034371 195088870477551941413551557)
          ·
            refine ⟨36579163214540989015040917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 195088870477551941413551557 36579163214540989015040917)
            ·
              refine ⟨1714648275681608860080043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36579163214540989015040917 1714648275681608860080043)
              ·
                refine ⟨2571972413522413290120065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1714648275681608860080043 2571972413522413290120065)
                ·
                  refine ⟨1928979310141809967590049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2571972413522413290120065 1928979310141809967590049)
                  ·
                    refine ⟨1446734482606357475692537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1928979310141809967590049 1446734482606357475692537)
                    ·
                      refine ⟨1085050861954768106769403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1446734482606357475692537 1085050861954768106769403)
                      ·
                        rfl

theorem cell23_2113129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 2, 2, 2].length) (baseStart_2113129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113129 prefixEnd_2113129 := by exact prefixLift 2113129
  have htrace : WordTrace (prefixWord ++ tailWord_2113129) baseStart_2113129 baseEnd_2113129 := by
    simpa [prefixWord, tailWord_2113129, baseEnd_2113129] using wordTrace_append hprefix tailTrace_2113129
  have hstable : (prefixWord ++ tailWord_2113129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113129).length < 2 ^ (prefixWord ++ tailWord_2113129).sum := by decide
  have hdescent : baseEnd_2113129 < baseStart_2113129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113229 : List Nat := [1, 6, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_2113229 : Nat := 118140960795 + 2113229 * 2 ^ 59
def prefixEnd_2113229 : Nat := 4983230072969 + 3 ^ 40 * 2113229 * 2
def baseEnd_2113229 : Nat := 361700736673405905172981

theorem tailTrace_2113229 : CollatzResearch.WordTrace tailWord_2113229 prefixEnd_2113229 361700736673405905172981 := by
  unfold tailWord_2113229
  simp only [CollatzResearch.WordTrace]
  refine ⟨77075793661139718624734741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51383862440759812416489827 77075793661139718624734741)
  ·
    refine ⟨3612927827865924310534441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 77075793661139718624734741 3612927827865924310534441)
    ·
      refine ⟨2709695870899443232900831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3612927827865924310534441 2709695870899443232900831)
      ·
        refine ⟨4064543806349164849351247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2709695870899443232900831 4064543806349164849351247)
        ·
          refine ⟨6096815709523747274026871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4064543806349164849351247 6096815709523747274026871)
          ·
            refine ⟨9145223564285620911040307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6096815709523747274026871 9145223564285620911040307)
            ·
              refine ⟨13717835346428431366560461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9145223564285620911040307 13717835346428431366560461)
              ·
                refine ⟨5144188254910661762460173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13717835346428431366560461 5144188254910661762460173)
                ·
                  refine ⟨1929070595591498160922565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5144188254910661762460173 1929070595591498160922565)
                  ·
                    refine ⟨361700736673405905172981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1929070595591498160922565 361700736673405905172981)
                    ·
                      rfl

theorem cell23_2113229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_2113229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113229 prefixEnd_2113229 := by exact prefixLift 2113229
  have htrace : WordTrace (prefixWord ++ tailWord_2113229) baseStart_2113229 baseEnd_2113229 := by
    simpa [prefixWord, tailWord_2113229, baseEnd_2113229] using wordTrace_append hprefix tailTrace_2113229
  have hstable : (prefixWord ++ tailWord_2113229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113229).length < 2 ^ (prefixWord ++ tailWord_2113229).sum := by decide
  have hdescent : baseEnd_2113229 < baseStart_2113229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113242 : List Nat := [3, 1, 1, 2, 2, 4, 3, 1, 6]
def baseStart_2113242 : Nat := 118140960795 + 2113242 * 2 ^ 59
def prefixEnd_2113242 : Nat := 4983230072969 + 3 ^ 40 * 2113242 * 2
def baseEnd_2113242 : Nat := 120567653918747351628487

theorem tailTrace_2113242 : CollatzResearch.WordTrace tailWord_2113242 prefixEnd_2113242 120567653918747351628487 := by
  unfold tailWord_2113242
  simp only [CollatzResearch.WordTrace]
  refine ⟨19269066952523155461239495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51384178540061747896638653 19269066952523155461239495)
  ·
    refine ⟨28903600428784733191859243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19269066952523155461239495 28903600428784733191859243)
    ·
      refine ⟨43355400643177099787788865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28903600428784733191859243 43355400643177099787788865)
      ·
        refine ⟨32516550482382824840841649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43355400643177099787788865 32516550482382824840841649)
        ·
          refine ⟨24387412861787118630631237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32516550482382824840841649 24387412861787118630631237)
          ·
            refine ⟨4572639911585084743243357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24387412861787118630631237 4572639911585084743243357)
            ·
              refine ⟨1714739966844406778716259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4572639911585084743243357 1714739966844406778716259)
              ·
                refine ⟨2572109950266610168074389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1714739966844406778716259 2572109950266610168074389)
                ·
                  refine ⟨120567653918747351628487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2572109950266610168074389 120567653918747351628487)
                  ·
                    rfl

theorem cell23_2113242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 6].length) (baseStart_2113242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113242 prefixEnd_2113242 := by exact prefixLift 2113242
  have htrace : WordTrace (prefixWord ++ tailWord_2113242) baseStart_2113242 baseEnd_2113242 := by
    simpa [prefixWord, tailWord_2113242, baseEnd_2113242] using wordTrace_append hprefix tailTrace_2113242
  have hstable : (prefixWord ++ tailWord_2113242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113242).length < 2 ^ (prefixWord ++ tailWord_2113242).sum := by decide
  have hdescent : baseEnd_2113242 < baseStart_2113242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113248 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 7]
def baseStart_2113248 : Nat := 118140960795 + 2113248 * 2 ^ 59
def prefixEnd_2113248 : Nat := 4983230072969 + 3 ^ 40 * 2113248 * 2
def baseEnd_2113248 : Nat := 1085111966152653141181355

theorem tailTrace_2113248 : CollatzResearch.WordTrace tailWord_2113248 prefixEnd_2113248 1085111966152653141181355 := by
  unfold tailWord_2113248
  simp only [CollatzResearch.WordTrace]
  refine ⟨38538243324035442434838199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51384324432047256579784265 38538243324035442434838199)
  ·
    refine ⟨57807364986053163652257299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38538243324035442434838199 57807364986053163652257299)
    ·
      refine ⟨86711047479079745478385949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57807364986053163652257299 86711047479079745478385949)
      ·
        refine ⟨32516642804654904554394731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86711047479079745478385949 32516642804654904554394731)
        ·
          refine ⟨48774964206982356831592097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32516642804654904554394731 48774964206982356831592097)
          ·
            refine ⟨36581223155236767623694073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48774964206982356831592097 36581223155236767623694073)
            ·
              refine ⟨27435917366427575717770555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36581223155236767623694073 27435917366427575717770555)
              ·
                refine ⟨41153876049641363576655833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27435917366427575717770555 41153876049641363576655833)
                ·
                  refine ⟨30865407037231022682491875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41153876049641363576655833 30865407037231022682491875)
                  ·
                    refine ⟨46298110555846534023737813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30865407037231022682491875 46298110555846534023737813)
                    ·
                      refine ⟨1085111966152653141181355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46298110555846534023737813 1085111966152653141181355)
                      ·
                        rfl

theorem cell23_2113248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_2113248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113248 prefixEnd_2113248 := by exact prefixLift 2113248
  have htrace : WordTrace (prefixWord ++ tailWord_2113248) baseStart_2113248 baseEnd_2113248 := by
    simpa [prefixWord, tailWord_2113248, baseEnd_2113248] using wordTrace_append hprefix tailTrace_2113248
  have hstable : (prefixWord ++ tailWord_2113248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113248).length < 2 ^ (prefixWord ++ tailWord_2113248).sum := by decide
  have hdescent : baseEnd_2113248 < baseStart_2113248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113252 : List Nat := [2, 3, 1, 1, 1, 3, 1, 4, 3, 1, 3]
def baseStart_2113252 : Nat := 118140960795 + 2113252 * 2 ^ 59
def prefixEnd_2113252 : Nat := 4983230072969 + 3 ^ 40 * 2113252 * 2
def baseEnd_2113252 : Nat := 1085114020075271125531337

theorem tailTrace_2113252 : CollatzResearch.WordTrace tailWord_2113252 prefixEnd_2113252 1085114020075271125531337 := by
  unfold tailWord_2113252
  simp only [CollatzResearch.WordTrace]
  refine ⟨38538316270028196776411005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51384421693370929035214673 38538316270028196776411005)
  ·
    refine ⟨14451868601260573791154127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38538316270028196776411005 14451868601260573791154127)
    ·
      refine ⟨21677802901890860686731191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14451868601260573791154127 21677802901890860686731191)
      ·
        refine ⟨32516704352836291030096787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21677802901890860686731191 32516704352836291030096787)
        ·
          refine ⟨48775056529254436545145181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32516704352836291030096787 48775056529254436545145181)
          ·
            refine ⟨18290646198470413704429443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48775056529254436545145181 18290646198470413704429443)
            ·
              refine ⟨27435969297705620556644165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18290646198470413704429443 27435969297705620556644165)
              ·
                refine ⟨5144244243319803854370781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27435969297705620556644165 5144244243319803854370781)
                ·
                  refine ⟨1929091591244926445389043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5144244243319803854370781 1929091591244926445389043)
                  ·
                    refine ⟨2893637386867389668083565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1929091591244926445389043 2893637386867389668083565)
                    ·
                      refine ⟨1085114020075271125531337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2893637386867389668083565 1085114020075271125531337)
                      ·
                        rfl

theorem cell23_2113252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_2113252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113252 prefixEnd_2113252 := by exact prefixLift 2113252
  have htrace : WordTrace (prefixWord ++ tailWord_2113252) baseStart_2113252 baseEnd_2113252 := by
    simpa [prefixWord, tailWord_2113252, baseEnd_2113252] using wordTrace_append hprefix tailTrace_2113252
  have hstable : (prefixWord ++ tailWord_2113252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113252).length < 2 ^ (prefixWord ++ tailWord_2113252).sum := by decide
  have hdescent : baseEnd_2113252 < baseStart_2113252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113262 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 1, 5, 2]
def baseStart_2113262 : Nat := 118140960795 + 2113262 * 2 ^ 59
def prefixEnd_2113262 : Nat := 4983230072969 + 3 ^ 40 * 2113262 * 2
def baseEnd_2113262 : Nat := 1085119154881816086406291

theorem tailTrace_2113262 : CollatzResearch.WordTrace tailWord_2113262 prefixEnd_2113262 1085119154881816086406291 := by
  unfold tailWord_2113262
  simp only [CollatzResearch.WordTrace]
  refine ⟨9634624658752520657585755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51384664846680110173790693 9634624658752520657585755)
  ·
    refine ⟨14451936988128780986378633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9634624658752520657585755 14451936988128780986378633)
    ·
      refine ⟨10838952741096585739783975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14451936988128780986378633 10838952741096585739783975)
      ·
        refine ⟨16258429111644878609675963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10838952741096585739783975 16258429111644878609675963)
        ·
          refine ⟨24387643667467317914513945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16258429111644878609675963 24387643667467317914513945)
          ·
            refine ⟨18290732750600488435885459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24387643667467317914513945 18290732750600488435885459)
            ·
              refine ⟨27436099125900732653828189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18290732750600488435885459 27436099125900732653828189)
              ·
                refine ⟨10288537172212774745185571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27436099125900732653828189 10288537172212774745185571)
                ·
                  refine ⟨15432805758319162117778357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10288537172212774745185571 15432805758319162117778357)
                  ·
                    refine ⟨1446825539842421448541721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15432805758319162117778357 1446825539842421448541721)
                    ·
                      refine ⟨1085119154881816086406291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1446825539842421448541721 1085119154881816086406291)
                      ·
                        rfl

theorem cell23_2113262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_2113262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113262 prefixEnd_2113262 := by exact prefixLift 2113262
  have htrace : WordTrace (prefixWord ++ tailWord_2113262) baseStart_2113262 baseEnd_2113262 := by
    simpa [prefixWord, tailWord_2113262, baseEnd_2113262] using wordTrace_append hprefix tailTrace_2113262
  have hstable : (prefixWord ++ tailWord_2113262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113262).length < 2 ^ (prefixWord ++ tailWord_2113262).sum := by decide
  have hdescent : baseEnd_2113262 < baseStart_2113262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113293 : List Nat := [1, 7, 2, 1, 1, 1, 1, 3, 6]
def baseStart_2113293 : Nat := 118140960795 + 2113293 * 2 ^ 59
def prefixEnd_2113293 : Nat := 4983230072969 + 3 ^ 40 * 2113293 * 2
def baseEnd_2113293 : Nat := 120570563642456162790961

theorem tailTrace_2113293 : CollatzResearch.WordTrace tailWord_2113293 prefixEnd_2113293 120570563642456162790961 := by
  unfold tailWord_2113293
  simp only [CollatzResearch.WordTrace]
  refine ⟨77078127932907857555064533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51385418621938571703376355 77078127932907857555064533)
  ·
    refine ⟨1806518623427527911446825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 77078127932907857555064533 1806518623427527911446825)
    ·
      refine ⟨1354888967570645933585119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1806518623427527911446825 1354888967570645933585119)
      ·
        refine ⟨2032333451355968900377679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1354888967570645933585119 2032333451355968900377679)
        ·
          refine ⟨3048500177033953350566519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2032333451355968900377679 3048500177033953350566519)
          ·
            refine ⟨4572750265550930025849779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3048500177033953350566519 4572750265550930025849779)
            ·
              refine ⟨6859125398326395038774669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4572750265550930025849779 6859125398326395038774669)
              ·
                refine ⟨2572172024372398139540501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6859125398326395038774669 2572172024372398139540501)
                ·
                  refine ⟨120570563642456162790961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2572172024372398139540501 120570563642456162790961)
                  ·
                    rfl

theorem cell23_2113293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_2113293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113293 prefixEnd_2113293 := by exact prefixLift 2113293
  have htrace : WordTrace (prefixWord ++ tailWord_2113293) baseStart_2113293 baseEnd_2113293 := by
    simpa [prefixWord, tailWord_2113293, baseEnd_2113293] using wordTrace_append hprefix tailTrace_2113293
  have hstable : (prefixWord ++ tailWord_2113293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113293).length < 2 ^ (prefixWord ++ tailWord_2113293).sum := by decide
  have hdescent : baseEnd_2113293 < baseStart_2113293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113312 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 3]
def baseStart_2113312 : Nat := 118140960795 + 2113312 * 2 ^ 59
def prefixEnd_2113312 : Nat := 4983230072969 + 3 ^ 40 * 2113312 * 2
def baseEnd_2113312 : Nat := 1085144828914540890781061

theorem tailTrace_2113312 : CollatzResearch.WordTrace tailWord_2113312 prefixEnd_2113312 1085144828914540890781061 := by
  unfold tailWord_2113312
  simp only [CollatzResearch.WordTrace]
  refine ⟨38539410459919511900003095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51385880613226015866670793 38539410459919511900003095)
  ·
    refine ⟨57809115689879267850004643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38539410459919511900003095 57809115689879267850004643)
    ·
      refine ⟨86713673534818901775006965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57809115689879267850004643 86713673534818901775006965)
      ·
        refine ⟨8129406893889272041406903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86713673534818901775006965 8129406893889272041406903)
        ·
          refine ⟨12194110340833908062110355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8129406893889272041406903 12194110340833908062110355)
          ·
            refine ⟨18291165511250862093165533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12194110340833908062110355 18291165511250862093165533)
            ·
              refine ⟨6859187066719073284937075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18291165511250862093165533 6859187066719073284937075)
              ·
                refine ⟨10288780600078609927405613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6859187066719073284937075 10288780600078609927405613)
                ·
                  refine ⟨3858292725029478722777105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10288780600078609927405613 3858292725029478722777105)
                  ·
                    refine ⟨2893719543772109042082829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3858292725029478722777105 2893719543772109042082829)
                    ·
                      refine ⟨1085144828914540890781061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2893719543772109042082829 1085144828914540890781061)
                      ·
                        rfl

theorem cell23_2113312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_2113312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113312 prefixEnd_2113312 := by exact prefixLift 2113312
  have htrace : WordTrace (prefixWord ++ tailWord_2113312) baseStart_2113312 baseEnd_2113312 := by
    simpa [prefixWord, tailWord_2113312, baseEnd_2113312] using wordTrace_append hprefix tailTrace_2113312
  have hstable : (prefixWord ++ tailWord_2113312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113312).length < 2 ^ (prefixWord ++ tailWord_2113312).sum := by decide
  have hdescent : baseEnd_2113312 < baseStart_2113312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113337 : List Nat := [1, 2, 1, 7, 2, 1, 2, 2, 1, 1, 3]
def baseStart_2113337 : Nat := 118140960795 + 2113337 * 2 ^ 59
def prefixEnd_2113337 : Nat := 4983230072969 + 3 ^ 40 * 2113337 * 2
def baseEnd_2113337 : Nat := 1085157665930903292968447

theorem tailTrace_2113337 : CollatzResearch.WordTrace tailWord_2113337 prefixEnd_2113337 1085157665930903292968447 := by
  unfold tailWord_2113337
  simp only [CollatzResearch.WordTrace]
  refine ⟨77079732744748453069666265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51386488496498968713110843 77079732744748453069666265)
  ·
    refine ⟨57809799558561339802249699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77079732744748453069666265 57809799558561339802249699)
    ·
      refine ⟨86714699337842009703374549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57809799558561339802249699 86714699337842009703374549)
      ·
        refine ⟨2032375765730672102422841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 86714699337842009703374549 2032375765730672102422841)
        ·
          refine ⟨1524281824298004076817131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2032375765730672102422841 1524281824298004076817131)
          ·
            refine ⟨2286422736447006115225697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1524281824298004076817131 2286422736447006115225697)
            ·
              refine ⟨1714817052335254586419273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2286422736447006115225697 1714817052335254586419273)
              ·
                refine ⟨1286112789251440939814455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1714817052335254586419273 1286112789251440939814455)
                ·
                  refine ⟨1929169183877161409721683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1286112789251440939814455 1929169183877161409721683)
                  ·
                    refine ⟨2893753775815742114582525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1929169183877161409721683 2893753775815742114582525)
                    ·
                      refine ⟨1085157665930903292968447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2893753775815742114582525 1085157665930903292968447)
                      ·
                        rfl

theorem cell23_2113337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_2113337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113337 prefixEnd_2113337 := by exact prefixLift 2113337
  have htrace : WordTrace (prefixWord ++ tailWord_2113337) baseStart_2113337 baseEnd_2113337 := by
    simpa [prefixWord, tailWord_2113337, baseEnd_2113337] using wordTrace_append hprefix tailTrace_2113337
  have hstable : (prefixWord ++ tailWord_2113337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113337).length < 2 ^ (prefixWord ++ tailWord_2113337).sum := by decide
  have hdescent : baseEnd_2113337 < baseStart_2113337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113343 : List Nat := [1, 1, 2, 2, 6, 1, 1, 4, 1, 2, 2]
def baseStart_2113343 : Nat := 118140960795 + 2113343 * 2 ^ 59
def prefixEnd_2113343 : Nat := 4983230072969 + 3 ^ 40 * 2113343 * 2
def baseEnd_2113343 : Nat := 1085160746814830269493419

theorem tailTrace_2113343 : CollatzResearch.WordTrace tailWord_2113343 prefixEnd_2113343 1085160746814830269493419 := by
  unfold tailWord_2113343
  simp only [CollatzResearch.WordTrace]
  refine ⟨77079951582726716094384683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51386634388484477396256455 77079951582726716094384683)
  ·
    refine ⟨115619927374090074141577025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77079951582726716094384683 115619927374090074141577025)
    ·
      refine ⟨86714945530567555606182769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115619927374090074141577025 86714945530567555606182769)
      ·
        refine ⟨65036209147925666704637077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86714945530567555606182769 65036209147925666704637077)
        ·
          refine ⟨3048572303809015626779863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65036209147925666704637077 3048572303809015626779863)
          ·
            refine ⟨4572858455713523440169795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3048572303809015626779863 4572858455713523440169795)
            ·
              refine ⟨6859287683570285160254693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4572858455713523440169795 6859287683570285160254693)
              ·
                refine ⟨1286116440669428467547755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6859287683570285160254693 1286116440669428467547755)
                ·
                  refine ⟨1929174661004142701321633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1286116440669428467547755 1929174661004142701321633)
                  ·
                    refine ⟨1446880995753107025991225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1929174661004142701321633 1446880995753107025991225)
                    ·
                      refine ⟨1085160746814830269493419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1446880995753107025991225 1085160746814830269493419)
                      ·
                        rfl

theorem cell23_2113343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 1, 2, 2].length) (baseStart_2113343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113343 prefixEnd_2113343 := by exact prefixLift 2113343
  have htrace : WordTrace (prefixWord ++ tailWord_2113343) baseStart_2113343 baseEnd_2113343 := by
    simpa [prefixWord, tailWord_2113343, baseEnd_2113343] using wordTrace_append hprefix tailTrace_2113343
  have hstable : (prefixWord ++ tailWord_2113343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113343).length < 2 ^ (prefixWord ++ tailWord_2113343).sum := by decide
  have hdescent : baseEnd_2113343 < baseStart_2113343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113369 : List Nat := [1, 2, 1, 2, 2, 3, 2, 4, 1, 3, 2]
def baseStart_2113369 : Nat := 118140960795 + 2113369 * 2 ^ 59
def prefixEnd_2113369 : Nat := 4983230072969 + 3 ^ 40 * 2113369 * 2
def baseEnd_2113369 : Nat := 1085174097311847167768299

theorem tailTrace_2113369 : CollatzResearch.WordTrace tailWord_2113369 prefixEnd_2113369 1085174097311847167768299 := by
  unfold tailWord_2113369
  simp only [CollatzResearch.WordTrace]
  refine ⟨77080899880632522534831161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51387266587088348356554107 77080899880632522534831161)
  ·
    refine ⟨57810674910474391901123371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77080899880632522534831161 57810674910474391901123371)
    ·
      refine ⟨86716012365711587851685057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57810674910474391901123371 86716012365711587851685057)
      ·
        refine ⟨65037009274283690888763793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86716012365711587851685057 65037009274283690888763793)
        ·
          refine ⟨48777756955712768166572845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65037009274283690888763793 48777756955712768166572845)
          ·
            refine ⟨18291658858392288062464817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48777756955712768166572845 18291658858392288062464817)
            ·
              refine ⟨13718744143794216046848613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18291658858392288062464817 13718744143794216046848613)
              ·
                refine ⟨2572264526961415508784115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13718744143794216046848613 2572264526961415508784115)
                ·
                  refine ⟨3858396790442123263176173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2572264526961415508784115 3858396790442123263176173)
                  ·
                    refine ⟨1446898796415796223691065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3858396790442123263176173 1446898796415796223691065)
                    ·
                      refine ⟨1085174097311847167768299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1446898796415796223691065 1085174097311847167768299)
                      ·
                        rfl

theorem cell23_2113369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 3, 2].length) (baseStart_2113369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113369 prefixEnd_2113369 := by exact prefixLift 2113369
  have htrace : WordTrace (prefixWord ++ tailWord_2113369) baseStart_2113369 baseEnd_2113369 := by
    simpa [prefixWord, tailWord_2113369, baseEnd_2113369] using wordTrace_append hprefix tailTrace_2113369
  have hstable : (prefixWord ++ tailWord_2113369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113369).length < 2 ^ (prefixWord ++ tailWord_2113369).sum := by decide
  have hdescent : baseEnd_2113369 < baseStart_2113369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113385 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 2, 1, 5]
def baseStart_2113385 : Nat := 118140960795 + 2113385 * 2 ^ 59
def prefixEnd_2113385 : Nat := 4983230072969 + 3 ^ 40 * 2113385 * 2
def baseEnd_2113385 : Nat := 1085182313002319105168225

theorem tailTrace_2113385 : CollatzResearch.WordTrace tailWord_2113385 prefixEnd_2113385 1085182313002319105168225 := by
  unfold tailWord_2113385
  simp only [CollatzResearch.WordTrace]
  refine ⟨77081483448574557267413609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51387655632383038178275739 77081483448574557267413609)
  ·
    refine ⟨57811112586430917950560207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77081483448574557267413609 57811112586430917950560207)
    ·
      refine ⟨86716668879646376925840311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57811112586430917950560207 86716668879646376925840311)
      ·
        refine ⟨130075003319469565388760467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86716668879646376925840311 130075003319469565388760467)
        ·
          refine ⟨195112504979204348083140701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130075003319469565388760467 195112504979204348083140701)
          ·
            refine ⟨73167189367201630531177763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 195112504979204348083140701 73167189367201630531177763)
            ·
              refine ⟨109750784050802445796766645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73167189367201630531177763 109750784050802445796766645)
              ·
                refine ⟨10289136004762729293446873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109750784050802445796766645 10289136004762729293446873)
                ·
                  refine ⟨7716852003572046970085155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10289136004762729293446873 7716852003572046970085155)
                  ·
                    refine ⟨11575278005358070455127733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7716852003572046970085155 11575278005358070455127733)
                    ·
                      refine ⟨1085182313002319105168225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11575278005358070455127733 1085182313002319105168225)
                      ·
                        rfl

theorem cell23_2113385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 1, 5].length) (baseStart_2113385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113385 prefixEnd_2113385 := by exact prefixLift 2113385
  have htrace : WordTrace (prefixWord ++ tailWord_2113385) baseStart_2113385 baseEnd_2113385 := by
    simpa [prefixWord, tailWord_2113385, baseEnd_2113385] using wordTrace_append hprefix tailTrace_2113385
  have hstable : (prefixWord ++ tailWord_2113385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113385).length < 2 ^ (prefixWord ++ tailWord_2113385).sum := by decide
  have hdescent : baseEnd_2113385 < baseStart_2113385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113412 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_2113412 : Nat := 118140960795 + 2113412 * 2 ^ 59
def prefixEnd_2113412 : Nat := 4983230072969 + 3 ^ 40 * 2113412 * 2
def baseEnd_2113412 : Nat := 1085196176979990499530601

theorem tailTrace_2113412 : CollatzResearch.WordTrace tailWord_2113412 prefixEnd_2113412 1085196176979990499530601 := by
  unfold tailWord_2113412
  simp only [CollatzResearch.WordTrace]
  refine ⟨38541234109738370439323245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51388312146317827252430993 38541234109738370439323245)
  ·
    refine ⟨14452962791151888914746217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38541234109738370439323245 14452962791151888914746217)
    ·
      refine ⟨10839722093363916686059663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14452962791151888914746217 10839722093363916686059663)
      ·
        refine ⟨16259583140045875029089495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10839722093363916686059663 16259583140045875029089495)
        ·
          refine ⟨24389374710068812543634243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16259583140045875029089495 24389374710068812543634243)
          ·
            refine ⟨36584062065103218815451365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24389374710068812543634243 36584062065103218815451365)
            ·
              refine ⟨6859511637206853527897131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36584062065103218815451365 6859511637206853527897131)
              ·
                refine ⟨10289267455810280291845697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6859511637206853527897131 10289267455810280291845697)
                ·
                  refine ⟨7716950591857710218884273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10289267455810280291845697 7716950591857710218884273)
                  ·
                    refine ⟨5787712943893282664163205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7716950591857710218884273 5787712943893282664163205)
                    ·
                      refine ⟨1085196176979990499530601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5787712943893282664163205 1085196176979990499530601)
                      ·
                        rfl

theorem cell23_2113412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_2113412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113412 prefixEnd_2113412 := by exact prefixLift 2113412
  have htrace : WordTrace (prefixWord ++ tailWord_2113412) baseStart_2113412 baseEnd_2113412 := by
    simpa [prefixWord, tailWord_2113412, baseEnd_2113412] using wordTrace_append hprefix tailTrace_2113412
  have hstable : (prefixWord ++ tailWord_2113412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113412).length < 2 ^ (prefixWord ++ tailWord_2113412).sum := by decide
  have hdescent : baseEnd_2113412 < baseStart_2113412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113445 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 3, 1, 7]
def baseStart_2113445 : Nat := 118140960795 + 2113445 * 2 ^ 59
def prefixEnd_2113445 : Nat := 4983230072969 + 3 ^ 40 * 2113445 * 2
def baseEnd_2113445 : Nat := 1085213121841588870417949

theorem tailTrace_2113445 : CollatzResearch.WordTrace tailWord_2113445 prefixEnd_2113445 1085213121841588870417949 := by
  unfold tailWord_2113445
  simp only [CollatzResearch.WordTrace]
  refine ⟨77083671828357187514597789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51389114552238125009731859 77083671828357187514597789)
  ·
    refine ⟨28906376935633945317974171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77083671828357187514597789 28906376935633945317974171)
    ·
      refine ⟨43359565403450917976961257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28906376935633945317974171 43359565403450917976961257)
      ·
        refine ⟨32519674052588188482720943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43359565403450917976961257 32519674052588188482720943)
        ·
          refine ⟨48779511078882282724081415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32519674052588188482720943 48779511078882282724081415)
          ·
            refine ⟨73169266618323424086122123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48779511078882282724081415 73169266618323424086122123)
            ·
              refine ⟨109753899927485136129183185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73169266618323424086122123 109753899927485136129183185)
              ·
                refine ⟨82315424945613852096887389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109753899927485136129183185 82315424945613852096887389)
                ·
                  refine ⟨30868284354605194536332771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82315424945613852096887389 30868284354605194536332771)
                  ·
                    refine ⟨46302426531907791804499157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30868284354605194536332771 46302426531907791804499157)
                    ·
                      refine ⟨1085213121841588870417949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46302426531907791804499157 1085213121841588870417949)
                      ·
                        rfl

theorem cell23_2113445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_2113445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113445 prefixEnd_2113445 := by exact prefixLift 2113445
  have htrace : WordTrace (prefixWord ++ tailWord_2113445) baseStart_2113445 baseEnd_2113445 := by
    simpa [prefixWord, tailWord_2113445, baseEnd_2113445] using wordTrace_append hprefix tailTrace_2113445
  have hstable : (prefixWord ++ tailWord_2113445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113445).length < 2 ^ (prefixWord ++ tailWord_2113445).sum := by decide
  have hdescent : baseEnd_2113445 < baseStart_2113445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113472 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 4]
def baseStart_2113472 : Nat := 118140960795 + 2113472 * 2 ^ 59
def prefixEnd_2113472 : Nat := 4983230072969 + 3 ^ 40 * 2113472 * 2
def baseEnd_2113472 : Nat := 1085226985819260264780325

theorem tailTrace_2113472 : CollatzResearch.WordTrace tailWord_2113472 prefixEnd_2113472 1085226985819260264780325 := by
  unfold tailWord_2113472
  simp only [CollatzResearch.WordTrace]
  refine ⟨38542328299629685562915335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51389771066172914083887113 38542328299629685562915335)
  ·
    refine ⟨57813492449444528344373003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38542328299629685562915335 57813492449444528344373003)
    ·
      refine ⟨86720238674166792516559505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57813492449444528344373003 86720238674166792516559505)
      ·
        refine ⟨65040179005625094387419629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86720238674166792516559505 65040179005625094387419629)
        ·
          refine ⟨24390067127109410395282361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65040179005625094387419629 24390067127109410395282361)
          ·
            refine ⟨18292550345332057796461771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24390067127109410395282361 18292550345332057796461771)
            ·
              refine ⟨27438825517998086694692657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18292550345332057796461771 27438825517998086694692657)
              ·
                refine ⟨20579119138498565021019493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27438825517998086694692657 20579119138498565021019493)
                ·
                  refine ⟨3858584838468480941441155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20579119138498565021019493 3858584838468480941441155)
                  ·
                    refine ⟨5787877257702721412161733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3858584838468480941441155 5787877257702721412161733)
                    ·
                      refine ⟨1085226985819260264780325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5787877257702721412161733 1085226985819260264780325)
                      ·
                        rfl

theorem cell23_2113472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_2113472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113472 prefixEnd_2113472 := by exact prefixLift 2113472
  have htrace : WordTrace (prefixWord ++ tailWord_2113472) baseStart_2113472 baseEnd_2113472 := by
    simpa [prefixWord, tailWord_2113472, baseEnd_2113472] using wordTrace_append hprefix tailTrace_2113472
  have hstable : (prefixWord ++ tailWord_2113472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113472).length < 2 ^ (prefixWord ++ tailWord_2113472).sum := by decide
  have hdescent : baseEnd_2113472 < baseStart_2113472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113540 : List Nat := [2, 3, 2, 4, 2, 1, 1, 1, 2, 1, 4]
def baseStart_2113540 : Nat := 118140960795 + 2113540 * 2 ^ 59
def prefixEnd_2113540 : Nat := 4983230072969 + 3 ^ 40 * 2113540 * 2
def baseEnd_2113540 : Nat := 1085261902503765998730013

theorem tailTrace_2113540 : CollatzResearch.WordTrace tailWord_2113540 prefixEnd_2113540 1085261902503765998730013 := by
  unfold tailWord_2113540
  simp only [CollatzResearch.WordTrace]
  refine ⟨38543568381506509369653037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51391424508675345826204049 38543568381506509369653037)
  ·
    refine ⟨14453838143064941013619889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38543568381506509369653037 14453838143064941013619889)
    ·
      refine ⟨10840378607298705760214917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14453838143064941013619889 10840378607298705760214917)
      ·
        refine ⟨2032570988868507330040297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10840378607298705760214917 2032570988868507330040297)
        ·
          refine ⟨1524428241651380497530223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2032570988868507330040297 1524428241651380497530223)
          ·
            refine ⟨2286642362477070746295335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1524428241651380497530223 2286642362477070746295335)
            ·
              refine ⟨3429963543715606119443003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2286642362477070746295335 3429963543715606119443003)
              ·
                refine ⟨5144945315573409179164505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3429963543715606119443003 5144945315573409179164505)
                ·
                  refine ⟨3858708986680056884373379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5144945315573409179164505 3858708986680056884373379)
                  ·
                    refine ⟨5788063480020085326560069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3858708986680056884373379 5788063480020085326560069)
                    ·
                      refine ⟨1085261902503765998730013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5788063480020085326560069 1085261902503765998730013)
                      ·
                        rfl

theorem cell23_2113540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_2113540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113540 prefixEnd_2113540 := by exact prefixLift 2113540
  have htrace : WordTrace (prefixWord ++ tailWord_2113540) baseStart_2113540 baseEnd_2113540 := by
    simpa [prefixWord, tailWord_2113540, baseEnd_2113540] using wordTrace_append hprefix tailTrace_2113540
  have hstable : (prefixWord ++ tailWord_2113540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113540).length < 2 ^ (prefixWord ++ tailWord_2113540).sum := by decide
  have hdescent : baseEnd_2113540 < baseStart_2113540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113573 : List Nat := [1, 3, 1, 2, 2, 3, 2, 4, 1, 1, 3]
def baseStart_2113573 : Nat := 118140960795 + 2113573 * 2 ^ 59
def prefixEnd_2113573 : Nat := 4983230072969 + 3 ^ 40 * 2113573 * 2
def baseEnd_2113573 : Nat := 1085278847365364369617361

theorem tailTrace_2113573 : CollatzResearch.WordTrace tailWord_2113573 prefixEnd_2113573 1085278847365364369617361 := by
  unfold tailWord_2113573
  simp only [CollatzResearch.WordTrace]
  refine ⟨77088340371893465375257373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51392226914595643583504915 77088340371893465375257373)
  ·
    refine ⟨28908127639460049515721515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77088340371893465375257373 28908127639460049515721515)
    ·
      refine ⟨43362191459190074273582273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28908127639460049515721515 43362191459190074273582273)
      ·
        refine ⟨32521643594392555705186705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43362191459190074273582273 32521643594392555705186705)
        ·
          refine ⟨24391232695794416778890029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32521643594392555705186705 24391232695794416778890029)
          ·
            refine ⟨9146712260922906292083761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24391232695794416778890029 9146712260922906292083761)
            ·
              refine ⟨6860034195692179719062821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9146712260922906292083761 6860034195692179719062821)
              ·
                refine ⟨1286256411692283697324279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6860034195692179719062821 1286256411692283697324279)
                ·
                  refine ⟨1929384617538425545986419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1286256411692283697324279 1929384617538425545986419)
                  ·
                    refine ⟨2894076926307638318979629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1929384617538425545986419 2894076926307638318979629)
                    ·
                      refine ⟨1085278847365364369617361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2894076926307638318979629 1085278847365364369617361)
                      ·
                        rfl

theorem cell23_2113573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 1, 1, 3].length) (baseStart_2113573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113573 prefixEnd_2113573 := by exact prefixLift 2113573
  have htrace : WordTrace (prefixWord ++ tailWord_2113573) baseStart_2113573 baseEnd_2113573 := by
    simpa [prefixWord, tailWord_2113573, baseEnd_2113573] using wordTrace_append hprefix tailTrace_2113573
  have hstable : (prefixWord ++ tailWord_2113573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113573).length < 2 ^ (prefixWord ++ tailWord_2113573).sum := by decide
  have hdescent : baseEnd_2113573 < baseStart_2113573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113589 : List Nat := [1, 3, 3, 1, 1, 1, 5, 1, 1, 6]
def baseStart_2113589 : Nat := 118140960795 + 2113589 * 2 ^ 59
def prefixEnd_2113589 : Nat := 4983230072969 + 3 ^ 40 * 2113589 * 2
def baseEnd_2113589 : Nat := 361762354351945435672429

theorem tailTrace_2113589 : CollatzResearch.WordTrace tailWord_2113589 prefixEnd_2113589 361762354351945435672429 := by
  unfold tailWord_2113589
  simp only [CollatzResearch.WordTrace]
  refine ⟨77088923939835500107839821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51392615959890333405226547 77088923939835500107839821)
  ·
    refine ⟨28908346477438312540439933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77088923939835500107839821 28908346477438312540439933)
    ·
      refine ⟨10840629929039367202664975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28908346477438312540439933 10840629929039367202664975)
      ·
        refine ⟨16260944893559050803997463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10840629929039367202664975 16260944893559050803997463)
        ·
          refine ⟨24391417340338576205996195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16260944893559050803997463 24391417340338576205996195)
          ·
            refine ⟨36587126010507864308994293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24391417340338576205996195 36587126010507864308994293)
            ·
              refine ⟨3430043063485112278968215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36587126010507864308994293 3430043063485112278968215)
              ·
                refine ⟨5145064595227668418452323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3430043063485112278968215 5145064595227668418452323)
                ·
                  refine ⟨7717596892841502627678485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5145064595227668418452323 7717596892841502627678485)
                  ·
                    refine ⟨361762354351945435672429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7717596892841502627678485 361762354351945435672429)
                    ·
                      rfl

theorem cell23_2113589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_2113589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113589 prefixEnd_2113589 := by exact prefixLift 2113589
  have htrace : WordTrace (prefixWord ++ tailWord_2113589) baseStart_2113589 baseEnd_2113589 := by
    simpa [prefixWord, tailWord_2113589, baseEnd_2113589] using wordTrace_append hprefix tailTrace_2113589
  have hstable : (prefixWord ++ tailWord_2113589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113589).length < 2 ^ (prefixWord ++ tailWord_2113589).sum := by decide
  have hdescent : baseEnd_2113589 < baseStart_2113589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113596 : List Nat := [2, 2, 2, 2, 2, 1, 4, 2, 1, 1, 4]
def baseStart_2113596 : Nat := 118140960795 + 2113596 * 2 ^ 59
def prefixEnd_2113596 : Nat := 4983230072969 + 3 ^ 40 * 2113596 * 2
def baseEnd_2113596 : Nat := 1085290657420417779629755

theorem tailTrace_2113596 : CollatzResearch.WordTrace tailWord_2113596 prefixEnd_2113596 1085290657420417779629755 := by
  unfold tailWord_2113596
  simp only [CollatzResearch.WordTrace]
  refine ⟨38544589625405070151672321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51392786167206760202229761 38544589625405070151672321)
  ·
    refine ⟨28908442219053802613754241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38544589625405070151672321 28908442219053802613754241)
    ·
      refine ⟨21681331664290351960315681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28908442219053802613754241 21681331664290351960315681)
      ·
        refine ⟨16260998748217763970236761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21681331664290351960315681 16260998748217763970236761)
        ·
          refine ⟨12195749061163322977677571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16260998748217763970236761 12195749061163322977677571)
          ·
            refine ⟨18293623591744984466516357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12195749061163322977677571 18293623591744984466516357)
            ·
              refine ⟨3430054423452184587471817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18293623591744984466516357 3430054423452184587471817)
              ·
                refine ⟨2572540817589138440603863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3430054423452184587471817 2572540817589138440603863)
                ·
                  refine ⟨3858811226383707660905795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2572540817589138440603863 3858811226383707660905795)
                  ·
                    refine ⟨5788216839575561491358693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3858811226383707660905795 5788216839575561491358693)
                    ·
                      refine ⟨1085290657420417779629755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5788216839575561491358693 1085290657420417779629755)
                      ·
                        rfl

theorem cell23_2113596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_2113596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113596 prefixEnd_2113596 := by exact prefixLift 2113596
  have htrace : WordTrace (prefixWord ++ tailWord_2113596) baseStart_2113596 baseEnd_2113596 := by
    simpa [prefixWord, tailWord_2113596, baseEnd_2113596] using wordTrace_append hprefix tailTrace_2113596
  have hstable : (prefixWord ++ tailWord_2113596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113596).length < 2 ^ (prefixWord ++ tailWord_2113596).sum := by decide
  have hdescent : baseEnd_2113596 < baseStart_2113596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113599 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 3]
def baseStart_2113599 : Nat := 118140960795 + 2113599 * 2 ^ 59
def prefixEnd_2113599 : Nat := 4983230072969 + 3 ^ 40 * 2113599 * 2
def baseEnd_2113599 : Nat := 1085292197862381267892241

theorem tailTrace_2113599 : CollatzResearch.WordTrace tailWord_2113599 prefixEnd_2113599 1085292197862381267892241 := by
  unfold tailWord_2113599
  simp only [CollatzResearch.WordTrace]
  refine ⟨77089288669799271815703851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51392859113199514543802567 77089288669799271815703851)
  ·
    refine ⟨115633933004698907723555777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77089288669799271815703851 115633933004698907723555777)
    ·
      refine ⟨86725449753524180792666833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115633933004698907723555777 86725449753524180792666833)
      ·
        refine ⟨65044087315143135594500125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86725449753524180792666833 65044087315143135594500125)
        ·
          refine ⟨24391532743178675847937547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65044087315143135594500125 24391532743178675847937547)
          ·
            refine ⟨36587299114768013771906321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24391532743178675847937547 36587299114768013771906321)
            ·
              refine ⟨27440474336076010328929741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36587299114768013771906321 27440474336076010328929741)
              ·
                refine ⟨10290177876028503873348653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27440474336076010328929741 10290177876028503873348653)
                ·
                  refine ⟨3858816703510688952505745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10290177876028503873348653 3858816703510688952505745)
                  ·
                    refine ⟨2894112527633016714379309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3858816703510688952505745 2894112527633016714379309)
                    ·
                      refine ⟨1085292197862381267892241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2894112527633016714379309 1085292197862381267892241)
                      ·
                        rfl

theorem cell23_2113599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 3].length) (baseStart_2113599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113599 prefixEnd_2113599 := by exact prefixLift 2113599
  have htrace : WordTrace (prefixWord ++ tailWord_2113599) baseStart_2113599 baseEnd_2113599 := by
    simpa [prefixWord, tailWord_2113599, baseEnd_2113599] using wordTrace_append hprefix tailTrace_2113599
  have hstable : (prefixWord ++ tailWord_2113599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113599).length < 2 ^ (prefixWord ++ tailWord_2113599).sum := by decide
  have hdescent : baseEnd_2113599 < baseStart_2113599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113606 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_2113606 : Nat := 118140960795 + 2113606 * 2 ^ 59
def prefixEnd_2113606 : Nat := 4983230072969 + 3 ^ 40 * 2113606 * 2
def baseEnd_2113606 : Nat := 361765264075654246834903

theorem tailTrace_2113606 : CollatzResearch.WordTrace tailWord_2113606 prefixEnd_2113606 361765264075654246834903 := by
  unfold tailWord_2113606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2409048249399184750350271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51393029320515941340805781 2409048249399184750350271)
  ·
    refine ⟨3613572374098777125525407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2409048249399184750350271 3613572374098777125525407)
    ·
      refine ⟨5420358561148165688288111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3613572374098777125525407 5420358561148165688288111)
      ·
        refine ⟨8130537841722248532432167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5420358561148165688288111 8130537841722248532432167)
        ·
          refine ⟨12195806762583372798648251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8130537841722248532432167 12195806762583372798648251)
          ·
            refine ⟨18293710143875059197972377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12195806762583372798648251 18293710143875059197972377)
            ·
              refine ⟨13720282607906294398479283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18293710143875059197972377 13720282607906294398479283)
              ·
                refine ⟨20580423911859441597718925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13720282607906294398479283 20580423911859441597718925)
                ·
                  refine ⟨7717658966947290599144597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20580423911859441597718925 7717658966947290599144597)
                  ·
                    refine ⟨361765264075654246834903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7717658966947290599144597 361765264075654246834903)
                    ·
                      rfl

theorem cell23_2113606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_2113606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113606 prefixEnd_2113606 := by exact prefixLift 2113606
  have htrace : WordTrace (prefixWord ++ tailWord_2113606) baseStart_2113606 baseEnd_2113606 := by
    simpa [prefixWord, tailWord_2113606, baseEnd_2113606] using wordTrace_append hprefix tailTrace_2113606
  have hstable : (prefixWord ++ tailWord_2113606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113606).length < 2 ^ (prefixWord ++ tailWord_2113606).sum := by decide
  have hdescent : baseEnd_2113606 < baseStart_2113606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113646 : List Nat := [4, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3]
def baseStart_2113646 : Nat := 118140960795 + 2113646 * 2 ^ 59
def prefixEnd_2113646 : Nat := 4983230072969 + 3 ^ 40 * 2113646 * 2
def baseEnd_2113646 : Nat := 1085316331453142584004525

theorem tailTrace_2113646 : CollatzResearch.WordTrace tailWord_2113646 prefixEnd_2113646 1085316331453142584004525 := by
  unfold tailWord_2113646
  simp only [CollatzResearch.WordTrace]
  refine ⟨9636375362578624855333099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51394001933752665895109861 9636375362578624855333099)
  ·
    refine ⟨14454563043867937282999649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9636375362578624855333099 14454563043867937282999649)
    ·
      refine ⟨10840922282900952962249737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14454563043867937282999649 10840922282900952962249737)
      ·
        refine ⟨8130691712175714721687303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10840922282900952962249737 8130691712175714721687303)
        ·
          refine ⟨12196037568263572082530955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8130691712175714721687303 12196037568263572082530955)
          ·
            refine ⟨18294056352395358123796433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12196037568263572082530955 18294056352395358123796433)
            ·
              refine ⟨13720542264296518592847325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18294056352395358123796433 13720542264296518592847325)
              ·
                refine ⟨5145203349111194472317747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13720542264296518592847325 5145203349111194472317747)
                ·
                  refine ⟨7717805023666791708476621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5145203349111194472317747 7717805023666791708476621)
                  ·
                    refine ⟨2894176883875046890678733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7717805023666791708476621 2894176883875046890678733)
                    ·
                      refine ⟨1085316331453142584004525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2894176883875046890678733 1085316331453142584004525)
                      ·
                        rfl

theorem cell23_2113646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_2113646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113646 prefixEnd_2113646 := by exact prefixLift 2113646
  have htrace : WordTrace (prefixWord ++ tailWord_2113646) baseStart_2113646 baseEnd_2113646 := by
    simpa [prefixWord, tailWord_2113646, baseEnd_2113646] using wordTrace_append hprefix tailTrace_2113646
  have hstable : (prefixWord ++ tailWord_2113646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113646).length < 2 ^ (prefixWord ++ tailWord_2113646).sum := by decide
  have hdescent : baseEnd_2113646 < baseStart_2113646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113724 : List Nat := [2, 2, 2, 3, 4, 1, 2, 1, 1, 3, 2]
def baseStart_2113724 : Nat := 118140960795 + 2113724 * 2 ^ 59
def prefixEnd_2113724 : Nat := 4983230072969 + 3 ^ 40 * 2113724 * 2
def baseEnd_2113724 : Nat := 1085356382944193278829167

theorem tailTrace_2113724 : CollatzResearch.WordTrace tailWord_2113724 prefixEnd_2113724 1085356382944193278829167 := by
  unfold tailWord_2113724
  simp only [CollatzResearch.WordTrace]
  refine ⟨38546923897173209082002113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51395898529564278776002817 38546923897173209082002113)
  ·
    refine ⟨28910192922879906811501585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38546923897173209082002113 28910192922879906811501585)
    ·
      refine ⟨21682644692159930108626189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28910192922879906811501585 21682644692159930108626189)
      ·
        refine ⟨8130991759559973790734821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21682644692159930108626189 8130991759559973790734821)
        ·
          refine ⟨1524560954917495085762779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8130991759559973790734821 1524560954917495085762779)
          ·
            refine ⟨2286841432376242628644169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1524560954917495085762779 2286841432376242628644169)
            ·
              refine ⟨1715131074282181971483127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2286841432376242628644169 1715131074282181971483127)
              ·
                refine ⟨2572696611423272957224691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1715131074282181971483127 2572696611423272957224691)
                ·
                  refine ⟨3859044917134909435837037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2572696611423272957224691 3859044917134909435837037)
                  ·
                    refine ⟨1447141843925591038438889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3859044917134909435837037 1447141843925591038438889)
                    ·
                      refine ⟨1085356382944193278829167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1447141843925591038438889 1085356382944193278829167)
                      ·
                        rfl

theorem cell23_2113724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_2113724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113724 prefixEnd_2113724 := by exact prefixLift 2113724
  have htrace : WordTrace (prefixWord ++ tailWord_2113724) baseStart_2113724 baseEnd_2113724 := by
    simpa [prefixWord, tailWord_2113724, baseEnd_2113724] using wordTrace_append hprefix tailTrace_2113724
  have hstable : (prefixWord ++ tailWord_2113724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113724).length < 2 ^ (prefixWord ++ tailWord_2113724).sum := by decide
  have hdescent : baseEnd_2113724 < baseStart_2113724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113739 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 4, 5]
def baseStart_2113739 : Nat := 118140960795 + 2113739 * 2 ^ 59
def prefixEnd_2113739 : Nat := 4983230072969 + 3 ^ 40 * 2113739 * 2
def baseEnd_2113739 : Nat := 361788028384670240047199

theorem tailTrace_2113739 : CollatzResearch.WordTrace tailWord_2113739 prefixEnd_2113739 361788028384670240047199 := by
  unfold tailWord_2113739
  simp only [CollatzResearch.WordTrace]
  refine ⟨77094394889292075725800271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51396263259528050483866847 77094394889292075725800271)
  ·
    refine ⟨115641592333938113588700407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77094394889292075725800271 115641592333938113588700407)
    ·
      refine ⟨173462388500907170383050611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115641592333938113588700407 173462388500907170383050611)
      ·
        refine ⟨260193582751360755574575917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173462388500907170383050611 260193582751360755574575917)
        ·
          refine ⟨97572593531760283340465969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 260193582751360755574575917 97572593531760283340465969)
          ·
            refine ⟨73179445148820212505349477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97572593531760283340465969 73179445148820212505349477)
            ·
              refine ⟨13721145965403789844753027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73179445148820212505349477 13721145965403789844753027)
              ·
                refine ⟨20581718948105684767129541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13721145965403789844753027 20581718948105684767129541)
                ·
                  refine ⟨3859072302769815893836789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20581718948105684767129541 3859072302769815893836789)
                  ·
                    refine ⟨361788028384670240047199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3859072302769815893836789 361788028384670240047199)
                    ·
                      rfl

theorem cell23_2113739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 5].length) (baseStart_2113739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113739 prefixEnd_2113739 := by exact prefixLift 2113739
  have htrace : WordTrace (prefixWord ++ tailWord_2113739) baseStart_2113739 baseEnd_2113739 := by
    simpa [prefixWord, tailWord_2113739, baseEnd_2113739] using wordTrace_append hprefix tailTrace_2113739
  have hstable : (prefixWord ++ tailWord_2113739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113739).length < 2 ^ (prefixWord ++ tailWord_2113739).sum := by decide
  have hdescent : baseEnd_2113739 < baseStart_2113739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113776 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 1, 6, 2]
def baseStart_2113776 : Nat := 118140960795 + 2113776 * 2 ^ 59
def prefixEnd_2113776 : Nat := 4983230072969 + 3 ^ 40 * 2113776 * 2
def baseEnd_2113776 : Nat := 1085383083938227075378927

theorem tailTrace_2113776 : CollatzResearch.WordTrace tailWord_2113776 prefixEnd_2113776 1085383083938227075378927 := by
  unfold tailWord_2113776
  simp only [CollatzResearch.WordTrace]
  refine ⟨38547872195079015522448591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51397162926772020696598121 38547872195079015522448591)
  ·
    refine ⟨57821808292618523283672887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38547872195079015522448591 57821808292618523283672887)
    ·
      refine ⟨86732712438927784925509331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57821808292618523283672887 86732712438927784925509331)
      ·
        refine ⟨130099068658391677388263997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86732712438927784925509331 130099068658391677388263997)
        ·
          refine ⟨48787150746896879020598999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130099068658391677388263997 48787150746896879020598999)
          ·
            refine ⟨73180726120345318530898499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48787150746896879020598999 73180726120345318530898499)
            ·
              refine ⟨109771089180517977796347749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73180726120345318530898499 109771089180517977796347749)
              ·
                refine ⟨20582079221347120836815203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109771089180517977796347749 20582079221347120836815203)
                ·
                  refine ⟨30873118832020681255222805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20582079221347120836815203 30873118832020681255222805)
                  ·
                    refine ⟨1447177445250969433838569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30873118832020681255222805 1447177445250969433838569)
                    ·
                      refine ⟨1085383083938227075378927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1447177445250969433838569 1085383083938227075378927)
                      ·
                        rfl

theorem cell23_2113776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 1, 6, 2].length) (baseStart_2113776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113776 prefixEnd_2113776 := by exact prefixLift 2113776
  have htrace : WordTrace (prefixWord ++ tailWord_2113776) baseStart_2113776 baseEnd_2113776 := by
    simpa [prefixWord, tailWord_2113776, baseEnd_2113776] using wordTrace_append hprefix tailTrace_2113776
  have hstable : (prefixWord ++ tailWord_2113776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113776).length < 2 ^ (prefixWord ++ tailWord_2113776).sum := by decide
  have hdescent : baseEnd_2113776 < baseStart_2113776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113789 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 1, 3, 6]
def baseStart_2113789 : Nat := 118140960795 + 2113789 * 2 ^ 59
def prefixEnd_2113789 : Nat := 4983230072969 + 3 ^ 40 * 2113789 * 2
def baseEnd_2113789 : Nat := 1085389759186735524516367

theorem tailTrace_2113789 : CollatzResearch.WordTrace tailWord_2113789 prefixEnd_2113789 1085389759186735524516367 := by
  unfold tailWord_2113789
  simp only [CollatzResearch.WordTrace]
  refine ⟨77096218539110934265120421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51397479026073956176746947 77096218539110934265120421)
  ·
    refine ⟨14455540976083300174710079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77096218539110934265120421 14455540976083300174710079)
    ·
      refine ⟨21683311464124950262065119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14455540976083300174710079 21683311464124950262065119)
      ·
        refine ⟨32524967196187425393097679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21683311464124950262065119 32524967196187425393097679)
        ·
          refine ⟨48787450794281138089646519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32524967196187425393097679 48787450794281138089646519)
          ·
            refine ⟨73181176191421707134469779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48787450794281138089646519 73181176191421707134469779)
            ·
              refine ⟨109771764287132560701704669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73181176191421707134469779 109771764287132560701704669)
              ·
                refine ⟨41164411607674710263139251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109771764287132560701704669 41164411607674710263139251)
                ·
                  refine ⟨61746617411512065394708877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41164411607674710263139251 61746617411512065394708877)
                  ·
                    refine ⟨23154981529317024523015829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61746617411512065394708877 23154981529317024523015829)
                    ·
                      refine ⟨1085389759186735524516367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23154981529317024523015829 1085389759186735524516367)
                      ·
                        rfl

theorem cell23_2113789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_2113789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113789 prefixEnd_2113789 := by exact prefixLift 2113789
  have htrace : WordTrace (prefixWord ++ tailWord_2113789) baseStart_2113789 baseEnd_2113789 := by
    simpa [prefixWord, tailWord_2113789, baseEnd_2113789] using wordTrace_append hprefix tailTrace_2113789
  have hstable : (prefixWord ++ tailWord_2113789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113789).length < 2 ^ (prefixWord ++ tailWord_2113789).sum := by decide
  have hdescent : baseEnd_2113789 < baseStart_2113789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113816 : List Nat := [2, 1, 2, 3, 1, 2, 3, 3, 6]
def baseStart_2113816 : Nat := 118140960795 + 2113816 * 2 ^ 59
def prefixEnd_2113816 : Nat := 4983230072969 + 3 ^ 40 * 2113816 * 2
def baseEnd_2113816 : Nat := 120600402573822990986527

theorem tailTrace_2113816 : CollatzResearch.WordTrace tailWord_2113816 prefixEnd_2113816 120600402573822990986527 := by
  unfold tailWord_2113816
  simp only [CollatzResearch.WordTrace]
  refine ⟨38548601655006558938176651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51398135540008745250902201 38548601655006558938176651)
  ·
    refine ⟨57822902482509838407264977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38548601655006558938176651 57822902482509838407264977)
    ·
      refine ⟨43367176861882378805448733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57822902482509838407264977 43367176861882378805448733)
      ·
        refine ⟨16262691323205892052043275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43367176861882378805448733 16262691323205892052043275)
        ·
          refine ⟨24394036984808838078064913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16262691323205892052043275 24394036984808838078064913)
          ·
            refine ⟨18295527738606628558548685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24394036984808838078064913 18295527738606628558548685)
            ·
              refine ⟨6860822901977485709455757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18295527738606628558548685 6860822901977485709455757)
              ·
                refine ⟨2572808588241557141045909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6860822901977485709455757 2572808588241557141045909)
                ·
                  refine ⟨120600402573822990986527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2572808588241557141045909 120600402573822990986527)
                  ·
                    rfl

theorem cell23_2113816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 6].length) (baseStart_2113816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113816 prefixEnd_2113816 := by exact prefixLift 2113816
  have htrace : WordTrace (prefixWord ++ tailWord_2113816) baseStart_2113816 baseEnd_2113816 := by
    simpa [prefixWord, tailWord_2113816, baseEnd_2113816] using wordTrace_append hprefix tailTrace_2113816
  have hstable : (prefixWord ++ tailWord_2113816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113816).length < 2 ^ (prefixWord ++ tailWord_2113816).sum := by decide
  have hdescent : baseEnd_2113816 < baseStart_2113816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113819 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 6]
def baseStart_2113819 : Nat := 118140960795 + 2113819 * 2 ^ 59
def prefixEnd_2113819 : Nat := 4983230072969 + 3 ^ 40 * 2113819 * 2
def baseEnd_2113819 : Nat := 1085405163606370407141229

theorem tailTrace_2113819 : CollatzResearch.WordTrace tailWord_2113819 prefixEnd_2113819 1085405163606370407141229 := by
  unfold tailWord_2113819
  simp only [CollatzResearch.WordTrace]
  refine ⟨77097312729002249388712511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51398208486001499592475007 77097312729002249388712511)
  ·
    refine ⟨115645969093503374083068767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77097312729002249388712511 115645969093503374083068767)
    ·
      refine ⟨173468953640255061124603151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115645969093503374083068767 173468953640255061124603151)
      ·
        refine ⟨260203430460382591686904727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173468953640255061124603151 260203430460382591686904727)
        ·
          refine ⟨390305145690573887530357091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260203430460382591686904727 390305145690573887530357091)
          ·
            refine ⟨585457718535860831295535637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390305145690573887530357091 585457718535860831295535637)
            ·
              refine ⟨27443330556368476466978233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 585457718535860831295535637 27443330556368476466978233)
              ·
                refine ⟨20582497917276357350233675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27443330556368476466978233 20582497917276357350233675)
                ·
                  refine ⟨30873746875914536025350513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20582497917276357350233675 30873746875914536025350513)
                  ·
                    refine ⟨23155310156935902019012885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30873746875914536025350513 23155310156935902019012885)
                    ·
                      refine ⟨1085405163606370407141229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23155310156935902019012885 1085405163606370407141229)
                      ·
                        rfl

theorem cell23_2113819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 6].length) (baseStart_2113819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113819 prefixEnd_2113819 := by exact prefixLift 2113819
  have htrace : WordTrace (prefixWord ++ tailWord_2113819) baseStart_2113819 baseEnd_2113819 := by
    simpa [prefixWord, tailWord_2113819, baseEnd_2113819] using wordTrace_append hprefix tailTrace_2113819
  have hstable : (prefixWord ++ tailWord_2113819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113819).length < 2 ^ (prefixWord ++ tailWord_2113819).sum := by decide
  have hdescent : baseEnd_2113819 < baseStart_2113819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113854 : List Nat := [4, 2, 1, 2, 1, 4, 2, 2, 1, 4]
def baseStart_2113854 : Nat := 118140960795 + 2113854 * 2 ^ 59
def prefixEnd_2113854 : Nat := 4983230072969 + 3 ^ 40 * 2113854 * 2
def baseEnd_2113854 : Nat := 361807711809759256734523

theorem tailTrace_2113854 : CollatzResearch.WordTrace tailWord_2113854 prefixEnd_2113854 361807711809759256734523 := by
  unfold tailWord_2113854
  simp only [CollatzResearch.WordTrace]
  refine ⟨9637323660484431295779577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51399059522583633577491077 9637323660484431295779577)
  ·
    refine ⟨7227992745363323471834683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9637323660484431295779577 7227992745363323471834683)
    ·
      refine ⟨10841989118044985207752025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7227992745363323471834683 10841989118044985207752025)
      ·
        refine ⟨8131491838533738905814019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10841989118044985207752025 8131491838533738905814019)
        ·
          refine ⟨12197237757800608358721029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8131491838533738905814019 12197237757800608358721029)
          ·
            refine ⟨2286982079587614067260193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12197237757800608358721029 2286982079587614067260193)
            ·
              refine ⟨1715236559690710550445145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2286982079587614067260193 1715236559690710550445145)
              ·
                refine ⟨1286427419768032912833859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1715236559690710550445145 1286427419768032912833859)
                ·
                  refine ⟨1929641129652049369250789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1286427419768032912833859 1929641129652049369250789)
                  ·
                    refine ⟨361807711809759256734523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1929641129652049369250789 361807711809759256734523)
                    ·
                      rfl

theorem cell23_2113854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_2113854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113854 prefixEnd_2113854 := by exact prefixLift 2113854
  have htrace : WordTrace (prefixWord ++ tailWord_2113854) baseStart_2113854 baseEnd_2113854 := by
    simpa [prefixWord, tailWord_2113854, baseEnd_2113854] using wordTrace_append hprefix tailTrace_2113854
  have hstable : (prefixWord ++ tailWord_2113854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113854).length < 2 ^ (prefixWord ++ tailWord_2113854).sum := by decide
  have hdescent : baseEnd_2113854 < baseStart_2113854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113900 : List Nat := [2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 4]
def baseStart_2113900 : Nat := 118140960795 + 2113900 * 2 ^ 59
def prefixEnd_2113900 : Nat := 4983230072969 + 3 ^ 40 * 2113900 * 2
def baseEnd_2113900 : Nat := 1085446755539384590228357

theorem tailTrace_2113900 : CollatzResearch.WordTrace tailWord_2113900 prefixEnd_2113900 1085446755539384590228357 := by
  unfold tailWord_2113900
  simp only [CollatzResearch.WordTrace]
  refine ⟨38550133520854400111205577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51400178027805866814940769 38550133520854400111205577)
  ·
    refine ⟨28912600140640800083404183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38550133520854400111205577 28912600140640800083404183)
    ·
      refine ⟨43368900210961200125106275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28912600140640800083404183 43368900210961200125106275)
      ·
        refine ⟨65053350316441800187659413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43368900210961200125106275 65053350316441800187659413)
        ·
          refine ⟨3049375796083209383796535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65053350316441800187659413 3049375796083209383796535)
          ·
            refine ⟨4574063694124814075694803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3049375796083209383796535 4574063694124814075694803)
            ·
              refine ⟨6861095541187221113542205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4574063694124814075694803 6861095541187221113542205)
              ·
                refine ⟨2572910827945207917578327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6861095541187221113542205 2572910827945207917578327)
                ·
                  refine ⟨3859366241917811876367491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2572910827945207917578327 3859366241917811876367491)
                  ·
                    refine ⟨5789049362876717814551237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3859366241917811876367491 5789049362876717814551237)
                    ·
                      refine ⟨1085446755539384590228357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5789049362876717814551237 1085446755539384590228357)
                      ·
                        rfl

theorem cell23_2113900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 4].length) (baseStart_2113900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113900 prefixEnd_2113900 := by exact prefixLift 2113900
  have htrace : WordTrace (prefixWord ++ tailWord_2113900) baseStart_2113900 baseEnd_2113900 := by
    simpa [prefixWord, tailWord_2113900, baseEnd_2113900] using wordTrace_append hprefix tailTrace_2113900
  have hstable : (prefixWord ++ tailWord_2113900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113900).length < 2 ^ (prefixWord ++ tailWord_2113900).sum := by decide
  have hdescent : baseEnd_2113900 < baseStart_2113900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113906 : List Nat := [3, 2, 1, 2, 1, 4, 10]
def baseStart_2113906 : Nat := 118140960795 + 2113906 * 2 ^ 59
def prefixEnd_2113906 : Nat := 4983230072969 + 3 ^ 40 * 2113906 * 2
def baseEnd_2113906 : Nat := 13400615264485327984609

theorem tailTrace_2113906 : CollatzResearch.WordTrace tailWord_2113906 prefixEnd_2113906 13400615264485327984609 := by
  unfold tailWord_2113906
  simp only [CollatzResearch.WordTrace]
  refine ⟨19275121469921765811782393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51400323919791375498086381 19275121469921765811782393)
  ·
    refine ⟨14456341102441324358836795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19275121469921765811782393 14456341102441324358836795)
    ·
      refine ⟨21684511653661986538255193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14456341102441324358836795 21684511653661986538255193)
      ·
        refine ⟨16263383740246489903691395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21684511653661986538255193 16263383740246489903691395)
        ·
          refine ⟨24395075610369734855537093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16263383740246489903691395 24395075610369734855537093)
          ·
            refine ⟨4574076676944325285413205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24395075610369734855537093 4574076676944325285413205)
            ·
              refine ⟨13400615264485327984609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4574076676944325285413205 13400615264485327984609)
              ·
                rfl

theorem cell23_2113906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 10].length) (baseStart_2113906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113906 prefixEnd_2113906 := by exact prefixLift 2113906
  have htrace : WordTrace (prefixWord ++ tailWord_2113906) baseStart_2113906 baseEnd_2113906 := by
    simpa [prefixWord, tailWord_2113906, baseEnd_2113906] using wordTrace_append hprefix tailTrace_2113906
  have hstable : (prefixWord ++ tailWord_2113906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113906).length < 2 ^ (prefixWord ++ tailWord_2113906).sum := by decide
  have hdescent : baseEnd_2113906 < baseStart_2113906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113917 : List Nat := [1, 4, 1, 1, 2, 4, 2, 1, 3, 2, 2]
def baseStart_2113917 : Nat := 118140960795 + 2113917 * 2 ^ 59
def prefixEnd_2113917 : Nat := 4983230072969 + 3 ^ 40 * 2113917 * 2
def baseEnd_2113917 : Nat := 1085455484710511023715779

theorem tailTrace_2113917 : CollatzResearch.WordTrace tailWord_2113917 prefixEnd_2113917 1085455484710511023715779 := by
  unfold tailWord_2113917
  simp only [CollatzResearch.WordTrace]
  refine ⟨77100887082647212125780005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51400591388431474750520003 77100887082647212125780005)
  ·
    refine ⟨14456416327996352273583751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77100887082647212125780005 14456416327996352273583751)
    ·
      refine ⟨21684624491994528410375627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14456416327996352273583751 21684624491994528410375627)
      ·
        refine ⟨32526936737991792615563441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21684624491994528410375627 32526936737991792615563441)
        ·
          refine ⟨24395202553493844461672581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32526936737991792615563441 24395202553493844461672581)
          ·
            refine ⟨4574100478780095836563609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24395202553493844461672581 4574100478780095836563609)
            ·
              refine ⟨3430575359085071877422707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4574100478780095836563609 3430575359085071877422707)
              ·
                refine ⟨5145863038627607816134061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3430575359085071877422707 5145863038627607816134061)
                ·
                  refine ⟨1929698639485352931050273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5145863038627607816134061 1929698639485352931050273)
                  ·
                    refine ⟨1447273979614014698287705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1929698639485352931050273 1447273979614014698287705)
                    ·
                      refine ⟨1085455484710511023715779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1447273979614014698287705 1085455484710511023715779)
                      ·
                        rfl

theorem cell23_2113917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 2, 2].length) (baseStart_2113917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113917 prefixEnd_2113917 := by exact prefixLift 2113917
  have htrace : WordTrace (prefixWord ++ tailWord_2113917) baseStart_2113917 baseEnd_2113917 := by
    simpa [prefixWord, tailWord_2113917, baseEnd_2113917] using wordTrace_append hprefix tailTrace_2113917
  have hstable : (prefixWord ++ tailWord_2113917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113917).length < 2 ^ (prefixWord ++ tailWord_2113917).sum := by decide
  have hdescent : baseEnd_2113917 < baseStart_2113917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113930 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 1, 1, 6]
def baseStart_2113930 : Nat := 118140960795 + 2113930 * 2 ^ 59
def prefixEnd_2113930 : Nat := 4983230072969 + 3 ^ 40 * 2113930 * 2
def baseEnd_2113930 : Nat := 1085462159959019472853219

theorem tailTrace_2113930 : CollatzResearch.WordTrace tailWord_2113930 prefixEnd_2113930 1085462159959019472853219 := by
  unfold tailWord_2113930
  simp only [CollatzResearch.WordTrace]
  refine ⟨19275340307900028836500811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51400907487733410230668829 19275340307900028836500811)
  ·
    refine ⟨28913010461850043254751217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19275340307900028836500811 28913010461850043254751217)
    ·
      refine ⟨21684757846387532441063413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28913010461850043254751217 21684757846387532441063413)
      ·
        refine ⟨2032946048098831166349695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21684757846387532441063413 2032946048098831166349695)
        ·
          refine ⟨3049419072148246749524543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2032946048098831166349695 3049419072148246749524543)
          ·
            refine ⟨4574128608222370124286815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3049419072148246749524543 4574128608222370124286815)
            ·
              refine ⟨6861192912333555186430223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4574128608222370124286815 6861192912333555186430223)
              ·
                refine ⟨10291789368500332779645335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6861192912333555186430223 10291789368500332779645335)
                ·
                  refine ⟨15437684052750499169468003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10291789368500332779645335 15437684052750499169468003)
                  ·
                    refine ⟨23156526079125748754202005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15437684052750499169468003 23156526079125748754202005)
                    ·
                      refine ⟨1085462159959019472853219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23156526079125748754202005 1085462159959019472853219)
                      ·
                        rfl

theorem cell23_2113930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_2113930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113930 prefixEnd_2113930 := by exact prefixLift 2113930
  have htrace : WordTrace (prefixWord ++ tailWord_2113930) baseStart_2113930 baseEnd_2113930 := by
    simpa [prefixWord, tailWord_2113930, baseEnd_2113930] using wordTrace_append hprefix tailTrace_2113930
  have hstable : (prefixWord ++ tailWord_2113930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113930).length < 2 ^ (prefixWord ++ tailWord_2113930).sum := by decide
  have hdescent : baseEnd_2113930 < baseStart_2113930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113976 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 3, 3, 5]
def baseStart_2113976 : Nat := 118140960795 + 2113976 * 2 ^ 59
def prefixEnd_2113976 : Nat := 4983230072969 + 3 ^ 40 * 2113976 * 2
def baseEnd_2113976 : Nat := 1085485780069126292878007

theorem tailTrace_2113976 : CollatzResearch.WordTrace tailWord_2113976 prefixEnd_2113976 1085485780069126292878007 := by
  unfold tailWord_2113976
  simp only [CollatzResearch.WordTrace]
  refine ⟨38551519494716732601088891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51402025992955643468118521 38551519494716732601088891)
  ·
    refine ⟨57827279242075098901633337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38551519494716732601088891 57827279242075098901633337)
    ·
      refine ⟨43370459431556324176225003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57827279242075098901633337 43370459431556324176225003)
      ·
        refine ⟨65055689147334486264337505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43370459431556324176225003 65055689147334486264337505)
        ·
          refine ⟨48791766860500864698253129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65055689147334486264337505 48791766860500864698253129)
          ·
            refine ⟨36593825145375648523689847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48791766860500864698253129 36593825145375648523689847)
            ·
              refine ⟨54890737718063472785534771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36593825145375648523689847 54890737718063472785534771)
              ·
                refine ⟨82336106577095209178302157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54890737718063472785534771 82336106577095209178302157)
                ·
                  refine ⟨30876039966410703441863309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82336106577095209178302157 30876039966410703441863309)
                  ·
                    refine ⟨11578514987404013790698741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30876039966410703441863309 11578514987404013790698741)
                    ·
                      refine ⟨1085485780069126292878007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11578514987404013790698741 1085485780069126292878007)
                      ·
                        rfl

theorem cell23_2113976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_2113976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2113976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2113976 prefixEnd_2113976 := by exact prefixLift 2113976
  have htrace : WordTrace (prefixWord ++ tailWord_2113976) baseStart_2113976 baseEnd_2113976 := by
    simpa [prefixWord, tailWord_2113976, baseEnd_2113976] using wordTrace_append hprefix tailTrace_2113976
  have hstable : (prefixWord ++ tailWord_2113976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113976).length < 2 ^ (prefixWord ++ tailWord_2113976).sum := by decide
  have hdescent : baseEnd_2113976 < baseStart_2113976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114024 : List Nat := [2, 1, 4, 1, 1, 4, 2, 2, 2, 2, 2]
def baseStart_2114024 : Nat := 118140960795 + 2114024 * 2 ^ 59
def prefixEnd_2114024 : Nat := 4983230072969 + 3 ^ 40 * 2114024 * 2
def baseEnd_2114024 : Nat := 1085510427140542105077787

theorem tailTrace_2114024 : CollatzResearch.WordTrace tailWord_2114024 prefixEnd_2114024 1085510427140542105077787 := by
  unfold tailWord_2114024
  simp only [CollatzResearch.WordTrace]
  refine ⟨38552394846629784699962563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51403193128839712933283417 38552394846629784699962563)
  ·
    refine ⟨57828592269944677049943845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38552394846629784699962563 57828592269944677049943845)
    ·
      refine ⟨10842861050614626946864471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57828592269944677049943845 10842861050614626946864471)
      ·
        refine ⟨16264291575921940420296707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10842861050614626946864471 16264291575921940420296707)
        ·
          refine ⟨24396437363882910630445061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16264291575921940420296707 24396437363882910630445061)
          ·
            refine ⟨4574332005728045743208449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24396437363882910630445061 4574332005728045743208449)
            ·
              refine ⟨3430749004296034307406337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4574332005728045743208449 3430749004296034307406337)
              ·
                refine ⟨2573061753222025730554753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3430749004296034307406337 2573061753222025730554753)
                ·
                  refine ⟨1929796314916519297916065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2573061753222025730554753 1929796314916519297916065)
                  ·
                    refine ⟨1447347236187389473437049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1929796314916519297916065 1447347236187389473437049)
                    ·
                      refine ⟨1085510427140542105077787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1447347236187389473437049 1085510427140542105077787)
                      ·
                        rfl

theorem cell23_2114024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_2114024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114024 prefixEnd_2114024 := by exact prefixLift 2114024
  have htrace : WordTrace (prefixWord ++ tailWord_2114024) baseStart_2114024 baseEnd_2114024 := by
    simpa [prefixWord, tailWord_2114024, baseEnd_2114024] using wordTrace_append hprefix tailTrace_2114024
  have hstable : (prefixWord ++ tailWord_2114024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114024).length < 2 ^ (prefixWord ++ tailWord_2114024).sum := by decide
  have hdescent : baseEnd_2114024 < baseStart_2114024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114037 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_2114037 : Nat := 118140960795 + 2114037 * 2 ^ 59
def prefixEnd_2114037 : Nat := 4983230072969 + 3 ^ 40 * 2114037 * 2
def baseEnd_2114037 : Nat := 1085517102389050554215227

theorem tailTrace_2114037 : CollatzResearch.WordTrace tailWord_2114037 prefixEnd_2114037 1085517102389050554215227 := by
  unfold tailWord_2114037
  simp only [CollatzResearch.WordTrace]
  refine ⟨77105263842212472620148365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51403509228141648413432243 77105263842212472620148365)
  ·
    refine ⟨28914473940829677232555637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77105263842212472620148365 28914473940829677232555637)
    ·
      refine ⟨2710731931952782240552091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28914473940829677232555637 2710731931952782240552091)
      ·
        refine ⟨4066097897929173360828137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2710731931952782240552091 4066097897929173360828137)
        ·
          refine ⟨3049573423446880020621103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4066097897929173360828137 3049573423446880020621103)
          ·
            refine ⟨4574360135170320030931655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3049573423446880020621103 4574360135170320030931655)
            ·
              refine ⟨6861540202755480046397483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4574360135170320030931655 6861540202755480046397483)
              ·
                refine ⟨10292310304133220069596225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6861540202755480046397483 10292310304133220069596225)
                ·
                  refine ⟨7719232728099915052197169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10292310304133220069596225 7719232728099915052197169)
                  ·
                    refine ⟨5789424546074936289147877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7719232728099915052197169 5789424546074936289147877)
                    ·
                      refine ⟨1085517102389050554215227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5789424546074936289147877 1085517102389050554215227)
                      ·
                        rfl

theorem cell23_2114037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_2114037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114037 prefixEnd_2114037 := by exact prefixLift 2114037
  have htrace : WordTrace (prefixWord ++ tailWord_2114037) baseStart_2114037 baseEnd_2114037 := by
    simpa [prefixWord, tailWord_2114037, baseEnd_2114037] using wordTrace_append hprefix tailTrace_2114037
  have hstable : (prefixWord ++ tailWord_2114037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114037).length < 2 ^ (prefixWord ++ tailWord_2114037).sum := by decide
  have hdescent : baseEnd_2114037 < baseStart_2114037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114060 : List Nat := [2, 2, 1, 2, 4, 1, 3, 1, 2, 5]
def baseStart_2114060 : Nat := 118140960795 + 2114060 * 2 ^ 59
def prefixEnd_2114060 : Nat := 4983230072969 + 3 ^ 40 * 2114060 * 2
def baseEnd_2114060 : Nat := 361842970814701321409207

theorem tailTrace_2114060 : CollatzResearch.WordTrace tailWord_2114060 prefixEnd_2114060 361842970814701321409207 := by
  unfold tailWord_2114060
  simp only [CollatzResearch.WordTrace]
  refine ⟨38553051360564573774117817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51404068480752765032157089 38553051360564573774117817)
  ·
    refine ⟨28914788520423430330588363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38553051360564573774117817 28914788520423430330588363)
    ·
      refine ⟨43372182780635145495882545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28914788520423430330588363 43372182780635145495882545)
      ·
        refine ⟨32529137085476359121911909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43372182780635145495882545 32529137085476359121911909)
        ·
          refine ⟨6099213203526817335358483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32529137085476359121911909 6099213203526817335358483)
          ·
            refine ⟨9148819805290226003037725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6099213203526817335358483 9148819805290226003037725)
            ·
              refine ⟨3430807426983834751139147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9148819805290226003037725 3430807426983834751139147)
              ·
                refine ⟨5146211140475752126708721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3430807426983834751139147 5146211140475752126708721)
                ·
                  refine ⟨3859658355356814095031541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5146211140475752126708721 3859658355356814095031541)
                  ·
                    refine ⟨361842970814701321409207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3859658355356814095031541 361842970814701321409207)
                    ·
                      rfl

theorem cell23_2114060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 2, 5].length) (baseStart_2114060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114060 prefixEnd_2114060 := by exact prefixLift 2114060
  have htrace : WordTrace (prefixWord ++ tailWord_2114060) baseStart_2114060 baseEnd_2114060 := by
    simpa [prefixWord, tailWord_2114060, baseEnd_2114060] using wordTrace_append hprefix tailTrace_2114060
  have hstable : (prefixWord ++ tailWord_2114060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114060).length < 2 ^ (prefixWord ++ tailWord_2114060).sum := by decide
  have hdescent : baseEnd_2114060 < baseStart_2114060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114153 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 2, 5, 4]
def baseStart_2114153 : Nat := 118140960795 + 2114153 * 2 ^ 59
def prefixEnd_2114153 : Nat := 4983230072969 + 3 ^ 40 * 2114153 * 2
def baseEnd_2114153 : Nat := 1085576666144972100364693

theorem tailTrace_2114153 : CollatzResearch.WordTrace tailWord_2114153 prefixEnd_2114153 1085576666144972100364693 := by
  unfold tailWord_2114153
  simp only [CollatzResearch.WordTrace]
  refine ⟨77109494709792224431371113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51406329806528149620914075 77109494709792224431371113)
  ·
    refine ⟨57832121032344168323528335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77109494709792224431371113 57832121032344168323528335)
    ·
      refine ⟨86748181548516252485292503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57832121032344168323528335 86748181548516252485292503)
      ·
        refine ⟨130122272322774378727938755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86748181548516252485292503 130122272322774378727938755)
        ·
          refine ⟨195183408484161568091908133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130122272322774378727938755 195183408484161568091908133)
          ·
            refine ⟨36596889090780294017232775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 195183408484161568091908133 36596889090780294017232775)
            ·
              refine ⟨54895333636170441025849163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36596889090780294017232775 54895333636170441025849163)
              ·
                refine ⟨82343000454255661538773745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54895333636170441025849163 82343000454255661538773745)
                ·
                  refine ⟨61757250340691746154080309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82343000454255661538773745 61757250340691746154080309)
                  ·
                    refine ⟨5789742219439851201945029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61757250340691746154080309 5789742219439851201945029)
                    ·
                      refine ⟨1085576666144972100364693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5789742219439851201945029 1085576666144972100364693)
                      ·
                        rfl

theorem cell23_2114153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 5, 4].length) (baseStart_2114153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114153 prefixEnd_2114153 := by exact prefixLift 2114153
  have htrace : WordTrace (prefixWord ++ tailWord_2114153) baseStart_2114153 baseEnd_2114153 := by
    simpa [prefixWord, tailWord_2114153, baseEnd_2114153] using wordTrace_append hprefix tailTrace_2114153
  have hstable : (prefixWord ++ tailWord_2114153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114153).length < 2 ^ (prefixWord ++ tailWord_2114153).sum := by decide
  have hdescent : baseEnd_2114153 < baseStart_2114153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114180 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 3, 6]
def baseStart_2114180 : Nat := 118140960795 + 2114180 * 2 ^ 59
def prefixEnd_2114180 : Nat := 4983230072969 + 3 ^ 40 * 2114180 * 2
def baseEnd_2114180 : Nat := 361863510040881164909023

theorem tailTrace_2114180 : CollatzResearch.WordTrace tailWord_2114180 prefixEnd_2114180 361863510040881164909023 := by
  unfold tailWord_2114180
  simp only [CollatzResearch.WordTrace]
  refine ⟨38555239740347204021301997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51406986320462938695069329 38555239740347204021301997)
  ·
    refine ⟨14458214902630201507988249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38555239740347204021301997 14458214902630201507988249)
    ·
      refine ⟨10843661176972651130991187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14458214902630201507988249 10843661176972651130991187)
      ·
        refine ⟨16265491765458976696486781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10843661176972651130991187 16265491765458976696486781)
        ·
          refine ⟨6099559412047116261182543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16265491765458976696486781 6099559412047116261182543)
          ·
            refine ⟨9149339118070674391773815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6099559412047116261182543 9149339118070674391773815)
            ·
              refine ⟨13724008677106011587660723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9149339118070674391773815 13724008677106011587660723)
              ·
                refine ⟨20586013015659017381491085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13724008677106011587660723 20586013015659017381491085)
                ·
                  refine ⟨7719754880872131518059157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20586013015659017381491085 7719754880872131518059157)
                  ·
                    refine ⟨361863510040881164909023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7719754880872131518059157 361863510040881164909023)
                    ·
                      rfl

theorem cell23_2114180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_2114180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114180 prefixEnd_2114180 := by exact prefixLift 2114180
  have htrace : WordTrace (prefixWord ++ tailWord_2114180) baseStart_2114180 baseEnd_2114180 := by
    simpa [prefixWord, tailWord_2114180, baseEnd_2114180] using wordTrace_append hprefix tailTrace_2114180
  have hstable : (prefixWord ++ tailWord_2114180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114180).length < 2 ^ (prefixWord ++ tailWord_2114180).sum := by decide
  have hdescent : baseEnd_2114180 < baseStart_2114180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114187 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 7, 2, 2]
def baseStart_2114187 : Nat := 118140960795 + 2114187 * 2 ^ 59
def prefixEnd_2114187 : Nat := 4983230072969 + 3 ^ 40 * 2114187 * 2
def baseEnd_2114187 : Nat := 1085594124487224967339537

theorem tailTrace_2114187 : CollatzResearch.WordTrace tailWord_2114187 prefixEnd_2114187 1085594124487224967339537 := by
  unfold tailWord_2114187
  simp only [CollatzResearch.WordTrace]
  refine ⟨77110734791669048238108815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51407156527779365492072543 77110734791669048238108815)
  ·
    refine ⟨115666102187503572357163223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77110734791669048238108815 115666102187503572357163223)
    ·
      refine ⟨173499153281255358535744835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115666102187503572357163223 173499153281255358535744835)
      ·
        refine ⟨260248729921883037803617253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173499153281255358535744835 260248729921883037803617253)
        ·
          refine ⟨48796636860353069588178235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 260248729921883037803617253 48796636860353069588178235)
          ·
            refine ⟨73194955290529604382267353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48796636860353069588178235 73194955290529604382267353)
            ·
              refine ⟨54896216467897203286700515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73194955290529604382267353 54896216467897203286700515)
              ·
                refine ⟨82344324701845804930050773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54896216467897203286700515 82344324701845804930050773)
                ·
                  refine ⟨1929945110199511053048065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 82344324701845804930050773 1929945110199511053048065)
                  ·
                    refine ⟨1447458832649633289786049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1929945110199511053048065 1447458832649633289786049)
                    ·
                      refine ⟨1085594124487224967339537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1447458832649633289786049 1085594124487224967339537)
                      ·
                        rfl

theorem cell23_2114187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 2, 2].length) (baseStart_2114187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114187 prefixEnd_2114187 := by exact prefixLift 2114187
  have htrace : WordTrace (prefixWord ++ tailWord_2114187) baseStart_2114187 baseEnd_2114187 := by
    simpa [prefixWord, tailWord_2114187, baseEnd_2114187] using wordTrace_append hprefix tailTrace_2114187
  have hstable : (prefixWord ++ tailWord_2114187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114187).length < 2 ^ (prefixWord ++ tailWord_2114187).sum := by decide
  have hdescent : baseEnd_2114187 < baseStart_2114187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114200 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 3, 2, 4]
def baseStart_2114200 : Nat := 118140960795 + 2114200 * 2 ^ 59
def prefixEnd_2114200 : Nat := 4983230072969 + 3 ^ 40 * 2114200 * 2
def baseEnd_2114200 : Nat := 1085600799735733416476977

theorem tailTrace_2114200 : CollatzResearch.WordTrace tailWord_2114200 prefixEnd_2114200 1085600799735733416476977 := by
  unfold tailWord_2114200
  simp only [CollatzResearch.WordTrace]
  refine ⟨38555604470310975729166027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51407472627081300972221369 38555604470310975729166027)
  ·
    refine ⟨57833406705466463593749041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38555604470310975729166027 57833406705466463593749041)
    ·
      refine ⟨43375055029099847695311781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57833406705466463593749041 43375055029099847695311781)
      ·
        refine ⟨8132822817956221442870959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43375055029099847695311781 8132822817956221442870959)
        ·
          refine ⟨12199234226934332164306439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8132822817956221442870959 12199234226934332164306439)
          ·
            refine ⟨18298851340401498246459659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12199234226934332164306439 18298851340401498246459659)
            ·
              refine ⟨27448277010602247369689489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18298851340401498246459659 27448277010602247369689489)
              ·
                refine ⟨20586207757951685527267117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27448277010602247369689489 20586207757951685527267117)
                ·
                  refine ⟨7719827909231882072725169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20586207757951685527267117 7719827909231882072725169)
                  ·
                    refine ⟨5789870931923911554543877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7719827909231882072725169 5789870931923911554543877)
                    ·
                      refine ⟨1085600799735733416476977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5789870931923911554543877 1085600799735733416476977)
                      ·
                        rfl

theorem cell23_2114200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_2114200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114200 prefixEnd_2114200 := by exact prefixLift 2114200
  have htrace : WordTrace (prefixWord ++ tailWord_2114200) baseStart_2114200 baseEnd_2114200 := by
    simpa [prefixWord, tailWord_2114200, baseEnd_2114200] using wordTrace_append hprefix tailTrace_2114200
  have hstable : (prefixWord ++ tailWord_2114200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114200).length < 2 ^ (prefixWord ++ tailWord_2114200).sum := by decide
  have hdescent : baseEnd_2114200 < baseStart_2114200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114221 : List Nat := [1, 5, 2, 1, 1, 3, 1, 2, 3, 2, 2]
def baseStart_2114221 : Nat := 118140960795 + 2114221 * 2 ^ 59
def prefixEnd_2114221 : Nat := 4983230072969 + 3 ^ 40 * 2114221 * 2
def baseEnd_2114221 : Nat := 1085611582829477834314381

theorem tailTrace_2114221 : CollatzResearch.WordTrace tailWord_2114221 prefixEnd_2114221 1085611582829477834314381 := by
  unfold tailWord_2114221
  simp only [CollatzResearch.WordTrace]
  refine ⟨77111974873545872044846517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51407983249030581363231011 77111974873545872044846517)
  ·
    refine ⟨7229247644394925504204361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77111974873545872044846517 7229247644394925504204361)
    ·
      refine ⟨5421935733296194128153271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7229247644394925504204361 5421935733296194128153271)
      ·
        refine ⟨8132903599944291192229907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5421935733296194128153271 8132903599944291192229907)
        ·
          refine ⟨12199355399916436788344861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8132903599944291192229907 12199355399916436788344861)
          ·
            refine ⟨4574758274968663795629323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12199355399916436788344861 4574758274968663795629323)
            ·
              refine ⟨6862137412452995693443985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4574758274968663795629323 6862137412452995693443985)
              ·
                refine ⟨5146603059339746770082989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6862137412452995693443985 5146603059339746770082989)
                ·
                  refine ⟨1929976147252405038781121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5146603059339746770082989 1929976147252405038781121)
                  ·
                    refine ⟨1447482110439303779085841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1929976147252405038781121 1447482110439303779085841)
                    ·
                      refine ⟨1085611582829477834314381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1447482110439303779085841 1085611582829477834314381)
                      ·
                        rfl

theorem cell23_2114221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_2114221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114221 prefixEnd_2114221 := by exact prefixLift 2114221
  have htrace : WordTrace (prefixWord ++ tailWord_2114221) baseStart_2114221 baseEnd_2114221 := by
    simpa [prefixWord, tailWord_2114221, baseEnd_2114221] using wordTrace_append hprefix tailTrace_2114221
  have hstable : (prefixWord ++ tailWord_2114221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114221).length < 2 ^ (prefixWord ++ tailWord_2114221).sum := by decide
  have hdescent : baseEnd_2114221 < baseStart_2114221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114237 : List Nat := [1, 4, 1, 2, 1, 3, 2, 2, 1, 3, 3]
def baseStart_2114237 : Nat := 118140960795 + 2114237 * 2 ^ 59
def prefixEnd_2114237 : Nat := 4983230072969 + 3 ^ 40 * 2114237 * 2
def baseEnd_2114237 : Nat := 1085619798519949771714307

theorem tailTrace_2114237 : CollatzResearch.WordTrace tailWord_2114237 prefixEnd_2114237 1085619798519949771714307 := by
  unfold tailWord_2114237
  simp only [CollatzResearch.WordTrace]
  refine ⟨77112558441487906777428965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51408372294325271184952643 77112558441487906777428965)
  ·
    refine ⟨14458604707778982520767931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77112558441487906777428965 14458604707778982520767931)
    ·
      refine ⟨21687907061668473781151897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14458604707778982520767931 21687907061668473781151897)
      ·
        refine ⟨16265930296251355335863923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21687907061668473781151897 16265930296251355335863923)
        ·
          refine ⟨24398895444377033003795885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16265930296251355335863923 24398895444377033003795885)
          ·
            refine ⟨9149585791641387376423457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24398895444377033003795885 9149585791641387376423457)
            ·
              refine ⟨6862189343731040532317593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9149585791641387376423457 6862189343731040532317593)
              ·
                refine ⟨5146642007798280399238195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6862189343731040532317593 5146642007798280399238195)
                ·
                  refine ⟨7719963011697420598857293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5146642007798280399238195 7719963011697420598857293)
                  ·
                    refine ⟨2894986129386532724571485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7719963011697420598857293 2894986129386532724571485)
                    ·
                      refine ⟨1085619798519949771714307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2894986129386532724571485 1085619798519949771714307)
                      ·
                        rfl

theorem cell23_2114237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_2114237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114237 prefixEnd_2114237 := by exact prefixLift 2114237
  have htrace : WordTrace (prefixWord ++ tailWord_2114237) baseStart_2114237 baseEnd_2114237 := by
    simpa [prefixWord, tailWord_2114237, baseEnd_2114237] using wordTrace_append hprefix tailTrace_2114237
  have hstable : (prefixWord ++ tailWord_2114237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114237).length < 2 ^ (prefixWord ++ tailWord_2114237).sum := by decide
  have hdescent : baseEnd_2114237 < baseStart_2114237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114238 : List Nat := [4, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2]
def baseStart_2114238 : Nat := 118140960795 + 2114238 * 2 ^ 59
def prefixEnd_2114238 : Nat := 4983230072969 + 3 ^ 40 * 2114238 * 2
def baseEnd_2114238 : Nat := 1085620312000604267801803

theorem tailTrace_2114238 : CollatzResearch.WordTrace tailWord_2114238 prefixEnd_2114238 1085620312000604267801803 := by
  unfold tailWord_2114238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9639074364310535493526921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51408396609656189298810245 9639074364310535493526921)
  ·
    refine ⟨7229305773232901620145191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9639074364310535493526921 7229305773232901620145191)
    ·
      refine ⟨10843958659849352430217787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7229305773232901620145191 10843958659849352430217787)
      ·
        refine ⟨16265937989774028645326681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10843958659849352430217787 16265937989774028645326681)
        ·
          refine ⟨12199453492330521483995011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16265937989774028645326681 12199453492330521483995011)
          ·
            refine ⟨18299180238495782225992517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12199453492330521483995011 18299180238495782225992517)
            ·
              refine ⟨3431096294717959167373597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18299180238495782225992517 3431096294717959167373597)
              ·
                refine ⟨1286661110519234687765099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3431096294717959167373597 1286661110519234687765099)
                ·
                  refine ⟨1929991665778852031647649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1286661110519234687765099 1929991665778852031647649)
                  ·
                    refine ⟨1447493749334139023735737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1929991665778852031647649 1447493749334139023735737)
                    ·
                      refine ⟨1085620312000604267801803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1447493749334139023735737 1085620312000604267801803)
                      ·
                        rfl

theorem cell23_2114238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_2114238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114238 prefixEnd_2114238 := by exact prefixLift 2114238
  have htrace : WordTrace (prefixWord ++ tailWord_2114238) baseStart_2114238 baseEnd_2114238 := by
    simpa [prefixWord, tailWord_2114238, baseEnd_2114238] using wordTrace_append hprefix tailTrace_2114238
  have hstable : (prefixWord ++ tailWord_2114238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114238).length < 2 ^ (prefixWord ++ tailWord_2114238).sum := by decide
  have hdescent : baseEnd_2114238 < baseStart_2114238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114247 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 5, 3, 2]
def baseStart_2114247 : Nat := 118140960795 + 2114247 * 2 ^ 59
def prefixEnd_2114247 : Nat := 4983230072969 + 3 ^ 40 * 2114247 * 2
def baseEnd_2114247 : Nat := 1085624933326494732589261

theorem tailTrace_2114247 : CollatzResearch.WordTrace tailWord_2114247 prefixEnd_2114247 1085624933326494732589261 := by
  unfold tailWord_2114247
  simp only [CollatzResearch.WordTrace]
  refine ⟨77112923171451678485292995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51408615447634452323528663 77112923171451678485292995)
  ·
    refine ⟨115669384757177517727939493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77112923171451678485292995 115669384757177517727939493)
    ·
      refine ⟨21688009641970784573988655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115669384757177517727939493 21688009641970784573988655)
      ·
        refine ⟨32532014462956176860982983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21688009641970784573988655 32532014462956176860982983)
        ·
          refine ⟨48798021694434265291474475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32532014462956176860982983 48798021694434265291474475)
          ·
            refine ⟨73197032541651397937211713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48798021694434265291474475 73197032541651397937211713)
            ·
              refine ⟨54897774406238548452908785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73197032541651397937211713 54897774406238548452908785)
              ·
                refine ⟨41173330804678911339681589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54897774406238548452908785 41173330804678911339681589)
                ·
                  refine ⟨3859999762938647938095149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41173330804678911339681589 3859999762938647938095149)
                  ·
                    refine ⟨1447499911101992976785681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3859999762938647938095149 1447499911101992976785681)
                    ·
                      refine ⟨1085624933326494732589261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1447499911101992976785681 1085624933326494732589261)
                      ·
                        rfl

theorem cell23_2114247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 3, 2].length) (baseStart_2114247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114247 prefixEnd_2114247 := by exact prefixLift 2114247
  have htrace : WordTrace (prefixWord ++ tailWord_2114247) baseStart_2114247 baseEnd_2114247 := by
    simpa [prefixWord, tailWord_2114247, baseEnd_2114247] using wordTrace_append hprefix tailTrace_2114247
  have hstable : (prefixWord ++ tailWord_2114247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114247).length < 2 ^ (prefixWord ++ tailWord_2114247).sum := by decide
  have hdescent : baseEnd_2114247 < baseStart_2114247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114254 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3]
def baseStart_2114254 : Nat := 118140960795 + 2114254 * 2 ^ 59
def prefixEnd_2114254 : Nat := 4983230072969 + 3 ^ 40 * 2114254 * 2
def baseEnd_2114254 : Nat := 1085628527691076205201729

theorem tailTrace_2114254 : CollatzResearch.WordTrace tailWord_2114254 prefixEnd_2114254 1085628527691076205201729 := by
  unfold tailWord_2114254
  simp only [CollatzResearch.WordTrace]
  refine ⟨9639147310303289835099727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51408785654950879120531877 9639147310303289835099727)
  ·
    refine ⟨14458720965454934752649591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9639147310303289835099727 14458720965454934752649591)
    ·
      refine ⟨21688081448182402128974387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14458720965454934752649591 21688081448182402128974387)
      ·
        refine ⟨32532122172273603193461581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21688081448182402128974387 32532122172273603193461581)
        ·
          refine ⟨12199545814602601197548093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32532122172273603193461581 12199545814602601197548093)
          ·
            refine ⟨4574829680475975449080535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12199545814602601197548093 4574829680475975449080535)
            ·
              refine ⟨6862244520713963173620803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4574829680475975449080535 6862244520713963173620803)
              ·
                refine ⟨10293366781070944760431205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6862244520713963173620803 10293366781070944760431205)
                ·
                  refine ⟨1930006271450802142580851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10293366781070944760431205 1930006271450802142580851)
                  ·
                    refine ⟨2895009407176203213871277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1930006271450802142580851 2895009407176203213871277)
                    ·
                      refine ⟨1085628527691076205201729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2895009407176203213871277 1085628527691076205201729)
                      ·
                        rfl

theorem cell23_2114254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_2114254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114254 prefixEnd_2114254 := by exact prefixLift 2114254
  have htrace : WordTrace (prefixWord ++ tailWord_2114254) baseStart_2114254 baseEnd_2114254 := by
    simpa [prefixWord, tailWord_2114254, baseEnd_2114254] using wordTrace_append hprefix tailTrace_2114254
  have hstable : (prefixWord ++ tailWord_2114254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114254).length < 2 ^ (prefixWord ++ tailWord_2114254).sum := by decide
  have hdescent : baseEnd_2114254 < baseStart_2114254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114271 : List Nat := [1, 1, 2, 3, 2, 4, 3, 1, 2, 1, 3]
def baseStart_2114271 : Nat := 118140960795 + 2114271 * 2 ^ 59
def prefixEnd_2114271 : Nat := 4983230072969 + 3 ^ 40 * 2114271 * 2
def baseEnd_2114271 : Nat := 1085637256862202638689151

theorem tailTrace_2114271 : CollatzResearch.WordTrace tailWord_2114271 prefixEnd_2114271 1085637256862202638689151 := by
  unfold tailWord_2114271
  simp only [CollatzResearch.WordTrace]
  refine ⟨77113798523364730584166667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51409199015576487056111111 77113798523364730584166667)
  ·
    refine ⟨115670697785047095876250001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77113798523364730584166667 115670697785047095876250001)
    ·
      refine ⟨86753023338785321907187501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115670697785047095876250001 86753023338785321907187501)
      ·
        refine ⟨32532383752044495715195313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86753023338785321907187501 32532383752044495715195313)
        ·
          refine ⟨24399287814033371786396485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32532383752044495715195313 24399287814033371786396485)
          ·
            refine ⟨4574866465131257209949341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24399287814033371786396485 4574866465131257209949341)
            ·
              refine ⟨1715574924424221453731003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4574866465131257209949341 1715574924424221453731003)
              ·
                refine ⟨2573362386636332180596505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1715574924424221453731003 2573362386636332180596505)
                ·
                  refine ⟨1930021789977249135447379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2573362386636332180596505 1930021789977249135447379)
                  ·
                    refine ⟨2895032684965873703171069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1930021789977249135447379 2895032684965873703171069)
                    ·
                      refine ⟨1085637256862202638689151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2895032684965873703171069 1085637256862202638689151)
                      ·
                        rfl

theorem cell23_2114271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 2, 1, 3].length) (baseStart_2114271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114271 prefixEnd_2114271 := by exact prefixLift 2114271
  have htrace : WordTrace (prefixWord ++ tailWord_2114271) baseStart_2114271 baseEnd_2114271 := by
    simpa [prefixWord, tailWord_2114271, baseEnd_2114271] using wordTrace_append hprefix tailTrace_2114271
  have hstable : (prefixWord ++ tailWord_2114271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114271).length < 2 ^ (prefixWord ++ tailWord_2114271).sum := by decide
  have hdescent : baseEnd_2114271 < baseStart_2114271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114294 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2]
def baseStart_2114294 : Nat := 118140960795 + 2114294 * 2 ^ 59
def prefixEnd_2114294 : Nat := 4983230072969 + 3 ^ 40 * 2114294 * 2
def baseEnd_2114294 : Nat := 1085649066917256048701545

theorem tailTrace_2114294 : CollatzResearch.WordTrace tailWord_2114294 prefixEnd_2114294 1085649066917256048701545 := by
  unfold tailWord_2114294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4819664837642587844515871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51409758268187603674835957 4819664837642587844515871)
  ·
    refine ⟨7229497256463881766773807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4819664837642587844515871 7229497256463881766773807)
    ·
      refine ⟨10844245884695822650160711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7229497256463881766773807 10844245884695822650160711)
      ·
        refine ⟨16266368827043733975241067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10844245884695822650160711 16266368827043733975241067)
        ·
          refine ⟨24399553240565600962861601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16266368827043733975241067 24399553240565600962861601)
          ·
            refine ⟨18299664930424200722146201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24399553240565600962861601 18299664930424200722146201)
            ·
              refine ⟨13724748697818150541609651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18299664930424200722146201 13724748697818150541609651)
              ·
                refine ⟨20587123046727225812414477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13724748697818150541609651 20587123046727225812414477)
                ·
                  refine ⟨7720171142522709679655429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20587123046727225812414477 7720171142522709679655429)
                  ·
                    refine ⟨1447532089223008064935393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7720171142522709679655429 1447532089223008064935393)
                    ·
                      refine ⟨1085649066917256048701545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1447532089223008064935393 1085649066917256048701545)
                      ·
                        rfl

theorem cell23_2114294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_2114294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114294 prefixEnd_2114294 := by exact prefixLift 2114294
  have htrace : WordTrace (prefixWord ++ tailWord_2114294) baseStart_2114294 baseEnd_2114294 := by
    simpa [prefixWord, tailWord_2114294, baseEnd_2114294] using wordTrace_append hprefix tailTrace_2114294
  have hstable : (prefixWord ++ tailWord_2114294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114294).length < 2 ^ (prefixWord ++ tailWord_2114294).sum := by decide
  have hdescent : baseEnd_2114294 < baseStart_2114294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114311 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 4, 2, 2]
def baseStart_2114311 : Nat := 118140960795 + 2114311 * 2 ^ 59
def prefixEnd_2114311 : Nat := 4983230072969 + 3 ^ 40 * 2114311 * 2
def baseEnd_2114311 : Nat := 1085657796088382482188967

theorem tailTrace_2114311 : CollatzResearch.WordTrace tailWord_2114311 prefixEnd_2114311 1085657796088382482188967 := by
  unfold tailWord_2114311
  simp only [CollatzResearch.WordTrace]
  refine ⟨77115257443219817415622787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51410171628813211610415191 77115257443219817415622787)
  ·
    refine ⟨115672886164829726123434181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77115257443219817415622787 115672886164829726123434181)
    ·
      refine ⟨21688666155905573648143909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115672886164829726123434181 21688666155905573648143909)
      ·
        refine ⟨4066624904232295059026983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21688666155905573648143909 4066624904232295059026983)
        ·
          refine ⟨6099937356348442588540475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4066624904232295059026983 6099937356348442588540475)
          ·
            refine ⟨9149906034522663882810713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6099937356348442588540475 9149906034522663882810713)
            ·
              refine ⟨6862429525891997912108035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9149906034522663882810713 6862429525891997912108035)
              ·
                refine ⟨10293644288837996868162053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6862429525891997912108035 10293644288837996868162053)
                ·
                  refine ⟨1930058304157124412780385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10293644288837996868162053 1930058304157124412780385)
                  ·
                    refine ⟨1447543728117843309585289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1930058304157124412780385 1447543728117843309585289)
                    ·
                      refine ⟨1085657796088382482188967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1447543728117843309585289 1085657796088382482188967)
                      ·
                        rfl

theorem cell23_2114311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_2114311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114311 prefixEnd_2114311 := by exact prefixLift 2114311
  have htrace : WordTrace (prefixWord ++ tailWord_2114311) baseStart_2114311 baseEnd_2114311 := by
    simpa [prefixWord, tailWord_2114311, baseEnd_2114311] using wordTrace_append hprefix tailTrace_2114311
  have hstable : (prefixWord ++ tailWord_2114311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114311).length < 2 ^ (prefixWord ++ tailWord_2114311).sum := by decide
  have hdescent : baseEnd_2114311 < baseStart_2114311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114322 : List Nat := [3, 2, 4, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_2114322 : Nat := 118140960795 + 2114322 * 2 ^ 59
def prefixEnd_2114322 : Nat := 4983230072969 + 3 ^ 40 * 2114322 * 2
def baseEnd_2114322 : Nat := 1085663444375581939151417

theorem tailTrace_2114322 : CollatzResearch.WordTrace tailWord_2114322 prefixEnd_2114322 1085663444375581939151417 := by
  unfold tailWord_2114322
  simp only [CollatzResearch.WordTrace]
  refine ⟨19278914661544991573568305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51410439097453310862848813 19278914661544991573568305)
  ·
    refine ⟨14459185996158743680176229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19278914661544991573568305 14459185996158743680176229)
    ·
      refine ⟨2711097374279764440033043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14459185996158743680176229 2711097374279764440033043)
      ·
        refine ⟨4066646061419646660049565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2711097374279764440033043 4066646061419646660049565)
        ·
          refine ⟨1524992273032367497518587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4066646061419646660049565 1524992273032367497518587)
          ·
            refine ⟨2287488409548551246277881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1524992273032367497518587 2287488409548551246277881)
            ·
              refine ⟨1715616307161413434708411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2287488409548551246277881 1715616307161413434708411)
              ·
                refine ⟨2573424460742120152062617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1715616307161413434708411 2573424460742120152062617)
                ·
                  refine ⟨1930068345556590114046963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2573424460742120152062617 1930068345556590114046963)
                  ·
                    refine ⟨2895102518334885171070445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1930068345556590114046963 2895102518334885171070445)
                    ·
                      refine ⟨1085663444375581939151417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2895102518334885171070445 1085663444375581939151417)
                      ·
                        rfl

theorem cell23_2114322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_2114322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114322 prefixEnd_2114322 := by exact prefixLift 2114322
  have htrace : WordTrace (prefixWord ++ tailWord_2114322) baseStart_2114322 baseEnd_2114322 := by
    simpa [prefixWord, tailWord_2114322, baseEnd_2114322] using wordTrace_append hprefix tailTrace_2114322
  have hstable : (prefixWord ++ tailWord_2114322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114322).length < 2 ^ (prefixWord ++ tailWord_2114322).sum := by decide
  have hdescent : baseEnd_2114322 < baseStart_2114322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114357 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_2114357 : Nat := 118140960795 + 2114357 * 2 ^ 59
def prefixEnd_2114357 : Nat := 4983230072969 + 3 ^ 40 * 2114357 * 2
def baseEnd_2114357 : Nat := 1085681416198489302213755

theorem tailTrace_2114357 : CollatzResearch.WordTrace tailWord_2114357 prefixEnd_2114357 1085681416198489302213755 := by
  unfold tailWord_2114357
  simp only [CollatzResearch.WordTrace]
  refine ⟨77116935201053167271797325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51411290134035444847864883 77116935201053167271797325)
  ·
    refine ⟨28918850700394937726923997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77116935201053167271797325 28918850700394937726923997)
    ·
      refine ⟨10844569012648101647596499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28918850700394937726923997 10844569012648101647596499)
      ·
        refine ⟨16266853518972152471394749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10844569012648101647596499 16266853518972152471394749)
        ·
          refine ⟨6100070069614557176773031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16266853518972152471394749 6100070069614557176773031)
          ·
            refine ⟨9150105104421835765159547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6100070069614557176773031 9150105104421835765159547)
            ·
              refine ⟨13725157656632753647739321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9150105104421835765159547 13725157656632753647739321)
              ·
                refine ⟨10293868242474565235804491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13725157656632753647739321 10293868242474565235804491)
                ·
                  refine ⟨15440802363711847853706737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10293868242474565235804491 15440802363711847853706737)
                  ·
                    refine ⟨11580601772783885890280053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15440802363711847853706737 11580601772783885890280053)
                    ·
                      refine ⟨1085681416198489302213755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11580601772783885890280053 1085681416198489302213755)
                      ·
                        rfl

theorem cell23_2114357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_2114357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114357 prefixEnd_2114357 := by exact prefixLift 2114357
  have htrace : WordTrace (prefixWord ++ tailWord_2114357) baseStart_2114357 baseEnd_2114357 := by
    simpa [prefixWord, tailWord_2114357, baseEnd_2114357] using wordTrace_append hprefix tailTrace_2114357
  have hstable : (prefixWord ++ tailWord_2114357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114357).length < 2 ^ (prefixWord ++ tailWord_2114357).sum := by decide
  have hdescent : baseEnd_2114357 < baseStart_2114357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114387 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 3]
def baseStart_2114387 : Nat := 118140960795 + 2114387 * 2 ^ 59
def prefixEnd_2114387 : Nat := 4983230072969 + 3 ^ 40 * 2114387 * 2
def baseEnd_2114387 : Nat := 1085696820618124184838617

theorem tailTrace_2114387 : CollatzResearch.WordTrace tailWord_2114387 prefixEnd_2114387 1085696820618124184838617 := by
  unfold tailWord_2114387
  simp only [CollatzResearch.WordTrace]
  refine ⟨77118029390944482395389415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51412019593962988263592943 77118029390944482395389415)
  ·
    refine ⟨115677044086416723593084123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77118029390944482395389415 115677044086416723593084123)
    ·
      refine ⟨173515566129625085389626185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115677044086416723593084123 173515566129625085389626185)
      ·
        refine ⟨130136674597218814042219639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173515566129625085389626185 130136674597218814042219639)
        ·
          refine ⟨195205011895828221063329459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130136674597218814042219639 195205011895828221063329459)
          ·
            refine ⟨292807517843742331594994189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195205011895828221063329459 292807517843742331594994189)
            ·
              refine ⟨109802819191403374348122821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 292807517843742331594994189 109802819191403374348122821)
              ·
                refine ⟨20588028598388132690273029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109802819191403374348122821 20588028598388132690273029)
                ·
                  refine ⟨3860255362197774879426193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20588028598388132690273029 3860255362197774879426193)
                  ·
                    refine ⟨2895191521648331159569645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3860255362197774879426193 2895191521648331159569645)
                    ·
                      refine ⟨1085696820618124184838617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2895191521648331159569645 1085696820618124184838617)
                      ·
                        rfl

theorem cell23_2114387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 3].length) (baseStart_2114387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114387 prefixEnd_2114387 := by exact prefixLift 2114387
  have htrace : WordTrace (prefixWord ++ tailWord_2114387) baseStart_2114387 baseEnd_2114387 := by
    simpa [prefixWord, tailWord_2114387, baseEnd_2114387] using wordTrace_append hprefix tailTrace_2114387
  have hstable : (prefixWord ++ tailWord_2114387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114387).length < 2 ^ (prefixWord ++ tailWord_2114387).sum := by decide
  have hdescent : baseEnd_2114387 < baseStart_2114387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114394 : List Nat := [3, 1, 1, 2, 1, 5, 1, 2, 3, 4]
def baseStart_2114394 : Nat := 118140960795 + 2114394 * 2 ^ 59
def prefixEnd_2114394 : Nat := 4983230072969 + 3 ^ 40 * 2114394 * 2
def baseEnd_2114394 : Nat := 361900138327568552483695

theorem tailTrace_2114394 : CollatzResearch.WordTrace tailWord_2114394 prefixEnd_2114394 361900138327568552483695 := by
  unfold tailWord_2114394
  simp only [CollatzResearch.WordTrace]
  refine ⟨19279571175479780647723559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51412189801279415060596157 19279571175479780647723559)
  ·
    refine ⟨28919356763219670971585339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19279571175479780647723559 28919356763219670971585339)
    ·
      refine ⟨43379035144829506457378009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28919356763219670971585339 43379035144829506457378009)
      ·
        refine ⟨32534276358622129843033507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43379035144829506457378009 32534276358622129843033507)
        ·
          refine ⟨48801414537933194764550261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32534276358622129843033507 48801414537933194764550261)
          ·
            refine ⟨4575132612931237009176587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48801414537933194764550261 4575132612931237009176587)
            ·
              refine ⟨6862698919396855513764881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4575132612931237009176587 6862698919396855513764881)
              ·
                refine ⟨5147024189547641635323661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6862698919396855513764881 5147024189547641635323661)
                ·
                  refine ⟨1930134071080365613246373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5147024189547641635323661 1930134071080365613246373)
                  ·
                    refine ⟨361900138327568552483695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1930134071080365613246373 361900138327568552483695)
                    ·
                      rfl

theorem cell23_2114394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 3, 4].length) (baseStart_2114394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114394 prefixEnd_2114394 := by exact prefixLift 2114394
  have htrace : WordTrace (prefixWord ++ tailWord_2114394) baseStart_2114394 baseEnd_2114394 := by
    simpa [prefixWord, tailWord_2114394, baseEnd_2114394] using wordTrace_append hprefix tailTrace_2114394
  have hstable : (prefixWord ++ tailWord_2114394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114394).length < 2 ^ (prefixWord ++ tailWord_2114394).sum := by decide
  have hdescent : baseEnd_2114394 < baseStart_2114394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114404 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 1, 4, 3]
def baseStart_2114404 : Nat := 118140960795 + 2114404 * 2 ^ 59
def prefixEnd_2114404 : Nat := 4983230072969 + 3 ^ 40 * 2114404 * 2
def baseEnd_2114404 : Nat := 1085705549789250618326039

theorem tailTrace_2114404 : CollatzResearch.WordTrace tailWord_2114404 prefixEnd_2114404 1085705549789250618326039 := by
  unfold tailWord_2114404
  simp only [CollatzResearch.WordTrace]
  refine ⟨38559324715941447149379133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51412432954588596199172177 38559324715941447149379133)
  ·
    refine ⟨14459746768478042681017175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38559324715941447149379133 14459746768478042681017175)
    ·
      refine ⟨21689620152717064021525763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14459746768478042681017175 21689620152717064021525763)
      ·
        refine ⟨32534430229075596032288645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21689620152717064021525763 32534430229075596032288645)
        ·
          refine ⟨6100205667951674256054121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32534430229075596032288645 6100205667951674256054121)
          ·
            refine ⟨4575154250963755692040591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6100205667951674256054121 4575154250963755692040591)
            ·
              refine ⟨6862731376445633538060887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4575154250963755692040591 6862731376445633538060887)
              ·
                refine ⟨10294097064668450307091331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6862731376445633538060887 10294097064668450307091331)
                ·
                  refine ⟨15441145597002675460636997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10294097064668450307091331 15441145597002675460636997)
                  ·
                    refine ⟨2895214799438001648869437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15441145597002675460636997 2895214799438001648869437)
                    ·
                      refine ⟨1085705549789250618326039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2895214799438001648869437 1085705549789250618326039)
                      ·
                        rfl

theorem cell23_2114404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_2114404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114404 prefixEnd_2114404 := by exact prefixLift 2114404
  have htrace : WordTrace (prefixWord ++ tailWord_2114404) baseStart_2114404 baseEnd_2114404 := by
    simpa [prefixWord, tailWord_2114404, baseEnd_2114404] using wordTrace_append hprefix tailTrace_2114404
  have hstable : (prefixWord ++ tailWord_2114404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114404).length < 2 ^ (prefixWord ++ tailWord_2114404).sum := by decide
  have hdescent : baseEnd_2114404 < baseStart_2114404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114444 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 1, 5, 2]
def baseStart_2114444 : Nat := 118140960795 + 2114444 * 2 ^ 59
def prefixEnd_2114444 : Nat := 4983230072969 + 3 ^ 40 * 2114444 * 2
def baseEnd_2114444 : Nat := 1085726089015430461825855

theorem tailTrace_2114444 : CollatzResearch.WordTrace tailWord_2114444 prefixEnd_2114444 1085726089015430461825855 := by
  unfold tailWord_2114444
  simp only [CollatzResearch.WordTrace]
  refine ⟨38560054175868990565107193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51413405567825320753476257 38560054175868990565107193)
  ·
    refine ⟨28920040631901742923830395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38560054175868990565107193 28920040631901742923830395)
    ·
      refine ⟨43380060947852614385745593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28920040631901742923830395 43380060947852614385745593)
      ·
        refine ⟨32535045710889460789309195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43380060947852614385745593 32535045710889460789309195)
        ·
          refine ⟨48802568566334191183963793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32535045710889460789309195 48802568566334191183963793)
          ·
            refine ⟨36601926424750643387972845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48802568566334191183963793 36601926424750643387972845)
            ·
              refine ⟨13725722409281491270489817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36601926424750643387972845 13725722409281491270489817)
              ·
                refine ⟨10294291806961118452867363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13725722409281491270489817 10294291806961118452867363)
                ·
                  refine ⟨15441437710441677679301045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10294291806961118452867363 15441437710441677679301045)
                  ·
                    refine ⟨1447634785353907282434473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15441437710441677679301045 1447634785353907282434473)
                    ·
                      refine ⟨1085726089015430461825855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1447634785353907282434473 1085726089015430461825855)
                      ·
                        rfl

theorem cell23_2114444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 1, 5, 2].length) (baseStart_2114444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114444 prefixEnd_2114444 := by exact prefixLift 2114444
  have htrace : WordTrace (prefixWord ++ tailWord_2114444) baseStart_2114444 baseEnd_2114444 := by
    simpa [prefixWord, tailWord_2114444, baseEnd_2114444] using wordTrace_append hprefix tailTrace_2114444
  have hstable : (prefixWord ++ tailWord_2114444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114444).length < 2 ^ (prefixWord ++ tailWord_2114444).sum := by decide
  have hdescent : baseEnd_2114444 < baseStart_2114444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114461 : List Nat := [1, 4, 2, 1, 2, 1, 2, 3, 2, 3, 2]
def baseStart_2114461 : Nat := 118140960795 + 2114461 * 2 ^ 59
def prefixEnd_2114461 : Nat := 4983230072969 + 3 ^ 40 * 2114461 * 2
def baseEnd_2114461 : Nat := 1085734818186556895313277

theorem tailTrace_2114461 : CollatzResearch.WordTrace tailWord_2114461 prefixEnd_2114461 1085734818186556895313277 := by
  unfold tailWord_2114461
  simp only [CollatzResearch.WordTrace]
  refine ⟨77120728392676393033583237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51413818928450928689055491 77120728392676393033583237)
  ·
    refine ⟨14460136573626823693796857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77120728392676393033583237 14460136573626823693796857)
    ·
      refine ⟨10845102430220117770347643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14460136573626823693796857 10845102430220117770347643)
      ·
        refine ⟨16267653645330176655521465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10845102430220117770347643 16267653645330176655521465)
        ·
          refine ⟨12200740233997632491641099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16267653645330176655521465 12200740233997632491641099)
          ·
            refine ⟨18301110350996448737461649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12200740233997632491641099 18301110350996448737461649)
            ·
              refine ⟨13725832763247336553096237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18301110350996448737461649 13725832763247336553096237)
              ·
                refine ⟨5147187286217751207411089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13725832763247336553096237 5147187286217751207411089)
                ·
                  refine ⟨3860390464663313405558317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5147187286217751207411089 3860390464663313405558317)
                  ·
                    refine ⟨1447646424248742527084369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3860390464663313405558317 1447646424248742527084369)
                    ·
                      refine ⟨1085734818186556895313277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1447646424248742527084369 1085734818186556895313277)
                      ·
                        rfl

theorem cell23_2114461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_2114461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114461 prefixEnd_2114461 := by exact prefixLift 2114461
  have htrace : WordTrace (prefixWord ++ tailWord_2114461) baseStart_2114461 baseEnd_2114461 := by
    simpa [prefixWord, tailWord_2114461, baseEnd_2114461] using wordTrace_append hprefix tailTrace_2114461
  have hstable : (prefixWord ++ tailWord_2114461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114461).length < 2 ^ (prefixWord ++ tailWord_2114461).sum := by decide
  have hdescent : baseEnd_2114461 < baseStart_2114461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114467 : List Nat := [1, 1, 1, 4, 1, 2, 2, 4, 1, 6]
def baseStart_2114467 : Nat := 118140960795 + 2114467 * 2 ^ 59
def prefixEnd_2114467 : Nat := 4983230072969 + 3 ^ 40 * 2114467 * 2
def baseEnd_2114467 : Nat := 361912633023494623946083

theorem tailTrace_2114467 : CollatzResearch.WordTrace tailWord_2114467 prefixEnd_2114467 361912633023494623946083 := by
  unfold tailWord_2114467
  simp only [CollatzResearch.WordTrace]
  refine ⟨77120947230654656058301655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51413964820436437372201103 77120947230654656058301655)
  ·
    refine ⟨115681420845981984087452483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77120947230654656058301655 115681420845981984087452483)
    ·
      refine ⟨173522131268972976131178725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115681420845981984087452483 173522131268972976131178725)
      ·
        refine ⟨32535399612932433024596011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173522131268972976131178725 32535399612932433024596011)
        ·
          refine ⟨48803099419398649536894017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32535399612932433024596011 48803099419398649536894017)
          ·
            refine ⟨36602324564548987152670513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48803099419398649536894017 36602324564548987152670513)
            ·
              refine ⟨27451743423411740364502885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36602324564548987152670513 27451743423411740364502885)
              ·
                refine ⟨5147201891889701318344291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27451743423411740364502885 5147201891889701318344291)
                ·
                  refine ⟨7720802837834551977516437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5147201891889701318344291 7720802837834551977516437)
                  ·
                    refine ⟨361912633023494623946083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7720802837834551977516437 361912633023494623946083)
                    ·
                      rfl

theorem cell23_2114467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 6].length) (baseStart_2114467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114467 prefixEnd_2114467 := by exact prefixLift 2114467
  have htrace : WordTrace (prefixWord ++ tailWord_2114467) baseStart_2114467 baseEnd_2114467 := by
    simpa [prefixWord, tailWord_2114467, baseEnd_2114467] using wordTrace_append hprefix tailTrace_2114467
  have hstable : (prefixWord ++ tailWord_2114467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114467).length < 2 ^ (prefixWord ++ tailWord_2114467).sum := by decide
  have hdescent : baseEnd_2114467 < baseStart_2114467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114485 : List Nat := [1, 3, 3, 2, 1, 1, 5, 2, 1, 1, 3]
def baseStart_2114485 : Nat := 118140960795 + 2114485 * 2 ^ 59
def prefixEnd_2114485 : Nat := 4983230072969 + 3 ^ 40 * 2114485 * 2
def baseEnd_2114485 : Nat := 1085747141722264801413167

theorem tailTrace_2114485 : CollatzResearch.WordTrace tailWord_2114485 prefixEnd_2114485 1085747141722264801413167 := by
  unfold tailWord_2114485
  simp only [CollatzResearch.WordTrace]
  refine ⟨77121603744589445132456909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51414402496392963421637939 77121603744589445132456909)
  ·
    refine ⟨28920601404221041924671341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77121603744589445132456909 28920601404221041924671341)
    ·
      refine ⟨10845225526582890721751753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28920601404221041924671341 10845225526582890721751753)
      ·
        refine ⟨8133919144937168041313815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10845225526582890721751753 8133919144937168041313815)
        ·
          refine ⟨12200878717405752061970723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8133919144937168041313815 12200878717405752061970723)
          ·
            refine ⟨18301318076108628092956085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12200878717405752061970723 18301318076108628092956085)
            ·
              refine ⟨1715748569635183883714633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18301318076108628092956085 1715748569635183883714633)
              ·
                refine ⟨1286811427226387912785975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1715748569635183883714633 1286811427226387912785975)
                ·
                  refine ⟨1930217140839581869178963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1286811427226387912785975 1930217140839581869178963)
                  ·
                    refine ⟨2895325711259372803768445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1930217140839581869178963 2895325711259372803768445)
                    ·
                      refine ⟨1085747141722264801413167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2895325711259372803768445 1085747141722264801413167)
                      ·
                        rfl

theorem cell23_2114485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_2114485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114485 prefixEnd_2114485 := by exact prefixLift 2114485
  have htrace : WordTrace (prefixWord ++ tailWord_2114485) baseStart_2114485 baseEnd_2114485 := by
    simpa [prefixWord, tailWord_2114485, baseEnd_2114485] using wordTrace_append hprefix tailTrace_2114485
  have hstable : (prefixWord ++ tailWord_2114485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114485).length < 2 ^ (prefixWord ++ tailWord_2114485).sum := by decide
  have hdescent : baseEnd_2114485 < baseStart_2114485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114487 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 6]
def baseStart_2114487 : Nat := 118140960795 + 2114487 * 2 ^ 59
def prefixEnd_2114487 : Nat := 4983230072969 + 3 ^ 40 * 2114487 * 2
def baseEnd_2114487 : Nat := 1085748168683573793588157

theorem tailTrace_2114487 : CollatzResearch.WordTrace tailWord_2114487 prefixEnd_2114487 1085748168683573793588157 := by
  unfold tailWord_2114487
  simp only [CollatzResearch.WordTrace]
  refine ⟨77121676690582199474029715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51414451127054799649353143 77121676690582199474029715)
  ·
    refine ⟨115682515035873299211044573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77121676690582199474029715 115682515035873299211044573)
    ·
      refine ⟨43380943138452487204141715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115682515035873299211044573 43380943138452487204141715)
      ·
        refine ⟨65071414707678730806212573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43380943138452487204141715 65071414707678730806212573)
        ·
          refine ⟨24401780515379524052329715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65071414707678730806212573 24401780515379524052329715)
          ·
            refine ⟨36602670773069286078494573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24401780515379524052329715 36602670773069286078494573)
            ·
              refine ⟨13726001539900982279435465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36602670773069286078494573 13726001539900982279435465)
              ·
                refine ⟨10294501154925736709576599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13726001539900982279435465 10294501154925736709576599)
                ·
                  refine ⟨15441751732388605064364899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10294501154925736709576599 15441751732388605064364899)
                  ·
                    refine ⟨23162627598582907596547349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15441751732388605064364899 23162627598582907596547349)
                    ·
                      refine ⟨1085748168683573793588157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23162627598582907596547349 1085748168683573793588157)
                      ·
                        rfl

theorem cell23_2114487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_2114487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114487 prefixEnd_2114487 := by exact prefixLift 2114487
  have htrace : WordTrace (prefixWord ++ tailWord_2114487) baseStart_2114487 baseEnd_2114487 := by
    simpa [prefixWord, tailWord_2114487, baseEnd_2114487] using wordTrace_append hprefix tailTrace_2114487
  have hstable : (prefixWord ++ tailWord_2114487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114487).length < 2 ^ (prefixWord ++ tailWord_2114487).sum := by decide
  have hdescent : baseEnd_2114487 < baseStart_2114487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114494 : List Nat := [4, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_2114494 : Nat := 118140960795 + 2114494 * 2 ^ 59
def prefixEnd_2114494 : Nat := 4983230072969 + 3 ^ 40 * 2114494 * 2
def baseEnd_2114494 : Nat := 1085751763048155266200625

theorem tailTrace_2114494 : CollatzResearch.WordTrace tailWord_2114494 prefixEnd_2114494 1085751763048155266200625 := by
  unfold tailWord_2114494
  simp only [CollatzResearch.WordTrace]
  refine ⟨9640241500194604958691817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51414621334371226446356357 9640241500194604958691817)
  ·
    refine ⟨7230181125145953719018863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9640241500194604958691817 7230181125145953719018863)
    ·
      refine ⟨10845271687718930578528295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7230181125145953719018863 10845271687718930578528295)
      ·
        refine ⟨16267907531578395867792443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10845271687718930578528295 16267907531578395867792443)
        ·
          refine ⟨24401861297367593801688665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16267907531578395867792443 24401861297367593801688665)
          ·
            refine ⟨18301395973025695351266499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24401861297367593801688665 18301395973025695351266499)
            ·
              refine ⟨27452093959538543026899749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18301395973025695351266499 27452093959538543026899749)
              ·
                refine ⟨5147267617413476817543703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27452093959538543026899749 5147267617413476817543703)
                ·
                  refine ⟨7720901426120215226315555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5147267617413476817543703 7720901426120215226315555)
                  ·
                    refine ⟨11581352139180322839473333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7720901426120215226315555 11581352139180322839473333)
                    ·
                      refine ⟨1085751763048155266200625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11581352139180322839473333 1085751763048155266200625)
                      ·
                        rfl

theorem cell23_2114494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_2114494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114494 prefixEnd_2114494 := by exact prefixLift 2114494
  have htrace : WordTrace (prefixWord ++ tailWord_2114494) baseStart_2114494 baseEnd_2114494 := by
    simpa [prefixWord, tailWord_2114494, baseEnd_2114494] using wordTrace_append hprefix tailTrace_2114494
  have hstable : (prefixWord ++ tailWord_2114494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114494).length < 2 ^ (prefixWord ++ tailWord_2114494).sum := by decide
  have hdescent : baseEnd_2114494 < baseStart_2114494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114511 : List Nat := [1, 1, 2, 1, 1, 6, 3, 2, 1, 2, 3]
def baseStart_2114511 : Nat := 118140960795 + 2114511 * 2 ^ 59
def prefixEnd_2114511 : Nat := 4983230072969 + 3 ^ 40 * 2114511 * 2
def baseEnd_2114511 : Nat := 1085760492219281699688047

theorem tailTrace_2114511 : CollatzResearch.WordTrace tailWord_2114511 prefixEnd_2114511 1085760492219281699688047 := by
  unfold tailWord_2114511
  simp only [CollatzResearch.WordTrace]
  refine ⟨77122552042495251572903387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51415034694996834381935591 77122552042495251572903387)
  ·
    refine ⟨115683828063742877359355081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77122552042495251572903387 115683828063742877359355081)
    ·
      refine ⟨86762871047807158019516311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115683828063742877359355081 86762871047807158019516311)
      ·
        refine ⟨130144306571710737029274467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86762871047807158019516311 130144306571710737029274467)
        ·
          refine ⟨195216459857566105543911701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130144306571710737029274467 195216459857566105543911701)
          ·
            refine ⟨9150771555823411197370861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 195216459857566105543911701 9150771555823411197370861)
            ·
              refine ⟨3431539333433779199014073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9150771555823411197370861 3431539333433779199014073)
              ·
                refine ⟨2573654500075334399260555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3431539333433779199014073 2573654500075334399260555)
                ·
                  refine ⟨3860481750113001598890833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2573654500075334399260555 3860481750113001598890833)
                  ·
                    refine ⟨2895361312584751199168125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3860481750113001598890833 2895361312584751199168125)
                    ·
                      refine ⟨1085760492219281699688047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2895361312584751199168125 1085760492219281699688047)
                      ·
                        rfl

theorem cell23_2114511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 2, 3].length) (baseStart_2114511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114511 prefixEnd_2114511 := by exact prefixLift 2114511
  have htrace : WordTrace (prefixWord ++ tailWord_2114511) baseStart_2114511 baseEnd_2114511 := by
    simpa [prefixWord, tailWord_2114511, baseEnd_2114511] using wordTrace_append hprefix tailTrace_2114511
  have hstable : (prefixWord ++ tailWord_2114511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114511).length < 2 ^ (prefixWord ++ tailWord_2114511).sum := by decide
  have hdescent : baseEnd_2114511 < baseStart_2114511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114514 : List Nat := [3, 2, 2, 3, 1, 1, 2, 9]
def baseStart_2114514 : Nat := 118140960795 + 2114514 * 2 ^ 59
def prefixEnd_2114514 : Nat := 4983230072969 + 3 ^ 40 * 2114514 * 2
def baseEnd_2114514 : Nat := 40213408617083155109279

theorem tailTrace_2114514 : CollatzResearch.WordTrace tailWord_2114514 prefixEnd_2114514 40213408617083155109279 := by
  unfold tailWord_2114514
  simp only [CollatzResearch.WordTrace]
  refine ⟨19280665365371095771315649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51415107640989588723508397 19280665365371095771315649)
  ·
    refine ⟨14460499024028321828486737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19280665365371095771315649 14460499024028321828486737)
    ·
      refine ⟨10845374268021241371365053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14460499024028321828486737 10845374268021241371365053)
      ·
        refine ⟨4067015350507965514261895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10845374268021241371365053 4067015350507965514261895)
        ·
          refine ⟨6100523025761948271392843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4067015350507965514261895 6100523025761948271392843)
          ·
            refine ⟨9150784538642922407089265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6100523025761948271392843 9150784538642922407089265)
            ·
              refine ⟨6863088403982191805316949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9150784538642922407089265 6863088403982191805316949)
              ·
                refine ⟨40213408617083155109279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6863088403982191805316949 40213408617083155109279)
                ·
                  rfl

theorem cell23_2114514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 9].length) (baseStart_2114514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114514 prefixEnd_2114514 := by exact prefixLift 2114514
  have htrace : WordTrace (prefixWord ++ tailWord_2114514) baseStart_2114514 baseEnd_2114514 := by
    simpa [prefixWord, tailWord_2114514, baseEnd_2114514] using wordTrace_append hprefix tailTrace_2114514
  have hstable : (prefixWord ++ tailWord_2114514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114514).length < 2 ^ (prefixWord ++ tailWord_2114514).sum := by decide
  have hdescent : baseEnd_2114514 < baseStart_2114514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114542 : List Nat := [4, 1, 2, 1, 4, 1, 1, 4, 1, 2, 2]
def baseStart_2114542 : Nat := 118140960795 + 2114542 * 2 ^ 59
def prefixEnd_2114542 : Nat := 4983230072969 + 3 ^ 40 * 2114542 * 2
def baseEnd_2114542 : Nat := 1085776410119571078400405

theorem tailTrace_2114542 : CollatzResearch.WordTrace tailWord_2114542 prefixEnd_2114542 1085776410119571078400405 := by
  unfold tailWord_2114542
  simp only [CollatzResearch.WordTrace]
  refine ⟨9640460338172867983410235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51415788470255295911521253 9640460338172867983410235)
  ·
    refine ⟨14460690507259301975115353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9640460338172867983410235 14460690507259301975115353)
    ·
      refine ⟨10845517880444476481336515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14460690507259301975115353 10845517880444476481336515)
      ·
        refine ⟨16268276820666714722004773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10845517880444476481336515 16268276820666714722004773)
        ·
          refine ⟨3050301903875009010375895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16268276820666714722004773 3050301903875009010375895)
          ·
            refine ⟨4575452855812513515563843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3050301903875009010375895 4575452855812513515563843)
            ·
              refine ⟨6863179283718770273345765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4575452855812513515563843 6863179283718770273345765)
              ·
                refine ⟨1286846115697269426252331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6863179283718770273345765 1286846115697269426252331)
                ·
                  refine ⟨1930269173545904139378497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1286846115697269426252331 1930269173545904139378497)
                  ·
                    refine ⟨1447701880159428104533873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1930269173545904139378497 1447701880159428104533873)
                    ·
                      refine ⟨1085776410119571078400405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1447701880159428104533873 1085776410119571078400405)
                      ·
                        rfl

theorem cell23_2114542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_2114542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114542 prefixEnd_2114542 := by exact prefixLift 2114542
  have htrace : WordTrace (prefixWord ++ tailWord_2114542) baseStart_2114542 baseEnd_2114542 := by
    simpa [prefixWord, tailWord_2114542, baseEnd_2114542] using wordTrace_append hprefix tailTrace_2114542
  have hstable : (prefixWord ++ tailWord_2114542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114542).length < 2 ^ (prefixWord ++ tailWord_2114542).sum := by decide
  have hdescent : baseEnd_2114542 < baseStart_2114542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114592 : List Nat := [2, 1, 1, 7, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2114592 : Nat := 118140960795 + 2114592 * 2 ^ 59
def prefixEnd_2114592 : Nat := 4983230072969 + 3 ^ 40 * 2114592 * 2
def baseEnd_2114592 : Nat := 1085802084152295882775175

theorem tailTrace_2114592 : CollatzResearch.WordTrace tailWord_2114592 prefixEnd_2114592 1085802084152295882775175 := by
  unfold tailWord_2114592
  simp only [CollatzResearch.WordTrace]
  refine ⟨38562753177600901203301015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51417004236801201604401353 38562753177600901203301015)
  ·
    refine ⟨57844129766401351804951523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38562753177600901203301015 57844129766401351804951523)
    ·
      refine ⟨86766194649602027707427285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57844129766401351804951523 86766194649602027707427285)
      ·
        refine ⟨2033582687100047524392827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 86766194649602027707427285 2033582687100047524392827)
        ·
          refine ⟨3050374030650071286589241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2033582687100047524392827 3050374030650071286589241)
          ·
            refine ⟨2287780522987553464941931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3050374030650071286589241 2287780522987553464941931)
            ·
              refine ⟨3431670784481330197412897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2287780522987553464941931 3431670784481330197412897)
              ·
                refine ⟨2573753088360997648059673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3431670784481330197412897 2573753088360997648059673)
                ·
                  refine ⟨1930314816270748236044755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2573753088360997648059673 1930314816270748236044755)
                  ·
                    refine ⟨2895472224406122354067133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1930314816270748236044755 2895472224406122354067133)
                    ·
                      refine ⟨1085802084152295882775175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2895472224406122354067133 1085802084152295882775175)
                      ·
                        rfl

theorem cell23_2114592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2114592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114592 prefixEnd_2114592 := by exact prefixLift 2114592
  have htrace : WordTrace (prefixWord ++ tailWord_2114592) baseStart_2114592 baseEnd_2114592 := by
    simpa [prefixWord, tailWord_2114592, baseEnd_2114592] using wordTrace_append hprefix tailTrace_2114592
  have hstable : (prefixWord ++ tailWord_2114592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114592).length < 2 ^ (prefixWord ++ tailWord_2114592).sum := by decide
  have hdescent : baseEnd_2114592 < baseStart_2114592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114604 : List Nat := [2, 2, 1, 1, 1, 2, 6, 1, 7]
def baseStart_2114604 : Nat := 118140960795 + 2114604 * 2 ^ 59
def prefixEnd_2114604 : Nat := 4983230072969 + 3 ^ 40 * 2114604 * 2
def baseEnd_2114604 : Nat := 120645360657794426202791

theorem tailTrace_2114604 : CollatzResearch.WordTrace tailWord_2114604 prefixEnd_2114604 120645360657794426202791 := by
  unfold tailWord_2114604
  simp only [CollatzResearch.WordTrace]
  refine ⟨38562972015579164228019433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51417296020772218970692577 38562972015579164228019433)
  ·
    refine ⟨28922229011684373171014575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38562972015579164228019433 28922229011684373171014575)
    ·
      refine ⟨43383343517526559756521863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28922229011684373171014575 43383343517526559756521863)
      ·
        refine ⟨65075015276289839634782795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43383343517526559756521863 65075015276289839634782795)
        ·
          refine ⟨97612522914434759452174193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65075015276289839634782795 97612522914434759452174193)
          ·
            refine ⟨73209392185826069589130645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97612522914434759452174193 73209392185826069589130645)
            ·
              refine ⟨3431690258710597011990499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73209392185826069589130645 3431690258710597011990499)
              ·
                refine ⟨5147535388065895517985749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3431690258710597011990499 5147535388065895517985749)
                ·
                  refine ⟨120645360657794426202791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5147535388065895517985749 120645360657794426202791)
                  ·
                    rfl

theorem cell23_2114604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 7].length) (baseStart_2114604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114604 prefixEnd_2114604 := by exact prefixLift 2114604
  have htrace : WordTrace (prefixWord ++ tailWord_2114604) baseStart_2114604 baseEnd_2114604 := by
    simpa [prefixWord, tailWord_2114604, baseEnd_2114604] using wordTrace_append hprefix tailTrace_2114604
  have hstable : (prefixWord ++ tailWord_2114604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114604).length < 2 ^ (prefixWord ++ tailWord_2114604).sum := by decide
  have hdescent : baseEnd_2114604 < baseStart_2114604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114634 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 1, 7]
def baseStart_2114634 : Nat := 118140960795 + 2114634 * 2 ^ 59
def prefixEnd_2114634 : Nat := 4983230072969 + 3 ^ 40 * 2114634 * 2
def baseEnd_2114634 : Nat := 361941216779928239483327

theorem tailTrace_2114634 : CollatzResearch.WordTrace tailWord_2114634 prefixEnd_2114634 361941216779928239483327 := by
  unfold tailWord_2114634
  simp only [CollatzResearch.WordTrace]
  refine ⟨19281759555262410894907739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51418025480699762386420637 19281759555262410894907739)
  ·
    refine ⟨28922639332893616342361609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19281759555262410894907739 28922639332893616342361609)
    ·
      refine ⟨21691979499670212256771207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28922639332893616342361609 21691979499670212256771207)
      ·
        refine ⟨32537969249505318385156811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21691979499670212256771207 32537969249505318385156811)
        ·
          refine ⟨48806953874257977577735217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32537969249505318385156811 48806953874257977577735217)
          ·
            refine ⟨36605215405693483183301413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48806953874257977577735217 36605215405693483183301413)
            ·
              refine ⟨6863477888567528096869015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36605215405693483183301413 6863477888567528096869015)
              ·
                refine ⟨10295216832851292145303523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6863477888567528096869015 10295216832851292145303523)
                ·
                  refine ⟨15442825249276938217955285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10295216832851292145303523 15442825249276938217955285)
                  ·
                    refine ⟨361941216779928239483327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15442825249276938217955285 361941216779928239483327)
                    ·
                      rfl

theorem cell23_2114634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_2114634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114634 prefixEnd_2114634 := by exact prefixLift 2114634
  have htrace : WordTrace (prefixWord ++ tailWord_2114634) baseStart_2114634 baseEnd_2114634 := by
    simpa [prefixWord, tailWord_2114634, baseEnd_2114634] using wordTrace_append hprefix tailTrace_2114634
  have hstable : (prefixWord ++ tailWord_2114634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114634).length < 2 ^ (prefixWord ++ tailWord_2114634).sum := by decide
  have hdescent : baseEnd_2114634 < baseStart_2114634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114671 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 1, 6, 2]
def baseStart_2114671 : Nat := 118140960795 + 2114671 * 2 ^ 59
def prefixEnd_2114671 : Nat := 4983230072969 + 3 ^ 40 * 2114671 * 2
def baseEnd_2114671 : Nat := 1085842649124001073687311

theorem tailTrace_2114671 : CollatzResearch.WordTrace tailWord_2114671 prefixEnd_2114671 1085842649124001073687311 := by
  unfold tailWord_2114671
  simp only [CollatzResearch.WordTrace]
  refine ⟨77128387721915598898727867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51418925147943732599151911 77128387721915598898727867)
  ·
    refine ⟨115692581582873398348091801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77128387721915598898727867 115692581582873398348091801)
    ·
      refine ⟨86769436187155048761068851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115692581582873398348091801 86769436187155048761068851)
      ·
        refine ⟨130154154280732573141603277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86769436187155048761068851 130154154280732573141603277)
        ·
          refine ⟨48807807855274714928101229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130154154280732573141603277 48807807855274714928101229)
          ·
            refine ⟨18302927945728018098037961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48807807855274714928101229 18302927945728018098037961)
            ·
              refine ⟨13727195959296013573528471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18302927945728018098037961 13727195959296013573528471)
              ·
                refine ⟨20590793938944020360292707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13727195959296013573528471 20590793938944020360292707)
                ·
                  refine ⟨30886190908416030540439061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20590793938944020360292707 30886190908416030540439061)
                  ·
                    refine ⟨1447790198832001431583081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30886190908416030540439061 1447790198832001431583081)
                    ·
                      refine ⟨1085842649124001073687311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1447790198832001431583081 1085842649124001073687311)
                      ·
                        rfl

theorem cell23_2114671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 6, 2].length) (baseStart_2114671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114671 prefixEnd_2114671 := by exact prefixLift 2114671
  have htrace : WordTrace (prefixWord ++ tailWord_2114671) baseStart_2114671 baseEnd_2114671 := by
    simpa [prefixWord, tailWord_2114671, baseEnd_2114671] using wordTrace_append hprefix tailTrace_2114671
  have hstable : (prefixWord ++ tailWord_2114671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114671).length < 2 ^ (prefixWord ++ tailWord_2114671).sum := by decide
  have hdescent : baseEnd_2114671 < baseStart_2114671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114711 : List Nat := [1, 1, 3, 3, 3, 1, 1, 4, 6]
def baseStart_2114711 : Nat := 118140960795 + 2114711 * 2 ^ 59
def prefixEnd_2114711 : Nat := 4983230072969 + 3 ^ 40 * 2114711 * 2
def baseEnd_2114711 : Nat := 120651465372242324131903

theorem tailTrace_2114711 : CollatzResearch.WordTrace tailWord_2114711 prefixEnd_2114711 120651465372242324131903 := by
  unfold tailWord_2114711
  simp only [CollatzResearch.WordTrace]
  refine ⟨77129846641770685730183987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51419897761180457153455991 77129846641770685730183987)
  ·
    refine ⟨115694769962656028595275981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77129846641770685730183987 115694769962656028595275981)
    ·
      refine ⟨43385538735996010723228493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115694769962656028595275981 43385538735996010723228493)
      ·
        refine ⟨16269577025998504021210685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43385538735996010723228493 16269577025998504021210685)
        ·
          refine ⟨6101091384749439007954007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16269577025998504021210685 6101091384749439007954007)
          ·
            refine ⟨9151637077124158511931011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6101091384749439007954007 9151637077124158511931011)
            ·
              refine ⟨13727455615686237767896517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9151637077124158511931011 13727455615686237767896517)
              ·
                refine ⟨2573897927941169581480597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13727455615686237767896517 2573897927941169581480597)
                ·
                  refine ⟨120651465372242324131903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2573897927941169581480597 120651465372242324131903)
                  ·
                    rfl

theorem cell23_2114711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 6].length) (baseStart_2114711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114711 prefixEnd_2114711 := by exact prefixLift 2114711
  have htrace : WordTrace (prefixWord ++ tailWord_2114711) baseStart_2114711 baseEnd_2114711 := by
    simpa [prefixWord, tailWord_2114711, baseEnd_2114711] using wordTrace_append hprefix tailTrace_2114711
  have hstable : (prefixWord ++ tailWord_2114711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114711).length < 2 ^ (prefixWord ++ tailWord_2114711).sum := by decide
  have hdescent : baseEnd_2114711 < baseStart_2114711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114738 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3]
def baseStart_2114738 : Nat := 118140960795 + 2114738 * 2 ^ 59
def prefixEnd_2114738 : Nat := 4983230072969 + 3 ^ 40 * 2114738 * 2
def baseEnd_2114738 : Nat := 1085877052327852311549503

theorem tailTrace_2114738 : CollatzResearch.WordTrace tailWord_2114738 prefixEnd_2114738 1085877052327852311549503 := by
  unfold tailWord_2114738
  simp only [CollatzResearch.WordTrace]
  refine ⟨19282707853168217335354217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51420554275115246227611245 19282707853168217335354217)
  ·
    refine ⟨14462030889876163001515663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19282707853168217335354217 14462030889876163001515663)
    ·
      refine ⟨21693046334814244502273495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14462030889876163001515663 21693046334814244502273495)
      ·
        refine ⟨32539569502221366753410243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21693046334814244502273495 32539569502221366753410243)
        ·
          refine ⟨48809354253332050130115365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32539569502221366753410243 48809354253332050130115365)
          ·
            refine ⟨9151753922499759399396631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48809354253332050130115365 9151753922499759399396631)
            ·
              refine ⟨13727630883749639099094947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9151753922499759399396631 13727630883749639099094947)
              ·
                refine ⟨20591446325624458648642421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13727630883749639099094947 20591446325624458648642421)
                ·
                  refine ⟨1930448093027292998310227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20591446325624458648642421 1930448093027292998310227)
                  ·
                    refine ⟨2895672139540939497465341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1930448093027292998310227 2895672139540939497465341)
                    ·
                      refine ⟨1085877052327852311549503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2895672139540939497465341 1085877052327852311549503)
                      ·
                        rfl

theorem cell23_2114738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_2114738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114738 prefixEnd_2114738 := by exact prefixLift 2114738
  have htrace : WordTrace (prefixWord ++ tailWord_2114738) baseStart_2114738 baseEnd_2114738 := by
    simpa [prefixWord, tailWord_2114738, baseEnd_2114738] using wordTrace_append hprefix tailTrace_2114738
  have hstable : (prefixWord ++ tailWord_2114738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114738).length < 2 ^ (prefixWord ++ tailWord_2114738).sum := by decide
  have hdescent : baseEnd_2114738 < baseStart_2114738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114742 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_2114742 : Nat := 118140960795 + 2114742 * 2 ^ 59
def prefixEnd_2114742 : Nat := 4983230072969 + 3 ^ 40 * 2114742 * 2
def baseEnd_2114742 : Nat := 1085879106250470295899485

theorem tailTrace_2114742 : CollatzResearch.WordTrace tailWord_2114742 prefixEnd_2114742 1085879106250470295899485 := by
  unfold tailWord_2114742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4820686081541148626535155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51420651536438918683041653 4820686081541148626535155)
  ·
    refine ⟨7231029122311722939802733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4820686081541148626535155 7231029122311722939802733)
    ·
      refine ⟨2711635920866896102426025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7231029122311722939802733 2711635920866896102426025)
      ·
        refine ⟨2033726940650172076819519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2711635920866896102426025 2033726940650172076819519)
        ·
          refine ⟨3050590410975258115229279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2033726940650172076819519 3050590410975258115229279)
          ·
            refine ⟨4575885616462887172843919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3050590410975258115229279 4575885616462887172843919)
            ·
              refine ⟨6863828424694330759265879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4575885616462887172843919 6863828424694330759265879)
              ·
                refine ⟨10295742637041496138898819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6863828424694330759265879 10295742637041496138898819)
                ·
                  refine ⟨15443613955562244208348229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10295742637041496138898819 15443613955562244208348229)
                  ·
                    refine ⟨2895677616667920789065293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15443613955562244208348229 2895677616667920789065293)
                    ·
                      refine ⟨1085879106250470295899485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2895677616667920789065293 1085879106250470295899485)
                      ·
                        rfl

theorem cell23_2114742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_2114742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114742 prefixEnd_2114742 := by exact prefixLift 2114742
  have htrace : WordTrace (prefixWord ++ tailWord_2114742) baseStart_2114742 baseEnd_2114742 := by
    simpa [prefixWord, tailWord_2114742, baseEnd_2114742] using wordTrace_append hprefix tailTrace_2114742
  have hstable : (prefixWord ++ tailWord_2114742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114742).length < 2 ^ (prefixWord ++ tailWord_2114742).sum := by decide
  have hdescent : baseEnd_2114742 < baseStart_2114742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114771 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 4, 4]
def baseStart_2114771 : Nat := 118140960795 + 2114771 * 2 ^ 59
def prefixEnd_2114771 : Nat := 4983230072969 + 3 ^ 40 * 2114771 * 2
def baseEnd_2114771 : Nat := 361964665729816894145617

theorem tailTrace_2114771 : CollatzResearch.WordTrace tailWord_2114771 prefixEnd_2114771 361964665729816894145617 := by
  unfold tailWord_2114771
  simp only [CollatzResearch.WordTrace]
  refine ⟨77132035021553315977368167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51421356681035543984912111 77132035021553315977368167)
  ·
    refine ⟨115698052532329973966052251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77132035021553315977368167 115698052532329973966052251)
    ·
      refine ⟨173547078798494960949078377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115698052532329973966052251 173547078798494960949078377)
      ·
        refine ⟨130160309098871220711808783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173547078798494960949078377 130160309098871220711808783)
        ·
          refine ⟨195240463648306831067713175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130160309098871220711808783 195240463648306831067713175)
          ·
            refine ⟨292860695472460246601569763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195240463648306831067713175 292860695472460246601569763)
            ·
              refine ⟨439291043208690369902354645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292860695472460246601569763 439291043208690369902354645)
              ·
                refine ⟨10295883825203680544586437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 439291043208690369902354645 10295883825203680544586437)
                ·
                  refine ⟨1930478217225690102109957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10295883825203680544586437 1930478217225690102109957)
                  ·
                    refine ⟨361964665729816894145617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1930478217225690102109957 361964665729816894145617)
                    ·
                      rfl

theorem cell23_2114771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 4].length) (baseStart_2114771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114771 prefixEnd_2114771 := by exact prefixLift 2114771
  have htrace : WordTrace (prefixWord ++ tailWord_2114771) baseStart_2114771 baseEnd_2114771 := by
    simpa [prefixWord, tailWord_2114771, baseEnd_2114771] using wordTrace_append hprefix tailTrace_2114771
  have hstable : (prefixWord ++ tailWord_2114771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114771).length < 2 ^ (prefixWord ++ tailWord_2114771).sum := by decide
  have hdescent : baseEnd_2114771 < baseStart_2114771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114788 : List Nat := [2, 3, 1, 1, 1, 2, 2, 5, 2, 4]
def baseStart_2114788 : Nat := 118140960795 + 2114788 * 2 ^ 59
def prefixEnd_2114788 : Nat := 4983230072969 + 3 ^ 40 * 2114788 * 2
def baseEnd_2114788 : Nat := 361967575453525705308091

theorem tailTrace_2114788 : CollatzResearch.WordTrace tailWord_2114788 prefixEnd_2114788 361967575453525705308091 := by
  unfold tailWord_2114788
  simp only [CollatzResearch.WordTrace]
  refine ⟨38566327531245863940368509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51421770041661151920491345 38566327531245863940368509)
  ·
    refine ⟨14462372824217198977638191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38566327531245863940368509 14462372824217198977638191)
    ·
      refine ⟨21693559236325798466457287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14462372824217198977638191 21693559236325798466457287)
      ·
        refine ⟨32540338854488697699685931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21693559236325798466457287 32540338854488697699685931)
        ·
          refine ⟨48810508281733046549528897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32540338854488697699685931 48810508281733046549528897)
          ·
            refine ⟨36607881211299784912146673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48810508281733046549528897 36607881211299784912146673)
            ·
              refine ⟨27455910908474838684110005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36607881211299784912146673 27455910908474838684110005)
              ·
                refine ⟨2573991647669516126635313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27455910908474838684110005 2573991647669516126635313)
                ·
                  refine ⟨1930493735752137094976485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2573991647669516126635313 1930493735752137094976485)
                  ·
                    refine ⟨361967575453525705308091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1930493735752137094976485 361967575453525705308091)
                    ·
                      rfl

theorem cell23_2114788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_2114788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114788 prefixEnd_2114788 := by exact prefixLift 2114788
  have htrace : WordTrace (prefixWord ++ tailWord_2114788) baseStart_2114788 baseEnd_2114788 := by
    simpa [prefixWord, tailWord_2114788, baseEnd_2114788] using wordTrace_append hprefix tailTrace_2114788
  have hstable : (prefixWord ++ tailWord_2114788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114788).length < 2 ^ (prefixWord ++ tailWord_2114788).sum := by decide
  have hdescent : baseEnd_2114788 < baseStart_2114788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114795 : List Nat := [1, 1, 1, 1, 2, 6, 2, 2, 3, 2, 2]
def baseStart_2114795 : Nat := 118140960795 + 2114795 * 2 ^ 59
def prefixEnd_2114795 : Nat := 4983230072969 + 3 ^ 40 * 2114795 * 2
def baseEnd_2114795 : Nat := 1085906320725158588536741

theorem tailTrace_2114795 : CollatzResearch.WordTrace tailWord_2114795 prefixEnd_2114795 1085906320725158588536741 := by
  unfold tailWord_2114795
  simp only [CollatzResearch.WordTrace]
  refine ⟨77132910373466368076241839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51421940248977578717494559 77132910373466368076241839)
  ·
    refine ⟨115699365560199552114362759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77132910373466368076241839 115699365560199552114362759)
    ·
      refine ⟨173549048340299328171544139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115699365560199552114362759 173549048340299328171544139)
      ·
        refine ⟨260323572510448992257316209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173549048340299328171544139 260323572510448992257316209)
        ·
          refine ⟨195242679382836744192987157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260323572510448992257316209 195242679382836744192987157)
          ·
            refine ⟨9152000596070472384046273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 195242679382836744192987157 9152000596070472384046273)
            ·
              refine ⟨6864000447052854288034705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9152000596070472384046273 6864000447052854288034705)
              ·
                refine ⟨5148000335289640716026029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6864000447052854288034705 5148000335289640716026029)
                ·
                  refine ⟨1930500125733615268509761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5148000335289640716026029 1930500125733615268509761)
                  ·
                    refine ⟨1447875094300211451382321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1930500125733615268509761 1447875094300211451382321)
                    ·
                      refine ⟨1085906320725158588536741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1447875094300211451382321 1085906320725158588536741)
                      ·
                        rfl

theorem cell23_2114795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 2, 2].length) (baseStart_2114795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114795 prefixEnd_2114795 := by exact prefixLift 2114795
  have htrace : WordTrace (prefixWord ++ tailWord_2114795) baseStart_2114795 baseEnd_2114795 := by
    simpa [prefixWord, tailWord_2114795, baseEnd_2114795] using wordTrace_append hprefix tailTrace_2114795
  have hstable : (prefixWord ++ tailWord_2114795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114795).length < 2 ^ (prefixWord ++ tailWord_2114795).sum := by decide
  have hdescent : baseEnd_2114795 < baseStart_2114795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114798 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 3, 2, 3]
def baseStart_2114798 : Nat := 118140960795 + 2114798 * 2 ^ 59
def prefixEnd_2114798 : Nat := 4983230072969 + 3 ^ 40 * 2114798 * 2
def baseEnd_2114798 : Nat := 1085907861167122076799227

theorem tailTrace_2114798 : CollatzResearch.WordTrace tailWord_2114798 prefixEnd_2114798 1085907861167122076799227 := by
  unfold tailWord_2114798
  simp only [CollatzResearch.WordTrace]
  refine ⟨9641627474056937448575131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51422013194970333059067365 9641627474056937448575131)
  ·
    refine ⟨14462441211085406172862697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9641627474056937448575131 14462441211085406172862697)
    ·
      refine ⟨10846830908314054629647023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14462441211085406172862697 10846830908314054629647023)
      ·
        refine ⟨16270246362471081944470535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10846830908314054629647023 16270246362471081944470535)
        ·
          refine ⟨24405369543706622916705803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16270246362471081944470535 24405369543706622916705803)
          ·
            refine ⟨36608054315559934375058705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24405369543706622916705803 36608054315559934375058705)
            ·
              refine ⟨27456040736669950781294029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36608054315559934375058705 27456040736669950781294029)
              ·
                refine ⟨10296015276251231542985261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27456040736669950781294029 10296015276251231542985261)
                ·
                  refine ⟨3861005728594211828619473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10296015276251231542985261 3861005728594211828619473)
                  ·
                    refine ⟨2895754296445658871464605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3861005728594211828619473 2895754296445658871464605)
                    ·
                      refine ⟨1085907861167122076799227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2895754296445658871464605 1085907861167122076799227)
                      ·
                        rfl

theorem cell23_2114798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_2114798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114798 prefixEnd_2114798 := by exact prefixLift 2114798
  have htrace : WordTrace (prefixWord ++ tailWord_2114798) baseStart_2114798 baseEnd_2114798 := by
    simpa [prefixWord, tailWord_2114798, baseEnd_2114798] using wordTrace_append hprefix tailTrace_2114798
  have hstable : (prefixWord ++ tailWord_2114798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114798).length < 2 ^ (prefixWord ++ tailWord_2114798).sum := by decide
  have hdescent : baseEnd_2114798 < baseStart_2114798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114846 : List Nat := [4, 3, 2, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_2114846 : Nat := 118140960795 + 2114846 * 2 ^ 59
def prefixEnd_2114846 : Nat := 4983230072969 + 3 ^ 40 * 2114846 * 2
def baseEnd_2114846 : Nat := 1085932508238537888999007

theorem tailTrace_2114846 : CollatzResearch.WordTrace tailWord_2114846 prefixEnd_2114846 1085932508238537888999007 := by
  unfold tailWord_2114846
  simp only [CollatzResearch.WordTrace]
  refine ⟨9641846312035200473293549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51423180330854402524232261 9641846312035200473293549)
  ·
    refine ⟨3615692367013200177485081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9641846312035200473293549 3615692367013200177485081)
    ·
      refine ⟨2711769275259900133113811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3615692367013200177485081 2711769275259900133113811)
      ·
        refine ⟨4067653912889850199670717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2711769275259900133113811 4067653912889850199670717)
        ·
          refine ⟨1525370217333693824876519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4067653912889850199670717 1525370217333693824876519)
          ·
            refine ⟨2288055326000540737314779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1525370217333693824876519 2288055326000540737314779)
            ·
              refine ⟨3432082989000811105972169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2288055326000540737314779 3432082989000811105972169)
              ·
                refine ⟨2574062241750608329479127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3432082989000811105972169 2574062241750608329479127)
                ·
                  refine ⟨3861093362625912494218691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2574062241750608329479127 3861093362625912494218691)
                  ·
                    refine ⟨5791640043938868741328037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3861093362625912494218691 5791640043938868741328037)
                    ·
                      refine ⟨1085932508238537888999007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5791640043938868741328037 1085932508238537888999007)
                      ·
                        rfl

theorem cell23_2114846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_2114846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114846 prefixEnd_2114846 := by exact prefixLift 2114846
  have htrace : WordTrace (prefixWord ++ tailWord_2114846) baseStart_2114846 baseEnd_2114846 := by
    simpa [prefixWord, tailWord_2114846, baseEnd_2114846] using wordTrace_append hprefix tailTrace_2114846
  have hstable : (prefixWord ++ tailWord_2114846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114846).length < 2 ^ (prefixWord ++ tailWord_2114846).sum := by decide
  have hdescent : baseEnd_2114846 < baseStart_2114846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114878 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 2, 6]
def baseStart_2114878 : Nat := 118140960795 + 2114878 * 2 ^ 59
def prefixEnd_2114878 : Nat := 4983230072969 + 3 ^ 40 * 2114878 * 2
def baseEnd_2114878 : Nat := 361982979873160587932953

theorem tailTrace_2114878 : CollatzResearch.WordTrace tailWord_2114878 prefixEnd_2114878 361982979873160587932953 := by
  unfold tailWord_2114878
  simp only [CollatzResearch.WordTrace]
  refine ⟨9641992204020709156439161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51423958421443782167675525 9641992204020709156439161)
  ·
    refine ⟨7231494153015531867329371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9641992204020709156439161 7231494153015531867329371)
    ·
      refine ⟨10847241229523297800994057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7231494153015531867329371 10847241229523297800994057)
      ·
        refine ⟨8135430922142473350745543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10847241229523297800994057 8135430922142473350745543)
        ·
          refine ⟨12203146383213710026118315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8135430922142473350745543 12203146383213710026118315)
          ·
            refine ⟨18304719574820565039177473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12203146383213710026118315 18304719574820565039177473)
            ·
              refine ⟨13728539681115423779383105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18304719574820565039177473 13728539681115423779383105)
              ·
                refine ⟨10296404760836567834537329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13728539681115423779383105 10296404760836567834537329)
                ·
                  refine ⟨7722303570627425875902997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10296404760836567834537329 7722303570627425875902997)
                  ·
                    refine ⟨361982979873160587932953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7722303570627425875902997 361982979873160587932953)
                    ·
                      rfl

theorem cell23_2114878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_2114878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114878 prefixEnd_2114878 := by exact prefixLift 2114878
  have htrace : WordTrace (prefixWord ++ tailWord_2114878) baseStart_2114878 baseEnd_2114878 := by
    simpa [prefixWord, tailWord_2114878, baseEnd_2114878] using wordTrace_append hprefix tailTrace_2114878
  have hstable : (prefixWord ++ tailWord_2114878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114878).length < 2 ^ (prefixWord ++ tailWord_2114878).sum := by decide
  have hdescent : baseEnd_2114878 < baseStart_2114878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114885 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 4, 2, 2]
def baseStart_2114885 : Nat := 118140960795 + 2114885 * 2 ^ 59
def prefixEnd_2114885 : Nat := 4983230072969 + 3 ^ 40 * 2114885 * 2
def baseEnd_2114885 : Nat := 1085952533984063236411327

theorem tailTrace_2114885 : CollatzResearch.WordTrace tailWord_2114885 prefixEnd_2114885 1085952533984063236411327 := by
  unfold tailWord_2114885
  simp only [CollatzResearch.WordTrace]
  refine ⟨77136192943140313447018109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51424128628760208964678739 77136192943140313447018109)
  ·
    refine ⟨28926072353677617542631791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77136192943140313447018109 28926072353677617542631791)
    ·
      refine ⟨43389108530516426313947687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28926072353677617542631791 43389108530516426313947687)
      ·
        refine ⟨65083662795774639470921531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43389108530516426313947687 65083662795774639470921531)
        ·
          refine ⟨97625494193661959206382297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65083662795774639470921531 97625494193661959206382297)
          ·
            refine ⟨73219120645246469404786723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97625494193661959206382297 73219120645246469404786723)
            ·
              refine ⟨109828680967869704107180085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73219120645246469404786723 109828680967869704107180085)
              ·
                refine ⟨10296438840737784760048133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109828680967869704107180085 10296438840737784760048133)
                ·
                  refine ⟨1930582282638334642509025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10296438840737784760048133 1930582282638334642509025)
                  ·
                    refine ⟨1447936711978750981881769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1930582282638334642509025 1447936711978750981881769)
                    ·
                      refine ⟨1085952533984063236411327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1447936711978750981881769 1085952533984063236411327)
                      ·
                        rfl

theorem cell23_2114885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 2, 2].length) (baseStart_2114885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114885 prefixEnd_2114885 := by exact prefixLift 2114885
  have htrace : WordTrace (prefixWord ++ tailWord_2114885) baseStart_2114885 baseEnd_2114885 := by
    simpa [prefixWord, tailWord_2114885, baseEnd_2114885] using wordTrace_append hprefix tailTrace_2114885
  have hstable : (prefixWord ++ tailWord_2114885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114885).length < 2 ^ (prefixWord ++ tailWord_2114885).sum := by decide
  have hdescent : baseEnd_2114885 < baseStart_2114885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114925 : List Nat := [1, 5, 1, 1, 1, 3, 1, 5, 5]
def baseStart_2114925 : Nat := 118140960795 + 2114925 * 2 ^ 59
def prefixEnd_2114925 : Nat := 4983230072969 + 3 ^ 40 * 2114925 * 2
def baseEnd_2114925 : Nat := 120663674801138119990127

theorem tailTrace_2114925 : CollatzResearch.WordTrace tailWord_2114925 prefixEnd_2114925 120663674801138119990127 := by
  unfold tailWord_2114925
  simp only [CollatzResearch.WordTrace]
  refine ⟨77137651862995400278474229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51425101241996933518982819 77137651862995400278474229)
  ·
    refine ⟨7231654862155818776106959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77137651862995400278474229 7231654862155818776106959)
    ·
      refine ⟨10847482293233728164160439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7231654862155818776106959 10847482293233728164160439)
      ·
        refine ⟨16271223439850592246240659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10847482293233728164160439 16271223439850592246240659)
        ·
          refine ⟨24406835159775888369360989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16271223439850592246240659 24406835159775888369360989)
          ·
            refine ⟨9152563184915958138510371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24406835159775888369360989 9152563184915958138510371)
            ·
              refine ⟨13728844777373937207765557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9152563184915958138510371 13728844777373937207765557)
              ·
                refine ⟨1287079197878806613228021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13728844777373937207765557 1287079197878806613228021)
                ·
                  refine ⟨120663674801138119990127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1287079197878806613228021 120663674801138119990127)
                  ·
                    rfl

theorem cell23_2114925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_2114925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2114925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2114925 prefixEnd_2114925 := by exact prefixLift 2114925
  have htrace : WordTrace (prefixWord ++ tailWord_2114925) baseStart_2114925 baseEnd_2114925 := by
    simpa [prefixWord, tailWord_2114925, baseEnd_2114925] using wordTrace_append hprefix tailTrace_2114925
  have hstable : (prefixWord ++ tailWord_2114925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114925).length < 2 ^ (prefixWord ++ tailWord_2114925).sum := by decide
  have hdescent : baseEnd_2114925 < baseStart_2114925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115053 : List Nat := [1, 5, 1, 3, 2, 2, 2, 2, 1, 4]
def baseStart_2115053 : Nat := 118140960795 + 2115053 * 2 ^ 59
def prefixEnd_2115053 : Nat := 4983230072969 + 3 ^ 40 * 2115053 * 2
def baseEnd_2115053 : Nat := 362012932911339526370185

theorem tailTrace_2115053 : CollatzResearch.WordTrace tailWord_2115053 prefixEnd_2115053 362012932911339526370185 := by
  unfold tailWord_2115053
  simp only [CollatzResearch.WordTrace]
  refine ⟨77142320406531678139133813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51428213604354452092755875 77142320406531678139133813)
  ·
    refine ⟨7232092538112344825543795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77142320406531678139133813 7232092538112344825543795)
    ·
      refine ⟨10848138807168517238315693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7232092538112344825543795 10848138807168517238315693)
      ·
        refine ⟨4068052052688193964368385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10848138807168517238315693 4068052052688193964368385)
        ·
          refine ⟨3051039039516145473276289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4068052052688193964368385 3051039039516145473276289)
          ·
            refine ⟨2288279279637109104957217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3051039039516145473276289 2288279279637109104957217)
            ·
              refine ⟨1716209459727831828717913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2288279279637109104957217 1716209459727831828717913)
              ·
                refine ⟨1287157094795873871538435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1716209459727831828717913 1287157094795873871538435)
                ·
                  refine ⟨1930735642193810807307653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1287157094795873871538435 1930735642193810807307653)
                  ·
                    refine ⟨362012932911339526370185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1930735642193810807307653 362012932911339526370185)
                    ·
                      rfl

theorem cell23_2115053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_2115053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115053 prefixEnd_2115053 := by exact prefixLift 2115053
  have htrace : WordTrace (prefixWord ++ tailWord_2115053) baseStart_2115053 baseEnd_2115053 := by
    simpa [prefixWord, tailWord_2115053, baseEnd_2115053] using wordTrace_append hprefix tailTrace_2115053
  have hstable : (prefixWord ++ tailWord_2115053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115053).length < 2 ^ (prefixWord ++ tailWord_2115053).sum := by decide
  have hdescent : baseEnd_2115053 < baseStart_2115053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115065 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 2, 6, 2]
def baseStart_2115065 : Nat := 118140960795 + 2115065 * 2 ^ 59
def prefixEnd_2115065 : Nat := 4983230072969 + 3 ^ 40 * 2115065 * 2
def baseEnd_2115065 : Nat := 1086044960501872532160499

theorem tailTrace_2115065 : CollatzResearch.WordTrace tailWord_2115065 prefixEnd_2115065 1086044960501872532160499 := by
  unfold tailWord_2115065
  simp only [CollatzResearch.WordTrace]
  refine ⟨77142758082488204188570649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51428505388325469459047099 77142758082488204188570649)
  ·
    refine ⟨57857068561866153141427987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77142758082488204188570649 57857068561866153141427987)
    ·
      refine ⟨86785602842799229712141981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57857068561866153141427987 86785602842799229712141981)
      ·
        refine ⟨32544601066049711142053243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86785602842799229712141981 32544601066049711142053243)
        ·
          refine ⟨48816901599074566713079865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32544601066049711142053243 48816901599074566713079865)
          ·
            refine ⟨36612676199305925034809899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48816901599074566713079865 36612676199305925034809899)
            ·
              refine ⟨54919014298958887552214849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36612676199305925034809899 54919014298958887552214849)
              ·
                refine ⟨41189260724219165664161137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54919014298958887552214849 41189260724219165664161137)
                ·
                  refine ⟨30891945543164374248120853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41189260724219165664161137 30891945543164374248120853)
                  ·
                    refine ⟨1448059947335830042880665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30891945543164374248120853 1448059947335830042880665)
                    ·
                      refine ⟨1086044960501872532160499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1448059947335830042880665 1086044960501872532160499)
                      ·
                        rfl

theorem cell23_2115065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 6, 2].length) (baseStart_2115065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115065 prefixEnd_2115065 := by exact prefixLift 2115065
  have htrace : WordTrace (prefixWord ++ tailWord_2115065) baseStart_2115065 baseEnd_2115065 := by
    simpa [prefixWord, tailWord_2115065, baseEnd_2115065] using wordTrace_append hprefix tailTrace_2115065
  have hstable : (prefixWord ++ tailWord_2115065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115065).length < 2 ^ (prefixWord ++ tailWord_2115065).sum := by decide
  have hdescent : baseEnd_2115065 < baseStart_2115065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115086 : List Nat := [4, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2]
def baseStart_2115086 : Nat := 118140960795 + 2115086 * 2 ^ 59
def prefixEnd_2115086 : Nat := 4983230072969 + 3 ^ 40 * 2115086 * 2
def baseEnd_2115086 : Nat := 1086055743595616949997903

theorem tailTrace_2115086 : CollatzResearch.WordTrace tailWord_2115086 prefixEnd_2115086 1086055743595616949997903 := by
  unfold tailWord_2115086
  simp only [CollatzResearch.WordTrace]
  refine ⟨9642940501926515596885639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51429016010274749850056741 9642940501926515596885639)
  ·
    refine ⟨14464410752889773395328459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9642940501926515596885639 14464410752889773395328459)
    ·
      refine ⟨21696616129334660092992689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14464410752889773395328459 21696616129334660092992689)
      ·
        refine ⟨16272462097000995069744517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21696616129334660092992689 16272462097000995069744517)
        ·
          refine ⟨3051086643187686575577097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16272462097000995069744517 3051086643187686575577097)
          ·
            refine ⟨2288314982390764931682823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3051086643187686575577097 2288314982390764931682823)
            ·
              refine ⟨3432472473586147397524235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2288314982390764931682823 3432472473586147397524235)
              ·
                refine ⟨5148708710379221096286353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3432472473586147397524235 5148708710379221096286353)
                ·
                  refine ⟨3861531532784415822214765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5148708710379221096286353 3861531532784415822214765)
                  ·
                    refine ⟨1448074324794155933330537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3861531532784415822214765 1448074324794155933330537)
                    ·
                      refine ⟨1086055743595616949997903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1448074324794155933330537 1086055743595616949997903)
                      ·
                        rfl

theorem cell23_2115086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_2115086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115086 prefixEnd_2115086 := by exact prefixLift 2115086
  have htrace : WordTrace (prefixWord ++ tailWord_2115086) baseStart_2115086 baseEnd_2115086 := by
    simpa [prefixWord, tailWord_2115086, baseEnd_2115086] using wordTrace_append hprefix tailTrace_2115086
  have hstable : (prefixWord ++ tailWord_2115086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115086).length < 2 ^ (prefixWord ++ tailWord_2115086).sum := by decide
  have hdescent : baseEnd_2115086 < baseStart_2115086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115096 : List Nat := [2, 1, 2, 3, 5, 1, 2, 1, 1, 5]
def baseStart_2115096 : Nat := 118140960795 + 2115096 * 2 ^ 59
def prefixEnd_2115096 : Nat := 4983230072969 + 3 ^ 40 * 2115096 * 2
def baseEnd_2115096 : Nat := 362020292800720636957619

theorem tailTrace_2115096 : CollatzResearch.WordTrace tailWord_2115096 prefixEnd_2115096 362020292800720636957619 := by
  unfold tailWord_2115096
  simp only [CollatzResearch.WordTrace]
  refine ⟨38571944372687948241474571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51429259163583930988632761 38571944372687948241474571)
  ·
    refine ⟨57857916559031922362211857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38571944372687948241474571 57857916559031922362211857)
    ·
      refine ⟨43393437419273941771658893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57857916559031922362211857 43393437419273941771658893)
      ·
        refine ⟨16272539032227728164372085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43393437419273941771658893 16272539032227728164372085)
        ·
          refine ⟨1525550534271349515409883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16272539032227728164372085 1525550534271349515409883)
          ·
            refine ⟨2288325801407024273114825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1525550534271349515409883 2288325801407024273114825)
            ·
              refine ⟨1716244351055268204836119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2288325801407024273114825 1716244351055268204836119)
              ·
                refine ⟨2574366526582902307254179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1716244351055268204836119 2574366526582902307254179)
                ·
                  refine ⟨3861549789874353460881269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2574366526582902307254179 3861549789874353460881269)
                  ·
                    refine ⟨362020292800720636957619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3861549789874353460881269 362020292800720636957619)
                    ·
                      rfl

theorem cell23_2115096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 1, 5].length) (baseStart_2115096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115096 prefixEnd_2115096 := by exact prefixLift 2115096
  have htrace : WordTrace (prefixWord ++ tailWord_2115096) baseStart_2115096 baseEnd_2115096 := by
    simpa [prefixWord, tailWord_2115096, baseEnd_2115096] using wordTrace_append hprefix tailTrace_2115096
  have hstable : (prefixWord ++ tailWord_2115096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115096).length < 2 ^ (prefixWord ++ tailWord_2115096).sum := by decide
  have hdescent : baseEnd_2115096 < baseStart_2115096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115126 : List Nat := [5, 1, 2, 1, 4, 1, 1, 1, 1, 6]
def baseStart_2115126 : Nat := 118140960795 + 2115126 * 2 ^ 59
def prefixEnd_2115126 : Nat := 4983230072969 + 3 ^ 40 * 2115126 * 2
def baseEnd_2115126 : Nat := 362025427607265597832573

theorem tailTrace_2115126 : CollatzResearch.WordTrace tailWord_2115126 prefixEnd_2115126 362025427607265597832573 := by
  unfold tailWord_2115126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4821561433454200725408827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51429988623511474404360821 4821561433454200725408827)
  ·
    refine ⟨7232342150181301088113241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4821561433454200725408827 7232342150181301088113241)
    ·
      refine ⟨5424256612635975816084931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7232342150181301088113241 5424256612635975816084931)
      ·
        refine ⟨8136384918953963724127397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5424256612635975816084931 8136384918953963724127397)
        ·
          refine ⟨1525572172303868198273887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8136384918953963724127397 1525572172303868198273887)
          ·
            refine ⟨2288358258455802297410831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1525572172303868198273887 2288358258455802297410831)
            ·
              refine ⟨3432537387683703446116247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2288358258455802297410831 3432537387683703446116247)
              ·
                refine ⟨5148806081525555169174371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3432537387683703446116247 5148806081525555169174371)
                ·
                  refine ⟨7723209122288332753761557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5148806081525555169174371 7723209122288332753761557)
                  ·
                    refine ⟨362025427607265597832573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7723209122288332753761557 362025427607265597832573)
                    ·
                      rfl

theorem cell23_2115126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_2115126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115126 prefixEnd_2115126 := by exact prefixLift 2115126
  have htrace : WordTrace (prefixWord ++ tailWord_2115126) baseStart_2115126 baseEnd_2115126 := by
    simpa [prefixWord, tailWord_2115126, baseEnd_2115126] using wordTrace_append hprefix tailTrace_2115126
  have hstable : (prefixWord ++ tailWord_2115126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115126).length < 2 ^ (prefixWord ++ tailWord_2115126).sum := by decide
  have hdescent : baseEnd_2115126 < baseStart_2115126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115159 : List Nat := [1, 1, 3, 2, 2, 3, 2, 3, 1, 3, 2]
def baseStart_2115159 : Nat := 118140960795 + 2115159 * 2 ^ 59
def prefixEnd_2115159 : Nat := 4983230072969 + 3 ^ 40 * 2115159 * 2
def baseEnd_2115159 : Nat := 1086093227683395164385067

theorem tailTrace_2115159 : CollatzResearch.WordTrace tailWord_2115159 prefixEnd_2115159 1086093227683395164385067 := by
  unfold tailWord_2115159
  simp only [CollatzResearch.WordTrace]
  refine ⟨77146186544147658242492531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51430791029431772161661687 77146186544147658242492531)
  ·
    refine ⟨115719279816221487363738797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77146186544147658242492531 115719279816221487363738797)
    ·
      refine ⟨43394729931083057761402049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115719279816221487363738797 43394729931083057761402049)
      ·
        refine ⟨32546047448312293321051537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43394729931083057761402049 32546047448312293321051537)
        ·
          refine ⟨24409535586234219990788653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32546047448312293321051537 24409535586234219990788653)
          ·
            refine ⟨9153575844837832496545745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24409535586234219990788653 9153575844837832496545745)
            ·
              refine ⟨6865181883628374372409309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9153575844837832496545745 6865181883628374372409309)
              ·
                refine ⟨2574443206360640389653491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6865181883628374372409309 2574443206360640389653491)
                ·
                  refine ⟨3861664809540960584480237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2574443206360640389653491 3861664809540960584480237)
                  ·
                    refine ⟨1448124303577860219180089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3861664809540960584480237 1448124303577860219180089)
                    ·
                      refine ⟨1086093227683395164385067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1448124303577860219180089 1086093227683395164385067)
                      ·
                        rfl

theorem cell23_2115159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 3, 2].length) (baseStart_2115159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115159 prefixEnd_2115159 := by exact prefixLift 2115159
  have htrace : WordTrace (prefixWord ++ tailWord_2115159) baseStart_2115159 baseEnd_2115159 := by
    simpa [prefixWord, tailWord_2115159, baseEnd_2115159] using wordTrace_append hprefix tailTrace_2115159
  have hstable : (prefixWord ++ tailWord_2115159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115159).length < 2 ^ (prefixWord ++ tailWord_2115159).sum := by decide
  have hdescent : baseEnd_2115159 < baseStart_2115159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115185 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 2, 2, 4]
def baseStart_2115185 : Nat := 118140960795 + 2115185 * 2 ^ 59
def prefixEnd_2115185 : Nat := 4983230072969 + 3 ^ 40 * 2115185 * 2
def baseEnd_2115185 : Nat := 1086106578180412062659947

theorem tailTrace_2115185 : CollatzResearch.WordTrace tailWord_2115185 prefixEnd_2115185 1086106578180412062659947 := by
  unfold tailWord_2115185
  simp only [CollatzResearch.WordTrace]
  refine ⟨77147134842053464682939009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51431423228035643121959339 77147134842053464682939009)
  ·
    refine ⟨57860351131540098512204257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77147134842053464682939009 57860351131540098512204257)
    ·
      refine ⟨43395263348655073884153193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57860351131540098512204257 43395263348655073884153193)
      ·
        refine ⟨32546447511491305413114895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43395263348655073884153193 32546447511491305413114895)
        ·
          refine ⟨48819671267236958119672343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32546447511491305413114895 48819671267236958119672343)
          ·
            refine ⟨73229506900855437179508515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48819671267236958119672343 73229506900855437179508515)
            ·
              refine ⟨109844260351283155769262773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73229506900855437179508515 109844260351283155769262773)
              ·
                refine ⟨10297899407932795853368385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109844260351283155769262773 10297899407932795853368385)
                ·
                  refine ⟨7723424555949596890026289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10297899407932795853368385 7723424555949596890026289)
                  ·
                    refine ⟨5792568416962197667519717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7723424555949596890026289 5792568416962197667519717)
                    ·
                      refine ⟨1086106578180412062659947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5792568416962197667519717 1086106578180412062659947)
                      ·
                        rfl

theorem cell23_2115185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_2115185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115185 prefixEnd_2115185 := by exact prefixLift 2115185
  have htrace : WordTrace (prefixWord ++ tailWord_2115185) baseStart_2115185 baseEnd_2115185 := by
    simpa [prefixWord, tailWord_2115185, baseEnd_2115185] using wordTrace_append hprefix tailTrace_2115185
  have hstable : (prefixWord ++ tailWord_2115185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115185).length < 2 ^ (prefixWord ++ tailWord_2115185).sum := by decide
  have hdescent : baseEnd_2115185 < baseStart_2115185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115212 : List Nat := [2, 2, 1, 2, 1, 1, 4, 5, 5]
def baseStart_2115212 : Nat := 118140960795 + 2115212 * 2 ^ 59
def prefixEnd_2115212 : Nat := 4983230072969 + 3 ^ 40 * 2115212 * 2
def baseEnd_2115212 : Nat := 120680049128675939669147

theorem tailTrace_2115212 : CollatzResearch.WordTrace tailWord_2115212 prefixEnd_2115212 120680049128675939669147 := by
  unfold tailWord_2115212
  simp only [CollatzResearch.WordTrace]
  refine ⟨38574059806477824147085945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51432079741970432196114593 38574059806477824147085945)
  ·
    refine ⟨28930544854858368110314459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38574059806477824147085945 28930544854858368110314459)
    ·
      refine ⟨43395817282287552165471689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28930544854858368110314459 43395817282287552165471689)
      ·
        refine ⟨32546862961715664124103767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43395817282287552165471689 32546862961715664124103767)
        ·
          refine ⟨48820294442573496186155651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32546862961715664124103767 48820294442573496186155651)
          ·
            refine ⟨73230441663860244279233477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48820294442573496186155651 73230441663860244279233477)
            ·
              refine ⟨13730707811973795802356277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73230441663860244279233477 13730707811973795802356277)
              ·
                refine ⟨1287253857372543356470901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13730707811973795802356277 1287253857372543356470901)
                ·
                  refine ⟨120680049128675939669147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1287253857372543356470901 120680049128675939669147)
                  ·
                    rfl

theorem cell23_2115212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 5].length) (baseStart_2115212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115212 prefixEnd_2115212 := by exact prefixLift 2115212
  have htrace : WordTrace (prefixWord ++ tailWord_2115212) baseStart_2115212 baseEnd_2115212 := by
    simpa [prefixWord, tailWord_2115212, baseEnd_2115212] using wordTrace_append hprefix tailTrace_2115212
  have hstable : (prefixWord ++ tailWord_2115212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115212).length < 2 ^ (prefixWord ++ tailWord_2115212).sum := by decide
  have hdescent : baseEnd_2115212 < baseStart_2115212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115225 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 4, 5]
def baseStart_2115225 : Nat := 118140960795 + 2115225 * 2 ^ 59
def prefixEnd_2115225 : Nat := 4983230072969 + 3 ^ 40 * 2115225 * 2
def baseEnd_2115225 : Nat := 362042372468863968719921

theorem tailTrace_2115225 : CollatzResearch.WordTrace tailWord_2115225 prefixEnd_2115225 362042372468863968719921 := by
  unfold tailWord_2115225
  simp only [CollatzResearch.WordTrace]
  refine ⟨77148593761908551514395129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51432395841272367676263419 77148593761908551514395129)
  ·
    refine ⟨57861445321431413635796347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77148593761908551514395129 57861445321431413635796347)
    ·
      refine ⟨86792167982147120453694521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57861445321431413635796347 86792167982147120453694521)
      ·
        refine ⟨65094125986610340340270891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86792167982147120453694521 65094125986610340340270891)
        ·
          refine ⟨97641188979915510510406337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65094125986610340340270891 97641188979915510510406337)
          ·
            refine ⟨73230891734936632882804753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97641188979915510510406337 73230891734936632882804753)
            ·
              refine ⟨54923168801202474662103565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73230891734936632882804753 54923168801202474662103565)
              ·
                refine ⟨20596188300450927998288837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54923168801202474662103565 20596188300450927998288837)
                ·
                  refine ⟨3861785306334548999679157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20596188300450927998288837 3861785306334548999679157)
                  ·
                    refine ⟨362042372468863968719921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3861785306334548999679157 362042372468863968719921)
                    ·
                      rfl

theorem cell23_2115225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 5].length) (baseStart_2115225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115225 prefixEnd_2115225 := by exact prefixLift 2115225
  have htrace : WordTrace (prefixWord ++ tailWord_2115225) baseStart_2115225 baseEnd_2115225 := by
    simpa [prefixWord, tailWord_2115225, baseEnd_2115225] using wordTrace_append hprefix tailTrace_2115225
  have hstable : (prefixWord ++ tailWord_2115225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115225).length < 2 ^ (prefixWord ++ tailWord_2115225).sum := by decide
  have hdescent : baseEnd_2115225 < baseStart_2115225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115235 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 5]
def baseStart_2115235 : Nat := 118140960795 + 2115235 * 2 ^ 59
def prefixEnd_2115235 : Nat := 4983230072969 + 3 ^ 40 * 2115235 * 2
def baseEnd_2115235 : Nat := 1086132252213136867034717

theorem tailTrace_2115235 : CollatzResearch.WordTrace tailWord_2115235 prefixEnd_2115235 1086132252213136867034717 := by
  unfold tailWord_2115235
  simp only [CollatzResearch.WordTrace]
  refine ⟨77148958491872323222259159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51432638994581548814839439 77148958491872323222259159)
  ·
    refine ⟨115723437737808484833388739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77148958491872323222259159 115723437737808484833388739)
    ·
      refine ⟨173585156606712727250083109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115723437737808484833388739 173585156606712727250083109)
      ·
        refine ⟨32547216863758636359390583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173585156606712727250083109 32547216863758636359390583)
        ·
          refine ⟨48820825295637954539085875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32547216863758636359390583 48820825295637954539085875)
          ·
            refine ⟨73231237943456931808628813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48820825295637954539085875 73231237943456931808628813)
            ·
              refine ⟨27461714228796349428235805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73231237943456931808628813 27461714228796349428235805)
              ·
                refine ⟨10298142835798631035588427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27461714228796349428235805 10298142835798631035588427)
                ·
                  refine ⟨15447214253697946553382641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10298142835798631035588427 15447214253697946553382641)
                  ·
                    refine ⟨11585410690273459915036981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15447214253697946553382641 11585410690273459915036981)
                    ·
                      refine ⟨1086132252213136867034717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11585410690273459915036981 1086132252213136867034717)
                      ·
                        rfl

theorem cell23_2115235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_2115235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115235 prefixEnd_2115235 := by exact prefixLift 2115235
  have htrace : WordTrace (prefixWord ++ tailWord_2115235) baseStart_2115235 baseEnd_2115235 := by
    simpa [prefixWord, tailWord_2115235, baseEnd_2115235] using wordTrace_append hprefix tailTrace_2115235
  have hstable : (prefixWord ++ tailWord_2115235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115235).length < 2 ^ (prefixWord ++ tailWord_2115235).sum := by decide
  have hdescent : baseEnd_2115235 < baseStart_2115235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115240 : List Nat := [2, 1, 7, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_2115240 : Nat := 118140960795 + 2115240 * 2 ^ 59
def prefixEnd_2115240 : Nat := 4983230072969 + 3 ^ 40 * 2115240 * 2
def baseEnd_2115240 : Nat := 1086134819616409347472195

theorem tailTrace_2115240 : CollatzResearch.WordTrace tailWord_2115240 prefixEnd_2115240 1086134819616409347472195 := by
  unfold tailWord_2115240
  simp only [CollatzResearch.WordTrace]
  refine ⟨38574570428427104538095587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51432760571236139384127449 38574570428427104538095587)
  ·
    refine ⟨57861855642640656807143381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38574570428427104538095587 57861855642640656807143381)
    ·
      refine ⟨1356137241624390393917423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 57861855642640656807143381 1356137241624390393917423)
      ·
        refine ⟨2034205862436585590876135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1356137241624390393917423 2034205862436585590876135)
        ·
          refine ⟨3051308793654878386314203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2034205862436585590876135 3051308793654878386314203)
          ·
            refine ⟨4576963190482317579471305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3051308793654878386314203 4576963190482317579471305)
            ·
              refine ⟨3432722392861738184603479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4576963190482317579471305 3432722392861738184603479)
              ·
                refine ⟨5149083589292607276905219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3432722392861738184603479 5149083589292607276905219)
                ·
                  refine ⟨7723625383938910915357829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5149083589292607276905219 7723625383938910915357829)
                  ·
                    refine ⟨1448179759488545796629593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7723625383938910915357829 1448179759488545796629593)
                    ·
                      refine ⟨1086134819616409347472195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1448179759488545796629593 1086134819616409347472195)
                      ·
                        rfl

theorem cell23_2115240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_2115240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115240 prefixEnd_2115240 := by exact prefixLift 2115240
  have htrace : WordTrace (prefixWord ++ tailWord_2115240) baseStart_2115240 baseEnd_2115240 := by
    simpa [prefixWord, tailWord_2115240, baseEnd_2115240] using wordTrace_append hprefix tailTrace_2115240
  have hstable : (prefixWord ++ tailWord_2115240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115240).length < 2 ^ (prefixWord ++ tailWord_2115240).sum := by decide
  have hdescent : baseEnd_2115240 < baseStart_2115240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115272 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 5, 4]
def baseStart_2115272 : Nat := 118140960795 + 2115272 * 2 ^ 59
def prefixEnd_2115272 : Nat := 4983230072969 + 3 ^ 40 * 2115272 * 2
def baseEnd_2115272 : Nat := 362050416999117740757349

theorem tailTrace_2115272 : CollatzResearch.WordTrace tailWord_2115272 prefixEnd_2115272 362050416999117740757349 := by
  unfold tailWord_2115272
  simp only [CollatzResearch.WordTrace]
  refine ⟨38575153996369139270678035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51433538661825519027570713 38575153996369139270678035)
  ·
    refine ⟨57862730994553708906017053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38575153996369139270678035 57862730994553708906017053)
    ·
      refine ⟨21698524122957640839756395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57862730994553708906017053 21698524122957640839756395)
      ·
        refine ⟨32547786184436461259634593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21698524122957640839756395 32547786184436461259634593)
        ·
          refine ⟨24410839638327345944725945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32547786184436461259634593 24410839638327345944725945)
          ·
            refine ⟨18308129728745509458544459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24410839638327345944725945 18308129728745509458544459)
            ·
              refine ⟨27462194593118264187816689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18308129728745509458544459 27462194593118264187816689)
              ·
                refine ⟨20596645944838698140862517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27462194593118264187816689 20596645944838698140862517)
                ·
                  refine ⟨1930935557328627950705861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20596645944838698140862517 1930935557328627950705861)
                  ·
                    refine ⟨362050416999117740757349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1930935557328627950705861 362050416999117740757349)
                    ·
                      rfl

theorem cell23_2115272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_2115272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115272 prefixEnd_2115272 := by exact prefixLift 2115272
  have htrace : WordTrace (prefixWord ++ tailWord_2115272) baseStart_2115272 baseEnd_2115272 := by
    simpa [prefixWord, tailWord_2115272, baseEnd_2115272] using wordTrace_append hprefix tailTrace_2115272
  have hstable : (prefixWord ++ tailWord_2115272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115272).length < 2 ^ (prefixWord ++ tailWord_2115272).sum := by decide
  have hdescent : baseEnd_2115272 < baseStart_2115272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115275 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 4]
def baseStart_2115275 : Nat := 118140960795 + 2115275 * 2 ^ 59
def prefixEnd_2115275 : Nat := 4983230072969 + 3 ^ 40 * 2115275 * 2
def baseEnd_2115275 : Nat := 1086152791439316710534533

theorem tailTrace_2115275 : CollatzResearch.WordTrace tailWord_2115275 prefixEnd_2115275 1086152791439316710534533 := by
  unfold tailWord_2115275
  simp only [CollatzResearch.WordTrace]
  refine ⟨77150417411727410053715279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51433611607818273369143519 77150417411727410053715279)
  ·
    refine ⟨115725626117591115080572919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77150417411727410053715279 115725626117591115080572919)
    ·
      refine ⟨173588439176386672620859379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115725626117591115080572919 173588439176386672620859379)
      ·
        refine ⟨260382658764580008931289069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173588439176386672620859379 260382658764580008931289069)
        ·
          refine ⟨97643497036717503349233401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 260382658764580008931289069 97643497036717503349233401)
          ·
            refine ⟨73232622777538127511925051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97643497036717503349233401 73232622777538127511925051)
            ·
              refine ⟨109848934166307191267887577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73232622777538127511925051 109848934166307191267887577)
              ·
                refine ⟨82386700624730393450915683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109848934166307191267887577 82386700624730393450915683)
                ·
                  refine ⟨123580050937095590176373525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82386700624730393450915683 123580050937095590176373525)
                  ·
                    refine ⟨5792814887676355789517509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 123580050937095590176373525 5792814887676355789517509)
                    ·
                      refine ⟨1086152791439316710534533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5792814887676355789517509 1086152791439316710534533)
                      ·
                        rfl

theorem cell23_2115275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 4].length) (baseStart_2115275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115275 prefixEnd_2115275 := by exact prefixLift 2115275
  have htrace : WordTrace (prefixWord ++ tailWord_2115275) baseStart_2115275 baseEnd_2115275 := by
    simpa [prefixWord, tailWord_2115275, baseEnd_2115275] using wordTrace_append hprefix tailTrace_2115275
  have hstable : (prefixWord ++ tailWord_2115275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115275).length < 2 ^ (prefixWord ++ tailWord_2115275).sum := by decide
  have hdescent : baseEnd_2115275 < baseStart_2115275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115289 : List Nat := [1, 2, 1, 2, 3, 4, 2, 1, 3, 4]
def baseStart_2115289 : Nat := 118140960795 + 2115289 * 2 ^ 59
def prefixEnd_2115289 : Nat := 4983230072969 + 3 ^ 40 * 2115289 * 2
def baseEnd_2115289 : Nat := 362053326722826551919823

theorem tailTrace_2115289 : CollatzResearch.WordTrace tailWord_2115289 prefixEnd_2115289 362053326722826551919823 := by
  unfold tailWord_2115289
  simp only [CollatzResearch.WordTrace]
  refine ⟨77150928033676690444724921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51433952022451126963149947 77150928033676690444724921)
  ·
    refine ⟨57863196025257517833543691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77150928033676690444724921 57863196025257517833543691)
    ·
      refine ⟨86794794037886276750315537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57863196025257517833543691 86794794037886276750315537)
      ·
        refine ⟨65096095528414707562736653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86794794037886276750315537 65096095528414707562736653)
        ·
          refine ⟨24411035823155515336026245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65096095528414707562736653 24411035823155515336026245)
          ·
            refine ⟨4577069216841659125504921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24411035823155515336026245 4577069216841659125504921)
            ·
              refine ⟨3432801912631244344128691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4577069216841659125504921 3432801912631244344128691)
              ·
                refine ⟨5149202868946866516193037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3432801912631244344128691 5149202868946866516193037)
                ·
                  refine ⟨1930951075855074943572389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5149202868946866516193037 1930951075855074943572389)
                  ·
                    refine ⟨362053326722826551919823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1930951075855074943572389 362053326722826551919823)
                    ·
                      rfl

theorem cell23_2115289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 4].length) (baseStart_2115289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115289 prefixEnd_2115289 := by exact prefixLift 2115289
  have htrace : WordTrace (prefixWord ++ tailWord_2115289) baseStart_2115289 baseEnd_2115289 := by
    simpa [prefixWord, tailWord_2115289, baseEnd_2115289] using wordTrace_append hprefix tailTrace_2115289
  have hstable : (prefixWord ++ tailWord_2115289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115289).length < 2 ^ (prefixWord ++ tailWord_2115289).sum := by decide
  have hdescent : baseEnd_2115289 < baseStart_2115289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115305 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 3, 2, 6]
def baseStart_2115305 : Nat := 118140960795 + 2115305 * 2 ^ 59
def prefixEnd_2115305 : Nat := 4983230072969 + 3 ^ 40 * 2115305 * 2
def baseEnd_2115305 : Nat := 1086168195858951593159395

theorem tailTrace_2115305 : CollatzResearch.WordTrace tailWord_2115305 prefixEnd_2115305 1086168195858951593159395 := by
  unfold tailWord_2115305
  simp only [CollatzResearch.WordTrace]
  refine ⟨77151511601618725177307369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51434341067745816784871579 77151511601618725177307369)
  ·
    refine ⟨57863633701214043882980527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77151511601618725177307369 57863633701214043882980527)
    ·
      refine ⟨86795450551821065824470791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57863633701214043882980527 86795450551821065824470791)
      ·
        refine ⟨130193175827731598736706187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86795450551821065824470791 130193175827731598736706187)
        ·
          refine ⟨195289763741597398105059281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130193175827731598736706187 195289763741597398105059281)
          ·
            refine ⟨146467322806198048578794461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195289763741597398105059281 146467322806198048578794461)
            ·
              refine ⟨54925246052324268217047923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146467322806198048578794461 54925246052324268217047923)
              ·
                refine ⟨82387869078486402325571885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54925246052324268217047923 82387869078486402325571885)
                ·
                  refine ⟨30895450904432400872089457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82387869078486402325571885 30895450904432400872089457)
                  ·
                    refine ⟨23171588178324300654067093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30895450904432400872089457 23171588178324300654067093)
                    ·
                      refine ⟨1086168195858951593159395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23171588178324300654067093 1086168195858951593159395)
                      ·
                        rfl

theorem cell23_2115305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_2115305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115305 prefixEnd_2115305 := by exact prefixLift 2115305
  have htrace : WordTrace (prefixWord ++ tailWord_2115305) baseStart_2115305 baseEnd_2115305 := by
    simpa [prefixWord, tailWord_2115305, baseEnd_2115305] using wordTrace_append hprefix tailTrace_2115305
  have hstable : (prefixWord ++ tailWord_2115305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115305).length < 2 ^ (prefixWord ++ tailWord_2115305).sum := by decide
  have hdescent : baseEnd_2115305 < baseStart_2115305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115329 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 5, 1, 3]
def baseStart_2115329 : Nat := 118140960795 + 2115329 * 2 ^ 59
def prefixEnd_2115329 : Nat := 4983230072969 + 3 ^ 40 * 2115329 * 2
def baseEnd_2115329 : Nat := 1086180519394659499259285

theorem tailTrace_2115329 : CollatzResearch.WordTrace tailWord_2115329 prefixEnd_2115329 1086180519394659499259285 := by
  unfold tailWord_2115329
  simp only [CollatzResearch.WordTrace]
  refine ⟨77152386953531777276181041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51434924635687851517454027 77152386953531777276181041)
  ·
    refine ⟨57864290215148832957135781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77152386953531777276181041 57864290215148832957135781)
    ·
      refine ⟨10849554415340406179462959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57864290215148832957135781 10849554415340406179462959)
      ·
        refine ⟨16274331623010609269194439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10849554415340406179462959 16274331623010609269194439)
        ·
          refine ⟨24411497434515913903791659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16274331623010609269194439 24411497434515913903791659)
          ·
            refine ⟨36617246151773870855687489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24411497434515913903791659 36617246151773870855687489)
            ·
              refine ⟨27462934613830403141765617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36617246151773870855687489 27462934613830403141765617)
              ·
                refine ⟨20597200960372802356324213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27462934613830403141765617 20597200960372802356324213)
                ·
                  refine ⟨1930987590034950220905395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20597200960372802356324213 1930987590034950220905395)
                  ·
                    refine ⟨2896481385052425331358093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1930987590034950220905395 2896481385052425331358093)
                    ·
                      refine ⟨1086180519394659499259285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2896481385052425331358093 1086180519394659499259285)
                      ·
                        rfl

theorem cell23_2115329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_2115329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115329 prefixEnd_2115329 := by exact prefixLift 2115329
  have htrace : WordTrace (prefixWord ++ tailWord_2115329) baseStart_2115329 baseEnd_2115329 := by
    simpa [prefixWord, tailWord_2115329, baseEnd_2115329] using wordTrace_append hprefix tailTrace_2115329
  have hstable : (prefixWord ++ tailWord_2115329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115329).length < 2 ^ (prefixWord ++ tailWord_2115329).sum := by decide
  have hdescent : baseEnd_2115329 < baseStart_2115329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115339 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 4, 3, 2]
def baseStart_2115339 : Nat := 118140960795 + 2115339 * 2 ^ 59
def prefixEnd_2115339 : Nat := 4983230072969 + 3 ^ 40 * 2115339 * 2
def baseEnd_2115339 : Nat := 1086185654201204460134239

theorem tailTrace_2115339 : CollatzResearch.WordTrace tailWord_2115339 prefixEnd_2115339 1086185654201204460134239 := by
  unfold tailWord_2115339
  simp only [CollatzResearch.WordTrace]
  refine ⟨77152751683495548984045071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51435167788997032656030047 77152751683495548984045071)
  ·
    refine ⟨115729127525243323476067607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77152751683495548984045071 115729127525243323476067607)
    ·
      refine ⟨173593691287864985214101411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115729127525243323476067607 173593691287864985214101411)
      ·
        refine ⟨260390536931797477821152117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173593691287864985214101411 260390536931797477821152117)
        ·
          refine ⟨24411612837356013545733011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 260390536931797477821152117 24411612837356013545733011)
          ·
            refine ⟨36617419256034020318599517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24411612837356013545733011 36617419256034020318599517)
            ·
              refine ⟨13731532221012757619474819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36617419256034020318599517 13731532221012757619474819)
              ·
                refine ⟨20597298331519136429212229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13731532221012757619474819 20597298331519136429212229)
                ·
                  refine ⟨3861993437159838080477293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20597298331519136429212229 3861993437159838080477293)
                  ·
                    refine ⟨1448247538934939280178985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3861993437159838080477293 1448247538934939280178985)
                    ·
                      refine ⟨1086185654201204460134239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1448247538934939280178985 1086185654201204460134239)
                      ·
                        rfl

theorem cell23_2115339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 3, 2].length) (baseStart_2115339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115339 prefixEnd_2115339 := by exact prefixLift 2115339
  have htrace : WordTrace (prefixWord ++ tailWord_2115339) baseStart_2115339 baseEnd_2115339 := by
    simpa [prefixWord, tailWord_2115339, baseEnd_2115339] using wordTrace_append hprefix tailTrace_2115339
  have hstable : (prefixWord ++ tailWord_2115339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115339).length < 2 ^ (prefixWord ++ tailWord_2115339).sum := by decide
  have hdescent : baseEnd_2115339 < baseStart_2115339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115379 : List Nat := [1, 1, 1, 2, 7, 1, 1, 2, 1, 6]
def baseStart_2115379 : Nat := 118140960795 + 2115379 * 2 ^ 59
def prefixEnd_2115379 : Nat := 4983230072969 + 3 ^ 40 * 2115379 * 2
def baseEnd_2115379 : Nat := 362068731142461434544685

theorem tailTrace_2115379 : CollatzResearch.WordTrace tailWord_2115379 prefixEnd_2115379 362068731142461434544685 := by
  unfold tailWord_2115379
  simp only [CollatzResearch.WordTrace]
  refine ⟨77154210603350635815501191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51436140402233757210334127 77154210603350635815501191)
  ·
    refine ⟨115731315905025953723251787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77154210603350635815501191 115731315905025953723251787)
    ·
      refine ⟨173596973857538930584877681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115731315905025953723251787 173596973857538930584877681)
      ·
        refine ⟨130197730393154197938658261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173596973857538930584877681 130197730393154197938658261)
        ·
          refine ⟨3051509306089551514187303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 130197730393154197938658261 3051509306089551514187303)
          ·
            refine ⟨4577263959134327271280955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3051509306089551514187303 4577263959134327271280955)
            ·
              refine ⟨6865895938701490906921433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4577263959134327271280955 6865895938701490906921433)
              ·
                refine ⟨5149421954026118180191075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6865895938701490906921433 5149421954026118180191075)
                ·
                  refine ⟨7724132931039177270286613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5149421954026118180191075 7724132931039177270286613)
                  ·
                    refine ⟨362068731142461434544685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7724132931039177270286613 362068731142461434544685)
                    ·
                      rfl

theorem cell23_2115379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 6].length) (baseStart_2115379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115379 prefixEnd_2115379 := by exact prefixLift 2115379
  have htrace : WordTrace (prefixWord ++ tailWord_2115379) baseStart_2115379 baseEnd_2115379 := by
    simpa [prefixWord, tailWord_2115379, baseEnd_2115379] using wordTrace_append hprefix tailTrace_2115379
  have hstable : (prefixWord ++ tailWord_2115379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115379).length < 2 ^ (prefixWord ++ tailWord_2115379).sum := by decide
  have hdescent : baseEnd_2115379 < baseStart_2115379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115409 : List Nat := [1, 2, 2, 1, 5, 3, 1, 8]
def baseStart_2115409 : Nat := 118140960795 + 2115409 * 2 ^ 59
def prefixEnd_2115409 : Nat := 4983230072969 + 3 ^ 40 * 2115409 * 2
def baseEnd_2115409 : Nat := 40230429549889599491071

theorem tailTrace_2115409 : CollatzResearch.WordTrace tailWord_2115409 prefixEnd_2115409 40230429549889599491071 := by
  unfold tailWord_2115409
  simp only [CollatzResearch.WordTrace]
  refine ⟨77155304793241950939093281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51436869862161300626062187 77155304793241950939093281)
  ·
    refine ⟨57866478594931463204319961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77155304793241950939093281 57866478594931463204319961)
    ·
      refine ⟨43399858946198597403239971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57866478594931463204319961 43399858946198597403239971)
      ·
        refine ⟨65099788419297896104859957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43399858946198597403239971 65099788419297896104859957)
        ·
          refine ⟨6103105164309177759830621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65099788419297896104859957 6103105164309177759830621)
          ·
            refine ⟨2288664436615941659936483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6103105164309177759830621 2288664436615941659936483)
            ·
              refine ⟨3432996654923912489904725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2288664436615941659936483 3432996654923912489904725)
              ·
                refine ⟨40230429549889599491071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3432996654923912489904725 40230429549889599491071)
                ·
                  rfl

theorem cell23_2115409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 8].length) (baseStart_2115409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115409 prefixEnd_2115409 := by exact prefixLift 2115409
  have htrace : WordTrace (prefixWord ++ tailWord_2115409) baseStart_2115409 baseEnd_2115409 := by
    simpa [prefixWord, tailWord_2115409, baseEnd_2115409] using wordTrace_append hprefix tailTrace_2115409
  have hstable : (prefixWord ++ tailWord_2115409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115409).length < 2 ^ (prefixWord ++ tailWord_2115409).sum := by decide
  have hdescent : baseEnd_2115409 < baseStart_2115409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115420 : List Nat := [2, 2, 4, 2, 2, 1, 1, 2, 3, 2, 2]
def baseStart_2115420 : Nat := 118140960795 + 2115420 * 2 ^ 59
def prefixEnd_2115420 : Nat := 4983230072969 + 3 ^ 40 * 2115420 * 2
def baseEnd_2115420 : Nat := 1086227246134218643221367

theorem tailTrace_2115420 : CollatzResearch.WordTrace tailWord_2115420 prefixEnd_2115420 1086227246134218643221367 := by
  unfold tailWord_2115420
  simp only [CollatzResearch.WordTrace]
  refine ⟨38577852998101049908871857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51437137330801399878495809 38577852998101049908871857)
  ·
    refine ⟨28933389748575787431653893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38577852998101049908871857 28933389748575787431653893)
    ·
      refine ⟨5425010577857960143435105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28933389748575787431653893 5425010577857960143435105)
      ·
        refine ⟨4068757933393470107576329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5425010577857960143435105 4068757933393470107576329)
        ·
          refine ⟨3051568450045102580682247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4068757933393470107576329 3051568450045102580682247)
          ·
            refine ⟨4577352675067653871023371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3051568450045102580682247 4577352675067653871023371)
            ·
              refine ⟨6866029012601480806535057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4577352675067653871023371 6866029012601480806535057)
              ·
                refine ⟨5149521759451110604901293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6866029012601480806535057 5149521759451110604901293)
                ·
                  refine ⟨1931070659794166476837985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5149521759451110604901293 1931070659794166476837985)
                  ·
                    refine ⟨1448302994845624857628489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1931070659794166476837985 1448302994845624857628489)
                    ·
                      refine ⟨1086227246134218643221367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1448302994845624857628489 1086227246134218643221367)
                      ·
                        rfl

theorem cell23_2115420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_2115420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115420 prefixEnd_2115420 := by exact prefixLift 2115420
  have htrace : WordTrace (prefixWord ++ tailWord_2115420) baseStart_2115420 baseEnd_2115420 := by
    simpa [prefixWord, tailWord_2115420, baseEnd_2115420] using wordTrace_append hprefix tailTrace_2115420
  have hstable : (prefixWord ++ tailWord_2115420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115420).length < 2 ^ (prefixWord ++ tailWord_2115420).sum := by decide
  have hdescent : baseEnd_2115420 < baseStart_2115420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115426 : List Nat := [3, 3, 2, 1, 2, 2, 3, 7]
def baseStart_2115426 : Nat := 118140960795 + 2115426 * 2 ^ 59
def prefixEnd_2115426 : Nat := 4983230072969 + 3 ^ 40 * 2115426 * 2
def baseEnd_2115426 : Nat := 40230752852523911842457

theorem tailTrace_2115426 : CollatzResearch.WordTrace tailWord_2115426 prefixEnd_2115426 40230752852523911842457 := by
  unfold tailWord_2115426
  simp only [CollatzResearch.WordTrace]
  refine ⟨19288981208545090710615533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51437283222786908561641421 19288981208545090710615533)
  ·
    refine ⟨7233367953204409016480825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19288981208545090710615533 7233367953204409016480825)
    ·
      refine ⟨5425025964903306762360619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7233367953204409016480825 5425025964903306762360619)
      ·
        refine ⟨8137538947354960143540929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5425025964903306762360619 8137538947354960143540929)
        ·
          refine ⟨6103154210516220107655697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8137538947354960143540929 6103154210516220107655697)
          ·
            refine ⟨4577365657887165080741773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6103154210516220107655697 4577365657887165080741773)
            ·
              refine ⟨1716512121707686905278165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4577365657887165080741773 1716512121707686905278165)
              ·
                refine ⟨40230752852523911842457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1716512121707686905278165 40230752852523911842457)
                ·
                  rfl

theorem cell23_2115426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 7].length) (baseStart_2115426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115426 prefixEnd_2115426 := by exact prefixLift 2115426
  have htrace : WordTrace (prefixWord ++ tailWord_2115426) baseStart_2115426 baseEnd_2115426 := by
    simpa [prefixWord, tailWord_2115426, baseEnd_2115426] using wordTrace_append hprefix tailTrace_2115426
  have hstable : (prefixWord ++ tailWord_2115426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115426).length < 2 ^ (prefixWord ++ tailWord_2115426).sum := by decide
  have hdescent : baseEnd_2115426 < baseStart_2115426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115470 : List Nat := [4, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3]
def baseStart_2115470 : Nat := 118140960795 + 2115470 * 2 ^ 59
def prefixEnd_2115470 : Nat := 4983230072969 + 3 ^ 40 * 2115470 * 2
def baseEnd_2115470 : Nat := 1086252920166943447596137

theorem tailTrace_2115470 : CollatzResearch.WordTrace tailWord_2115470 prefixEnd_2115470 1086252920166943447596137 := by
  unfold tailWord_2115470
  simp only [CollatzResearch.WordTrace]
  refine ⟨9644691205752619794632983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51438353097347305571375909 9644691205752619794632983)
  ·
    refine ⟨14467036808628929691949475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9644691205752619794632983 14467036808628929691949475)
    ·
      refine ⟨21700555212943394537924213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14467036808628929691949475 21700555212943394537924213)
      ·
        refine ⟨2034427051213443237930395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21700555212943394537924213 2034427051213443237930395)
        ·
          refine ⟨3051640576820164856895593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2034427051213443237930395 3051640576820164856895593)
          ·
            refine ⟨2288730432615123642671695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3051640576820164856895593 2288730432615123642671695)
            ·
              refine ⟨3433095648922685464007543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2288730432615123642671695 3433095648922685464007543)
              ·
                refine ⟨5149643473384028196011315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3433095648922685464007543 5149643473384028196011315)
                ·
                  refine ⟨7724465210076042294016973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5149643473384028196011315 7724465210076042294016973)
                  ·
                    refine ⟨2896674453778515860256365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7724465210076042294016973 2896674453778515860256365)
                    ·
                      refine ⟨1086252920166943447596137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2896674453778515860256365 1086252920166943447596137)
                      ·
                        rfl

theorem cell23_2115470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_2115470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115470 prefixEnd_2115470 := by exact prefixLift 2115470
  have htrace : WordTrace (prefixWord ++ tailWord_2115470) baseStart_2115470 baseEnd_2115470 := by
    simpa [prefixWord, tailWord_2115470, baseEnd_2115470] using wordTrace_append hprefix tailTrace_2115470
  have hstable : (prefixWord ++ tailWord_2115470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115470).length < 2 ^ (prefixWord ++ tailWord_2115470).sum := by decide
  have hdescent : baseEnd_2115470 < baseStart_2115470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115610 : List Nat := [3, 1, 1, 3, 1, 4, 2, 3, 1, 4]
def baseStart_2115610 : Nat := 118140960795 + 2115610 * 2 ^ 59
def prefixEnd_2115610 : Nat := 4983230072969 + 3 ^ 40 * 2115610 * 2
def baseEnd_2115610 : Nat := 362108269152857633281831

theorem tailTrace_2115610 : CollatzResearch.WordTrace tailWord_2115610 prefixEnd_2115610 362108269152857633281831 := by
  unfold tailWord_2115610
  simp only [CollatzResearch.WordTrace]
  refine ⟨19290658966378440566790071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51441757243675841511440189 19290658966378440566790071)
  ·
    refine ⟨28935988449567660850185107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19290658966378440566790071 28935988449567660850185107)
    ·
      refine ⟨43403982674351491275277661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28935988449567660850185107 43403982674351491275277661)
      ·
        refine ⟨16276493502881809228229123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43403982674351491275277661 16276493502881809228229123)
        ·
          refine ⟨24414740254322713842343685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16276493502881809228229123 24414740254322713842343685)
          ·
            refine ⟨4577763797685508845439441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24414740254322713842343685 4577763797685508845439441)
            ·
              refine ⟨3433322848264131634079581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4577763797685508845439441 3433322848264131634079581)
              ·
                refine ⟨1287496068099049362779843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3433322848264131634079581 1287496068099049362779843)
                ·
                  refine ⟨1931244102148574044169765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1287496068099049362779843 1931244102148574044169765)
                  ·
                    refine ⟨362108269152857633281831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1931244102148574044169765 362108269152857633281831)
                    ·
                      rfl

theorem cell23_2115610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 1, 4].length) (baseStart_2115610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115610 prefixEnd_2115610 := by exact prefixLift 2115610
  have htrace : WordTrace (prefixWord ++ tailWord_2115610) baseStart_2115610 baseEnd_2115610 := by
    simpa [prefixWord, tailWord_2115610, baseEnd_2115610] using wordTrace_append hprefix tailTrace_2115610
  have hstable : (prefixWord ++ tailWord_2115610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115610).length < 2 ^ (prefixWord ++ tailWord_2115610).sum := by decide
  have hdescent : baseEnd_2115610 < baseStart_2115610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115623 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 8]
def baseStart_2115623 : Nat := 118140960795 + 2115623 * 2 ^ 59
def prefixEnd_2115623 : Nat := 4983230072969 + 3 ^ 40 * 2115623 * 2
def baseEnd_2115623 : Nat := 120703498078564594331437

theorem tailTrace_2115623 : CollatzResearch.WordTrace tailWord_2115623 prefixEnd_2115623 120703498078564594331437 := by
  unfold tailWord_2115623
  simp only [CollatzResearch.WordTrace]
  refine ⟨77163110014466665487383523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51442073342977776991589015 77163110014466665487383523)
  ·
    refine ⟨115744665021699998231075285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77163110014466665487383523 115744665021699998231075285)
    ·
      refine ⟨2712765586446093708540827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 115744665021699998231075285 2712765586446093708540827)
      ·
        refine ⟨4069148379669140562811241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2712765586446093708540827 4069148379669140562811241)
        ·
          refine ⟨3051861284751855422108431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4069148379669140562811241 3051861284751855422108431)
          ·
            refine ⟨4577791927127783133162647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3051861284751855422108431 4577791927127783133162647)
            ·
              refine ⟨6866687890691674699743971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4577791927127783133162647 6866687890691674699743971)
              ·
                refine ⟨10300031836037512049615957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6866687890691674699743971 10300031836037512049615957)
                ·
                  refine ⟨120703498078564594331437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10300031836037512049615957 120703498078564594331437)
                  ·
                    rfl

theorem cell23_2115623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 8].length) (baseStart_2115623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115623 prefixEnd_2115623 := by exact prefixLift 2115623
  have htrace : WordTrace (prefixWord ++ tailWord_2115623) baseStart_2115623 baseEnd_2115623 := by
    simpa [prefixWord, tailWord_2115623, baseEnd_2115623] using wordTrace_append hprefix tailTrace_2115623
  have hstable : (prefixWord ++ tailWord_2115623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115623).length < 2 ^ (prefixWord ++ tailWord_2115623).sum := by decide
  have hdescent : baseEnd_2115623 < baseStart_2115623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115626 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_2115626 : Nat := 118140960795 + 2115626 * 2 ^ 59
def prefixEnd_2115626 : Nat := 4983230072969 + 3 ^ 40 * 2115626 * 2
def baseEnd_2115626 : Nat := 1086333023149044837245419

theorem tailTrace_2115626 : CollatzResearch.WordTrace tailWord_2115626 prefixEnd_2115626 1086333023149044837245419 := by
  unfold tailWord_2115626
  simp only [CollatzResearch.WordTrace]
  refine ⟨19290804858363949249935683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51442146288970531333161821 19290804858363949249935683)
  ·
    refine ⟨28936207287545923874903525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19290804858363949249935683 28936207287545923874903525)
    ·
      refine ⟨5425538866414860726544411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28936207287545923874903525 5425538866414860726544411)
      ·
        refine ⟨8138308299622291089816617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5425538866414860726544411 8138308299622291089816617)
        ·
          refine ⟨6103731224716718317362463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8138308299622291089816617 6103731224716718317362463)
          ·
            refine ⟨9155596837075077476043695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6103731224716718317362463 9155596837075077476043695)
            ·
              refine ⟨13733395255612616214065543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9155596837075077476043695 13733395255612616214065543)
              ·
                refine ⟨20600092883418924321098315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13733395255612616214065543 20600092883418924321098315)
                ·
                  refine ⟨30900139325128386481647473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20600092883418924321098315 30900139325128386481647473)
                  ·
                    refine ⟨23175104493846289861235605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30900139325128386481647473 23175104493846289861235605)
                    ·
                      refine ⟨1086333023149044837245419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23175104493846289861235605 1086333023149044837245419)
                      ·
                        rfl

theorem cell23_2115626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_2115626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115626 prefixEnd_2115626 := by exact prefixLift 2115626
  have htrace : WordTrace (prefixWord ++ tailWord_2115626) baseStart_2115626 baseEnd_2115626 := by
    simpa [prefixWord, tailWord_2115626, baseEnd_2115626] using wordTrace_append hprefix tailTrace_2115626
  have hstable : (prefixWord ++ tailWord_2115626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115626).length < 2 ^ (prefixWord ++ tailWord_2115626).sum := by decide
  have hdescent : baseEnd_2115626 < baseStart_2115626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115633 : List Nat := [1, 2, 2, 3, 1, 3, 1, 3, 3, 1, 3]
def baseStart_2115633 : Nat := 118140960795 + 2115633 * 2 ^ 59
def prefixEnd_2115633 : Nat := 4983230072969 + 3 ^ 40 * 2115633 * 2
def baseEnd_2115633 : Nat := 1086336617513626309857887

theorem tailTrace_2115633 : CollatzResearch.WordTrace tailWord_2115633 prefixEnd_2115633 1086336617513626309857887 := by
  unfold tailWord_2115633
  simp only [CollatzResearch.WordTrace]
  refine ⟨77163474744430437195247553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51442316496286958130165035 77163474744430437195247553)
  ·
    refine ⟨57872606058322827896435665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77163474744430437195247553 57872606058322827896435665)
    ·
      refine ⟨43404454543742120922326749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57872606058322827896435665 43404454543742120922326749)
      ·
        refine ⟨16276670453903295345872531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43404454543742120922326749 16276670453903295345872531)
        ·
          refine ⟨24415005680854943018808797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16276670453903295345872531 24415005680854943018808797)
          ·
            refine ⟨9155627130320603632053299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24415005680854943018808797 9155627130320603632053299)
            ·
              refine ⟨13733440695480905448079949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9155627130320603632053299 13733440695480905448079949)
              ·
                refine ⟨5150040260805339543029981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13733440695480905448079949 5150040260805339543029981)
                ·
                  refine ⟨1931265097802002328636243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5150040260805339543029981 1931265097802002328636243)
                  ·
                    refine ⟨2896897646703003492954365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1931265097802002328636243 2896897646703003492954365)
                    ·
                      refine ⟨1086336617513626309857887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2896897646703003492954365 1086336617513626309857887)
                      ·
                        rfl

theorem cell23_2115633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_2115633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115633 prefixEnd_2115633 := by exact prefixLift 2115633
  have htrace : WordTrace (prefixWord ++ tailWord_2115633) baseStart_2115633 baseEnd_2115633 := by
    simpa [prefixWord, tailWord_2115633, baseEnd_2115633] using wordTrace_append hprefix tailTrace_2115633
  have hstable : (prefixWord ++ tailWord_2115633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115633).length < 2 ^ (prefixWord ++ tailWord_2115633).sum := by decide
  have hdescent : baseEnd_2115633 < baseStart_2115633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115677 : List Nat := [1, 4, 4, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_2115677 : Nat := 118140960795 + 2115677 * 2 ^ 59
def prefixEnd_2115677 : Nat := 4983230072969 + 3 ^ 40 * 2115677 * 2
def baseEnd_2115677 : Nat := 1086359210662424137707685

theorem tailTrace_2115677 : CollatzResearch.WordTrace tailWord_2115677 prefixEnd_2115677 1086359210662424137707685 := by
  unfold tailWord_2115677
  simp only [CollatzResearch.WordTrace]
  refine ⟨77165079556271032709849285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51443386370847355139899523 77165079556271032709849285)
  ·
    refine ⟨14468452416800818633096741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77165079556271032709849285 14468452416800818633096741)
    ·
      refine ⟨2712834828150153493705639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14468452416800818633096741 2712834828150153493705639)
      ·
        refine ⟨4069252242225230240558459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2712834828150153493705639 4069252242225230240558459)
        ·
          refine ⟨6103878363337845360837689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4069252242225230240558459 6103878363337845360837689)
          ·
            refine ⟨4577908772503384020628267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6103878363337845360837689 4577908772503384020628267)
            ·
              refine ⟨6866863158755076030942401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4577908772503384020628267 6866863158755076030942401)
              ·
                refine ⟨5150147369066307023206801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6866863158755076030942401 5150147369066307023206801)
                ·
                  refine ⟨3862610526799730267405101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5150147369066307023206801 3862610526799730267405101)
                  ·
                    refine ⟨1448478947549898850276913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3862610526799730267405101 1448478947549898850276913)
                    ·
                      refine ⟨1086359210662424137707685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1448478947549898850276913 1086359210662424137707685)
                      ·
                        rfl

theorem cell23_2115677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_2115677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115677 prefixEnd_2115677 := by exact prefixLift 2115677
  have htrace : WordTrace (prefixWord ++ tailWord_2115677) baseStart_2115677 baseEnd_2115677 := by
    simpa [prefixWord, tailWord_2115677, baseEnd_2115677] using wordTrace_append hprefix tailTrace_2115677
  have hstable : (prefixWord ++ tailWord_2115677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115677).length < 2 ^ (prefixWord ++ tailWord_2115677).sum := by decide
  have hdescent : baseEnd_2115677 < baseStart_2115677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115693 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 3, 2, 3]
def baseStart_2115693 : Nat := 118140960795 + 2115693 * 2 ^ 59
def prefixEnd_2115693 : Nat := 4983230072969 + 3 ^ 40 * 2115693 * 2
def baseEnd_2115693 : Nat := 1086367426352896075107611

theorem tailTrace_2115693 : CollatzResearch.WordTrace tailWord_2115693 prefixEnd_2115693 1086367426352896075107611 := by
  unfold tailWord_2115693
  simp only [CollatzResearch.WordTrace]
  refine ⟨77165663124213067442431733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51443775416142044961621155 77165663124213067442431733)
  ·
    refine ⟨7234280917894975072727975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77165663124213067442431733 7234280917894975072727975)
    ·
      refine ⟨10851421376842462609091963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7234280917894975072727975 10851421376842462609091963)
      ·
        refine ⟨16277132065263693913637945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10851421376842462609091963 16277132065263693913637945)
        ·
          refine ⟨12207849048947770435228459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16277132065263693913637945 12207849048947770435228459)
          ·
            refine ⟨18311773573421655652842689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12207849048947770435228459 18311773573421655652842689)
            ·
              refine ⟨13733830180066241739632017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18311773573421655652842689 13733830180066241739632017)
              ·
                refine ⟨10300372635049681304724013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13733830180066241739632017 10300372635049681304724013)
                ·
                  refine ⟨3862639738143630489271505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10300372635049681304724013 3862639738143630489271505)
                  ·
                    refine ⟨2896979803607722866953629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3862639738143630489271505 2896979803607722866953629)
                    ·
                      refine ⟨1086367426352896075107611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2896979803607722866953629 1086367426352896075107611)
                      ·
                        rfl

theorem cell23_2115693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_2115693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115693 prefixEnd_2115693 := by exact prefixLift 2115693
  have htrace : WordTrace (prefixWord ++ tailWord_2115693) baseStart_2115693 baseEnd_2115693 := by
    simpa [prefixWord, tailWord_2115693, baseEnd_2115693] using wordTrace_append hprefix tailTrace_2115693
  have hstable : (prefixWord ++ tailWord_2115693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115693).length < 2 ^ (prefixWord ++ tailWord_2115693).sum := by decide
  have hdescent : baseEnd_2115693 < baseStart_2115693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115696 : List Nat := [2, 1, 1, 1, 5, 3, 2, 8]
def baseStart_2115696 : Nat := 118140960795 + 2115696 * 2 ^ 59
def prefixEnd_2115696 : Nat := 4983230072969 + 3 ^ 40 * 2115696 * 2
def baseEnd_2115696 : Nat := 40235887659068872717411

theorem tailTrace_2115696 : CollatzResearch.WordTrace tailWord_2115696 prefixEnd_2115696 40235887659068872717411 := by
  unfold tailWord_2115696
  simp only [CollatzResearch.WordTrace]
  refine ⟨38582886271601099477395471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51443848362134799303193961 38582886271601099477395471)
  ·
    refine ⟨57874329407401649216093207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38582886271601099477395471 57874329407401649216093207)
    ·
      refine ⟨86811494111102473824139811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57874329407401649216093207 86811494111102473824139811)
      ·
        refine ⟨130217241166653710736209717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86811494111102473824139811 130217241166653710736209717)
        ·
          refine ⟨12207866359373785381519661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130217241166653710736209717 12207866359373785381519661)
          ·
            refine ⟨4577949884765169518069873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12207866359373785381519661 4577949884765169518069873)
            ·
              refine ⟨3433462413573877138552405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4577949884765169518069873 3433462413573877138552405)
              ·
                refine ⟨40235887659068872717411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3433462413573877138552405 40235887659068872717411)
                ·
                  rfl

theorem cell23_2115696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 8].length) (baseStart_2115696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115696 prefixEnd_2115696 := by exact prefixLift 2115696
  have htrace : WordTrace (prefixWord ++ tailWord_2115696) baseStart_2115696 baseEnd_2115696 := by
    simpa [prefixWord, tailWord_2115696, baseEnd_2115696] using wordTrace_append hprefix tailTrace_2115696
  have hstable : (prefixWord ++ tailWord_2115696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115696).length < 2 ^ (prefixWord ++ tailWord_2115696).sum := by decide
  have hdescent : baseEnd_2115696 < baseStart_2115696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115706 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3]
def baseStart_2115706 : Nat := 118140960795 + 2115706 * 2 ^ 59
def prefixEnd_2115706 : Nat := 4983230072969 + 3 ^ 40 * 2115706 * 2
def baseEnd_2115706 : Nat := 1086374101601404524245051

theorem tailTrace_2115706 : CollatzResearch.WordTrace tailWord_2115706 prefixEnd_2115706 1086374101601404524245051 := by
  unfold tailWord_2115706
  simp only [CollatzResearch.WordTrace]
  refine ⟨19291534318291492665663743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51444091515443980441769981 19291534318291492665663743)
  ·
    refine ⟨28937301477437238998495615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19291534318291492665663743 28937301477437238998495615)
    ·
      refine ⟨43405952216155858497743423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28937301477437238998495615 43405952216155858497743423)
      ·
        refine ⟨65108928324233787746615135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43405952216155858497743423 65108928324233787746615135)
        ·
          refine ⟨97663392486350681619922703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65108928324233787746615135 97663392486350681619922703)
          ·
            refine ⟨146495088729526022429884055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97663392486350681619922703 146495088729526022429884055)
            ·
              refine ⟨219742633094289033644826083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146495088729526022429884055 219742633094289033644826083)
              ·
                refine ⟨329613949641433550467239125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219742633094289033644826083 329613949641433550467239125)
                ·
                  refine ⟨7725326944721098839075917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 329613949641433550467239125 7725326944721098839075917)
                  ·
                    refine ⟨2896997604270412064653469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7725326944721098839075917 2896997604270412064653469)
                    ·
                      refine ⟨1086374101601404524245051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2896997604270412064653469 1086374101601404524245051)
                      ·
                        rfl

theorem cell23_2115706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3].length) (baseStart_2115706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115706 prefixEnd_2115706 := by exact prefixLift 2115706
  have htrace : WordTrace (prefixWord ++ tailWord_2115706) baseStart_2115706 baseEnd_2115706 := by
    simpa [prefixWord, tailWord_2115706, baseEnd_2115706] using wordTrace_append hprefix tailTrace_2115706
  have hstable : (prefixWord ++ tailWord_2115706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115706).length < 2 ^ (prefixWord ++ tailWord_2115706).sum := by decide
  have hdescent : baseEnd_2115706 < baseStart_2115706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115741 : List Nat := [1, 4, 2, 1, 1, 5, 2, 2, 1, 2, 2]
def baseStart_2115741 : Nat := 118140960795 + 2115741 * 2 ^ 59
def prefixEnd_2115741 : Nat := 4983230072969 + 3 ^ 40 * 2115741 * 2
def baseEnd_2115741 : Nat := 1086392073424311887307391

theorem tailTrace_2115741 : CollatzResearch.WordTrace tailWord_2115741 prefixEnd_2115741 1086392073424311887307391 := by
  unfold tailWord_2115741
  simp only [CollatzResearch.WordTrace]
  refine ⟨77167413828039171640179077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51444942552026114426786051 77167413828039171640179077)
  ·
    refine ⟨14468890092757344682533577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77167413828039171640179077 14468890092757344682533577)
    ·
      refine ⟨10851667569568008511900183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14468890092757344682533577 10851667569568008511900183)
      ·
        refine ⟨16277501354352012767850275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10851667569568008511900183 16277501354352012767850275)
        ·
          refine ⟨24416252031528019151775413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16277501354352012767850275 24416252031528019151775413)
          ·
            refine ⟨2289023627955751795478945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24416252031528019151775413 2289023627955751795478945)
            ·
              refine ⟨1716767720966813846609209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2289023627955751795478945 1716767720966813846609209)
              ·
                refine ⟨1287575790725110384956907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1716767720966813846609209 1287575790725110384956907)
                ·
                  refine ⟨1931363686087665577435361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1287575790725110384956907 1931363686087665577435361)
                  ·
                    refine ⟨1448522764565749183076521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1931363686087665577435361 1448522764565749183076521)
                    ·
                      refine ⟨1086392073424311887307391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1448522764565749183076521 1086392073424311887307391)
                      ·
                        rfl

theorem cell23_2115741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_2115741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115741 prefixEnd_2115741 := by exact prefixLift 2115741
  have htrace : WordTrace (prefixWord ++ tailWord_2115741) baseStart_2115741 baseEnd_2115741 := by
    simpa [prefixWord, tailWord_2115741, baseEnd_2115741] using wordTrace_append hprefix tailTrace_2115741
  have hstable : (prefixWord ++ tailWord_2115741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115741).length < 2 ^ (prefixWord ++ tailWord_2115741).sum := by decide
  have hdescent : baseEnd_2115741 < baseStart_2115741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115757 : List Nat := [1, 5, 2, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_2115757 : Nat := 118140960795 + 2115757 * 2 ^ 59
def prefixEnd_2115757 : Nat := 4983230072969 + 3 ^ 40 * 2115757 * 2
def baseEnd_2115757 : Nat := 1086400289114783824707317

theorem tailTrace_2115757 : CollatzResearch.WordTrace tailWord_2115757 prefixEnd_2115757 1086400289114783824707317 := by
  unfold tailWord_2115757
  simp only [CollatzResearch.WordTrace]
  refine ⟨77167997395981206372761525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51445331597320804248507683 77167997395981206372761525)
  ·
    refine ⟨7234499755873238097446393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77167997395981206372761525 7234499755873238097446393)
    ·
      refine ⟨5425874816904928573084795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7234499755873238097446393 5425874816904928573084795)
      ·
        refine ⟨8138812225357392859627193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5425874816904928573084795 8138812225357392859627193)
        ·
          refine ⟨6104109169018044644720395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8138812225357392859627193 6104109169018044644720395)
          ·
            refine ⟨9156163753527066967080593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6104109169018044644720395 9156163753527066967080593)
            ·
              refine ⟨6867122815145300225310445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9156163753527066967080593 6867122815145300225310445)
              ·
                refine ⟨2575171055679487584491417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6867122815145300225310445 2575171055679487584491417)
                ·
                  refine ⟨1931378291759615688368563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2575171055679487584491417 1931378291759615688368563)
                  ·
                    refine ⟨2897067437639423532552845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1931378291759615688368563 2897067437639423532552845)
                    ·
                      refine ⟨1086400289114783824707317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2897067437639423532552845 1086400289114783824707317)
                      ·
                        rfl

theorem cell23_2115757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_2115757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115757 prefixEnd_2115757 := by exact prefixLift 2115757
  have htrace : WordTrace (prefixWord ++ tailWord_2115757) baseStart_2115757 baseEnd_2115757 := by
    simpa [prefixWord, tailWord_2115757, baseEnd_2115757] using wordTrace_append hprefix tailTrace_2115757
  have hstable : (prefixWord ++ tailWord_2115757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115757).length < 2 ^ (prefixWord ++ tailWord_2115757).sum := by decide
  have hdescent : baseEnd_2115757 < baseStart_2115757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115764 : List Nat := [2, 5, 3, 1, 1, 1, 3, 7]
def baseStart_2115764 : Nat := 118140960795 + 2115764 * 2 ^ 59
def prefixEnd_2115764 : Nat := 4983230072969 + 3 ^ 40 * 2115764 * 2
def baseEnd_2115764 : Nat := 40237180869606122122955

theorem tailTrace_2115764 : CollatzResearch.WordTrace tailWord_2115764 prefixEnd_2115764 40237180869606122122955 := by
  unfold tailWord_2115764
  simp only [CollatzResearch.WordTrace]
  refine ⟨38584126353477923284133173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51445501804637231045510897 38584126353477923284133173)
  ·
    refine ⟨3617261845638555307887485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38584126353477923284133173 3617261845638555307887485)
    ·
      refine ⟨1356473192114458240457807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3617261845638555307887485 1356473192114458240457807)
      ·
        refine ⟨2034709788171687360686711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1356473192114458240457807 2034709788171687360686711)
        ·
          refine ⟨3052064682257531041030067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2034709788171687360686711 3052064682257531041030067)
          ·
            refine ⟨4578097023386296561545101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3052064682257531041030067 4578097023386296561545101)
            ·
              refine ⟨1716786383769861210579413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4578097023386296561545101 1716786383769861210579413)
              ·
                refine ⟨40237180869606122122955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1716786383769861210579413 40237180869606122122955)
                ·
                  rfl

theorem cell23_2115764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 7].length) (baseStart_2115764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115764 prefixEnd_2115764 := by exact prefixLift 2115764
  have htrace : WordTrace (prefixWord ++ tailWord_2115764) baseStart_2115764 baseEnd_2115764 := by
    simpa [prefixWord, tailWord_2115764, baseEnd_2115764] using wordTrace_append hprefix tailTrace_2115764
  have hstable : (prefixWord ++ tailWord_2115764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115764).length < 2 ^ (prefixWord ++ tailWord_2115764).sum := by decide
  have hdescent : baseEnd_2115764 < baseStart_2115764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115786 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 9]
def baseStart_2115786 : Nat := 118140960795 + 2115786 * 2 ^ 59
def prefixEnd_2115786 : Nat := 4983230072969 + 3 ^ 40 * 2115786 * 2
def baseEnd_2115786 : Nat := 120712797783751579027187

theorem tailTrace_2115786 : CollatzResearch.WordTrace tailWord_2115786 prefixEnd_2115786 120712797783751579027187 := by
  unfold tailWord_2115786
  simp only [CollatzResearch.WordTrace]
  refine ⟨19292263778219036081391803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51446036741917429550378141 19292263778219036081391803)
  ·
    refine ⟨28938395667328554122087705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19292263778219036081391803 28938395667328554122087705)
    ·
      refine ⟨21703796750496415591565779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28938395667328554122087705 21703796750496415591565779)
      ·
        refine ⟨32555695125744623387348669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21703796750496415591565779 32555695125744623387348669)
        ·
          refine ⟨12208385672154233770255751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32555695125744623387348669 12208385672154233770255751)
          ·
            refine ⟨18312578508231350655383627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12208385672154233770255751 18312578508231350655383627)
            ·
              refine ⟨27468867762347025983075441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18312578508231350655383627 27468867762347025983075441)
              ·
                refine ⟨20601650821760269487306581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27468867762347025983075441 20601650821760269487306581)
                ·
                  refine ⟨120712797783751579027187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20601650821760269487306581 120712797783751579027187)
                  ·
                    rfl

theorem cell23_2115786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 9].length) (baseStart_2115786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115786 prefixEnd_2115786 := by exact prefixLift 2115786
  have htrace : WordTrace (prefixWord ++ tailWord_2115786) baseStart_2115786 baseEnd_2115786 := by
    simpa [prefixWord, tailWord_2115786, baseEnd_2115786] using wordTrace_append hprefix tailTrace_2115786
  have hstable : (prefixWord ++ tailWord_2115786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115786).length < 2 ^ (prefixWord ++ tailWord_2115786).sum := by decide
  have hdescent : baseEnd_2115786 < baseStart_2115786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115873 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 3, 4, 3]
def baseStart_2115873 : Nat := 118140960795 + 2115873 * 2 ^ 59
def prefixEnd_2115873 : Nat := 4983230072969 + 3 ^ 40 * 2115873 * 2
def baseEnd_2115873 : Nat := 1086459852870705370856783

theorem tailTrace_2115873 : CollatzResearch.WordTrace tailWord_2115873 prefixEnd_2115873 1086459852870705370856783 := by
  unfold tailWord_2115873
  simp only [CollatzResearch.WordTrace]
  refine ⟨77172228263560958183984273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51448152175707305455989515 77172228263560958183984273)
  ·
    refine ⟨57879171197670718637988205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77172228263560958183984273 57879171197670718637988205)
    ·
      refine ⟨21704689199126519489245577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57879171197670718637988205 21704689199126519489245577)
      ·
        refine ⟨16278516899344889616934183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21704689199126519489245577 16278516899344889616934183)
        ·
          refine ⟨24417775349017334425401275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16278516899344889616934183 24417775349017334425401275)
          ·
            refine ⟨36626663023526001638101913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24417775349017334425401275 36626663023526001638101913)
            ·
              refine ⟨27469997267644501228576435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36626663023526001638101913 27469997267644501228576435)
              ·
                refine ⟨41204995901466751842864653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27469997267644501228576435 41204995901466751842864653)
                ·
                  refine ⟨15451873463050031941074245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41204995901466751842864653 15451873463050031941074245)
                  ·
                    refine ⟨2897226274321880988951421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15451873463050031941074245 2897226274321880988951421)
                    ·
                      refine ⟨1086459852870705370856783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2897226274321880988951421 1086459852870705370856783)
                      ·
                        rfl

theorem cell23_2115873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_2115873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115873 prefixEnd_2115873 := by exact prefixLift 2115873
  have htrace : WordTrace (prefixWord ++ tailWord_2115873) baseStart_2115873 baseEnd_2115873 := by
    simpa [prefixWord, tailWord_2115873, baseEnd_2115873] using wordTrace_append hprefix tailTrace_2115873
  have hstable : (prefixWord ++ tailWord_2115873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115873).length < 2 ^ (prefixWord ++ tailWord_2115873).sum := by decide
  have hdescent : baseEnd_2115873 < baseStart_2115873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115930 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2]
def baseStart_2115930 : Nat := 118140960795 + 2115930 * 2 ^ 59
def prefixEnd_2115930 : Nat := 4983230072969 + 3 ^ 40 * 2115930 * 2
def baseEnd_2115930 : Nat := 1086489121268011647844021

theorem tailTrace_2115930 : CollatzResearch.WordTrace tailWord_2115930 prefixEnd_2115930 1086489121268011647844021 := by
  unfold tailWord_2115930
  simp only [CollatzResearch.WordTrace]
  refine ⟨19293576806088614229702311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51449538149569637945872829 19293576806088614229702311)
  ·
    refine ⟨28940365209132921344553467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19293576806088614229702311 28940365209132921344553467)
    ·
      refine ⟨43410547813699382016830201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28940365209132921344553467 43410547813699382016830201)
      ·
        refine ⟨32557910860274536512622651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43410547813699382016830201 32557910860274536512622651)
        ·
          refine ⟨48836866290411804768933977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32557910860274536512622651 48836866290411804768933977)
          ·
            refine ⟨36627649717808853576700483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48836866290411804768933977 36627649717808853576700483)
            ·
              refine ⟨54941474576713280365050725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36627649717808853576700483 54941474576713280365050725)
              ·
                refine ⟨10301526483133740068447011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54941474576713280365050725 10301526483133740068447011)
                ·
                  refine ⟨15452289724700610102670517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10301526483133740068447011 15452289724700610102670517)
                  ·
                    refine ⟨1448652161690682197125361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15452289724700610102670517 1448652161690682197125361)
                    ·
                      refine ⟨1086489121268011647844021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1448652161690682197125361 1086489121268011647844021)
                      ·
                        rfl

theorem cell23_2115930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2].length) (baseStart_2115930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115930 prefixEnd_2115930 := by exact prefixLift 2115930
  have htrace : WordTrace (prefixWord ++ tailWord_2115930) baseStart_2115930 baseEnd_2115930 := by
    simpa [prefixWord, tailWord_2115930, baseEnd_2115930] using wordTrace_append hprefix tailTrace_2115930
  have hstable : (prefixWord ++ tailWord_2115930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115930).length < 2 ^ (prefixWord ++ tailWord_2115930).sum := by decide
  have hdescent : baseEnd_2115930 < baseStart_2115930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115940 : List Nat := [2, 3, 1, 1, 3, 1, 2, 4, 1, 5]
def baseStart_2115940 : Nat := 118140960795 + 2115940 * 2 ^ 59
def prefixEnd_2115940 : Nat := 4983230072969 + 3 ^ 40 * 2115940 * 2
def baseEnd_2115940 : Nat := 362164752024852202906325

theorem tailTrace_2115940 : CollatzResearch.WordTrace tailWord_2115940 prefixEnd_2115940 362164752024852202906325 := by
  unfold tailWord_2115940
  simp only [CollatzResearch.WordTrace]
  refine ⟨38587335977159114313336637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51449781302878819084448849 38587335977159114313336637)
  ·
    refine ⟨14470250991434667867501239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38587335977159114313336637 14470250991434667867501239)
    ·
      refine ⟨21705376487152001801251859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14470250991434667867501239 21705376487152001801251859)
      ·
        refine ⟨32558064730728002701877789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21705376487152001801251859 32558064730728002701877789)
        ·
          refine ⟨12209274274023001013204171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32558064730728002701877789 12209274274023001013204171)
          ·
            refine ⟨18313911411034501519806257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12209274274023001013204171 18313911411034501519806257)
            ·
              refine ⟨13735433558275876139854693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18313911411034501519806257 13735433558275876139854693)
              ·
                refine ⟨2575393792176726776222755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13735433558275876139854693 2575393792176726776222755)
                ·
                  refine ⟨3863090688265090164334133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2575393792176726776222755 3863090688265090164334133)
                  ·
                    refine ⟨362164752024852202906325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3863090688265090164334133 362164752024852202906325)
                    ·
                      rfl

theorem cell23_2115940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_2115940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115940 prefixEnd_2115940 := by exact prefixLift 2115940
  have htrace : WordTrace (prefixWord ++ tailWord_2115940) baseStart_2115940 baseEnd_2115940 := by
    simpa [prefixWord, tailWord_2115940, baseEnd_2115940] using wordTrace_append hprefix tailTrace_2115940
  have hstable : (prefixWord ++ tailWord_2115940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115940).length < 2 ^ (prefixWord ++ tailWord_2115940).sum := by decide
  have hdescent : baseEnd_2115940 < baseStart_2115940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115954 : List Nat := [3, 2, 1, 2, 1, 3, 1, 5, 1, 1, 3]
def baseStart_2115954 : Nat := 118140960795 + 2115954 * 2 ^ 59
def prefixEnd_2115954 : Nat := 4983230072969 + 3 ^ 40 * 2115954 * 2
def baseEnd_2115954 : Nat := 1086501444803719553943911

theorem tailTrace_2115954 : CollatzResearch.WordTrace tailWord_2115954 prefixEnd_2115954 1086501444803719553943911 := by
  unfold tailWord_2115954
  simp only [CollatzResearch.WordTrace]
  refine ⟨19293795644066877254420729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51450121717511672678455277 19293795644066877254420729)
  ·
    refine ⟨14470346733050157940815547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19293795644066877254420729 14470346733050157940815547)
    ·
      refine ⟨21705520099575236911223321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14470346733050157940815547 21705520099575236911223321)
      ·
        refine ⟨16279140074681427683417491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21705520099575236911223321 16279140074681427683417491)
        ·
          refine ⟨24418710112022141525126237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16279140074681427683417491 24418710112022141525126237)
          ·
            refine ⟨9157016292008303071922339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24418710112022141525126237 9157016292008303071922339)
            ·
              refine ⟨13735524438012454607883509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9157016292008303071922339 13735524438012454607883509)
              ·
                refine ⟨1287705416063667619489079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13735524438012454607883509 1287705416063667619489079)
                ·
                  refine ⟨1931558124095501429233619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1287705416063667619489079 1931558124095501429233619)
                  ·
                    refine ⟨2897337186143252143850429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1931558124095501429233619 2897337186143252143850429)
                    ·
                      refine ⟨1086501444803719553943911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2897337186143252143850429 1086501444803719553943911)
                      ·
                        rfl

theorem cell23_2115954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_2115954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115954 prefixEnd_2115954 := by exact prefixLift 2115954
  have htrace : WordTrace (prefixWord ++ tailWord_2115954) baseStart_2115954 baseEnd_2115954 := by
    simpa [prefixWord, tailWord_2115954, baseEnd_2115954] using wordTrace_append hprefix tailTrace_2115954
  have hstable : (prefixWord ++ tailWord_2115954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115954).length < 2 ^ (prefixWord ++ tailWord_2115954).sum := by decide
  have hdescent : baseEnd_2115954 < baseStart_2115954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115957 : List Nat := [1, 3, 4, 1, 2, 2, 1, 3, 1, 5]
def baseStart_2115957 : Nat := 118140960795 + 2115957 * 2 ^ 59
def prefixEnd_2115957 : Nat := 4983230072969 + 3 ^ 40 * 2115957 * 2
def baseEnd_2115957 : Nat := 362167661748561014068799

theorem tailTrace_2115957 : CollatzResearch.WordTrace tailWord_2115957 prefixEnd_2115957 362167661748561014068799 := by
  unfold tailWord_2115957
  simp only [CollatzResearch.WordTrace]
  refine ⟨77175291995256640530042125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51450194663504427020028083 77175291995256640530042125)
  ·
    refine ⟨28940734498221240198765797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77175291995256640530042125 28940734498221240198765797)
    ·
      refine ⟨5426387718416482537268587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28940734498221240198765797 5426387718416482537268587)
      ·
        refine ⟨8139581577624723805902881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5426387718416482537268587 8139581577624723805902881)
        ·
          refine ⟨6104686183218542854427161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8139581577624723805902881 6104686183218542854427161)
          ·
            refine ⟨4578514637413907140820371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6104686183218542854427161 4578514637413907140820371)
            ·
              refine ⟨6867771956120860711230557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4578514637413907140820371 6867771956120860711230557)
              ·
                refine ⟨2575414483545322766711459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6867771956120860711230557 2575414483545322766711459)
                ·
                  refine ⟨3863121725317984150067189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2575414483545322766711459 3863121725317984150067189)
                  ·
                    refine ⟨362167661748561014068799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3863121725317984150067189 362167661748561014068799)
                    ·
                      rfl

theorem cell23_2115957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_2115957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115957 prefixEnd_2115957 := by exact prefixLift 2115957
  have htrace : WordTrace (prefixWord ++ tailWord_2115957) baseStart_2115957 baseEnd_2115957 := by
    simpa [prefixWord, tailWord_2115957, baseEnd_2115957] using wordTrace_append hprefix tailTrace_2115957
  have hstable : (prefixWord ++ tailWord_2115957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115957).length < 2 ^ (prefixWord ++ tailWord_2115957).sum := by decide
  have hdescent : baseEnd_2115957 < baseStart_2115957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115973 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 1, 1, 6]
def baseStart_2115973 : Nat := 118140960795 + 2115973 * 2 ^ 59
def prefixEnd_2115973 : Nat := 4983230072969 + 3 ^ 40 * 2115973 * 2
def baseEnd_2115973 : Nat := 1086511200936154979606323

theorem tailTrace_2115973 : CollatzResearch.WordTrace tailWord_2115973 prefixEnd_2115973 1086511200936154979606323 := by
  unfold tailWord_2115973
  simp only [CollatzResearch.WordTrace]
  refine ⟨77175875563198675262624573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51450583708799116841749715 77175875563198675262624573)
  ·
    refine ⟨28940953336199503223484215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77175875563198675262624573 28940953336199503223484215)
    ·
      refine ⟨43411430004299254835226323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28940953336199503223484215 43411430004299254835226323)
      ·
        refine ⟨65117145006448882252839485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43411430004299254835226323 65117145006448882252839485)
        ·
          refine ⟨24418929377418330844814807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65117145006448882252839485 24418929377418330844814807)
          ·
            refine ⟨36628394066127496267222211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24418929377418330844814807 36628394066127496267222211)
            ·
              refine ⟨54942591099191244400833317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36628394066127496267222211 54942591099191244400833317)
              ·
                refine ⟨10301735831098358325156247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54942591099191244400833317 10301735831098358325156247)
                ·
                  refine ⟨15452603746647537487734371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10301735831098358325156247 15452603746647537487734371)
                  ·
                    refine ⟨23178905619971306231601557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15452603746647537487734371 23178905619971306231601557)
                    ·
                      refine ⟨1086511200936154979606323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23178905619971306231601557 1086511200936154979606323)
                      ·
                        rfl

theorem cell23_2115973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_2115973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115973 prefixEnd_2115973 := by exact prefixLift 2115973
  have htrace : WordTrace (prefixWord ++ tailWord_2115973) baseStart_2115973 baseEnd_2115973 := by
    simpa [prefixWord, tailWord_2115973, baseEnd_2115973] using wordTrace_append hprefix tailTrace_2115973
  have hstable : (prefixWord ++ tailWord_2115973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115973).length < 2 ^ (prefixWord ++ tailWord_2115973).sum := by decide
  have hdescent : baseEnd_2115973 < baseStart_2115973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115980 : List Nat := [2, 2, 1, 2, 1, 5, 1, 2, 1, 1, 5]
def baseStart_2115980 : Nat := 118140960795 + 2115980 * 2 ^ 59
def prefixEnd_2115980 : Nat := 4983230072969 + 3 ^ 40 * 2115980 * 2
def baseEnd_2115980 : Nat := 1086514795300736452218791

theorem tailTrace_2115980 : CollatzResearch.WordTrace tailWord_2115980 prefixEnd_2115980 1086514795300736452218791 := by
  unfold tailWord_2115980
  simp only [CollatzResearch.WordTrace]
  refine ⟨38588065437086657729064697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51450753916115543638752929 38588065437086657729064697)
  ·
    refine ⟨28941049077814993296798523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38588065437086657729064697 28941049077814993296798523)
    ·
      refine ⟨43411573616722489945197785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28941049077814993296798523 43411573616722489945197785)
      ·
        refine ⟨32558680212541867458898339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43411573616722489945197785 32558680212541867458898339)
        ·
          refine ⟨48838020318812801188347509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32558680212541867458898339 48838020318812801188347509)
          ·
            refine ⟨4578564404888700111407579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48838020318812801188347509 4578564404888700111407579)
            ·
              refine ⟨6867846607333050167111369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4578564404888700111407579 6867846607333050167111369)
              ·
                refine ⟨5150884955499787625333527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6867846607333050167111369 5150884955499787625333527)
                ·
                  refine ⟨7726327433249681438000291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5150884955499787625333527 7726327433249681438000291)
                  ·
                    refine ⟨11589491149874522157000437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7726327433249681438000291 11589491149874522157000437)
                    ·
                      refine ⟨1086514795300736452218791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11589491149874522157000437 1086514795300736452218791)
                      ·
                        rfl

theorem cell23_2115980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_2115980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115980 prefixEnd_2115980 := by exact prefixLift 2115980
  have htrace : WordTrace (prefixWord ++ tailWord_2115980) baseStart_2115980 baseEnd_2115980 := by
    simpa [prefixWord, tailWord_2115980, baseEnd_2115980] using wordTrace_append hprefix tailTrace_2115980
  have hstable : (prefixWord ++ tailWord_2115980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115980).length < 2 ^ (prefixWord ++ tailWord_2115980).sum := by decide
  have hdescent : baseEnd_2115980 < baseStart_2115980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115994 : List Nat := [3, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2]
def baseStart_2115994 : Nat := 118140960795 + 2115994 * 2 ^ 59
def prefixEnd_2115994 : Nat := 4983230072969 + 3 ^ 40 * 2115994 * 2
def baseEnd_2115994 : Nat := 1086521984029899397443727

theorem tailTrace_2115994 : CollatzResearch.WordTrace tailWord_2115994 prefixEnd_2115994 1086521984029899397443727 := by
  unfold tailWord_2115994
  simp only [CollatzResearch.WordTrace]
  refine ⟨19294160374030648962284759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51451094330748397232759357 19294160374030648962284759)
  ·
    refine ⟨28941240561045973443427139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19294160374030648962284759 28941240561045973443427139)
    ·
      refine ⟨43411860841568960165140709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28941240561045973443427139 43411860841568960165140709)
      ·
        refine ⟨8139723907794180030963883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43411860841568960165140709 8139723907794180030963883)
        ·
          refine ⟨12209585861691270046445825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8139723907794180030963883 12209585861691270046445825)
          ·
            refine ⟨9157189396268452534834369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12209585861691270046445825 9157189396268452534834369)
            ·
              refine ⟨6867892047201339401125777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9157189396268452534834369 6867892047201339401125777)
              ·
                refine ⟨5150919035401004550844333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6867892047201339401125777 5150919035401004550844333)
                ·
                  refine ⟨1931594638275376706566625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5150919035401004550844333 1931594638275376706566625)
                  ·
                    refine ⟨1448695978706532529924969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1931594638275376706566625 1448695978706532529924969)
                    ·
                      refine ⟨1086521984029899397443727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1448695978706532529924969 1086521984029899397443727)
                      ·
                        rfl

theorem cell23_2115994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_2115994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2115994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2115994 prefixEnd_2115994 := by exact prefixLift 2115994
  have htrace : WordTrace (prefixWord ++ tailWord_2115994) baseStart_2115994 baseEnd_2115994 := by
    simpa [prefixWord, tailWord_2115994, baseEnd_2115994] using wordTrace_append hprefix tailTrace_2115994
  have hstable : (prefixWord ++ tailWord_2115994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115994).length < 2 ^ (prefixWord ++ tailWord_2115994).sum := by decide
  have hdescent : baseEnd_2115994 < baseStart_2115994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116000 : List Nat := [2, 1, 1, 4, 1, 3, 4, 7]
def baseStart_2116000 : Nat := 118140960795 + 2116000 * 2 ^ 59
def prefixEnd_2116000 : Nat := 4983230072969 + 3 ^ 40 * 2116000 * 2
def baseEnd_2116000 : Nat := 40241669070882458295137

theorem tailTrace_2116000 : CollatzResearch.WordTrace tailWord_2116000 prefixEnd_2116000 40241669070882458295137 := by
  unfold tailWord_2116000
  simp only [CollatzResearch.WordTrace]
  refine ⟨38588430167050429436928727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51451240222733905915904969 38588430167050429436928727)
  ·
    refine ⟨57882645250575644155393091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38588430167050429436928727 57882645250575644155393091)
    ·
      refine ⟨86823967875863466233089637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57882645250575644155393091 86823967875863466233089637)
      ·
        refine ⟨16279493976724399918704307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86823967875863466233089637 16279493976724399918704307)
        ·
          refine ⟨24419240965086599878056461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16279493976724399918704307 24419240965086599878056461)
          ·
            refine ⟨9157215361907474954271173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24419240965086599878056461 9157215361907474954271173)
            ·
              refine ⟨1716977880357651553925845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9157215361907474954271173 1716977880357651553925845)
              ·
                refine ⟨40241669070882458295137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1716977880357651553925845 40241669070882458295137)
                ·
                  rfl

theorem cell23_2116000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 7].length) (baseStart_2116000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116000 prefixEnd_2116000 := by exact prefixLift 2116000
  have htrace : WordTrace (prefixWord ++ tailWord_2116000) baseStart_2116000 baseEnd_2116000 := by
    simpa [prefixWord, tailWord_2116000, baseEnd_2116000] using wordTrace_append hprefix tailTrace_2116000
  have hstable : (prefixWord ++ tailWord_2116000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116000).length < 2 ^ (prefixWord ++ tailWord_2116000).sum := by decide
  have hdescent : baseEnd_2116000 < baseStart_2116000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116043 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 1, 8]
def baseStart_2116043 : Nat := 118140960795 + 2116043 * 2 ^ 59
def prefixEnd_2116043 : Nat := 4983230072969 + 3 ^ 40 * 2116043 * 2
def baseEnd_2116043 : Nat := 362182381527323235243667

theorem tailTrace_2116043 : CollatzResearch.WordTrace tailWord_2116043 prefixEnd_2116043 362182381527323235243667 := by
  unfold tailWord_2116043
  simp only [CollatzResearch.WordTrace]
  refine ⟨77178428672945077217672783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51452285781963384811781855 77178428672945077217672783)
  ·
    refine ⟨115767643009417615826509175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77178428672945077217672783 115767643009417615826509175)
    ·
      refine ⟨173651464514126423739763763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115767643009417615826509175 173651464514126423739763763)
      ·
        refine ⟨260477196771189635609645645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173651464514126423739763763 260477196771189635609645645)
        ·
          refine ⟨97678948789196113353617117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 260477196771189635609645645 97678948789196113353617117)
          ·
            refine ⟨36629605795948542507606419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97678948789196113353617117 36629605795948542507606419)
            ·
              refine ⟨54944408693922813761409629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36629605795948542507606419 54944408693922813761409629)
              ·
                refine ⟨20604153260221055160528611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54944408693922813761409629 20604153260221055160528611)
                ·
                  refine ⟨30906229890331582740792917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20604153260221055160528611 30906229890331582740792917)
                  ·
                    refine ⟨362182381527323235243667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30906229890331582740792917 362182381527323235243667)
                    ·
                      rfl

theorem cell23_2116043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 8].length) (baseStart_2116043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116043 prefixEnd_2116043 := by exact prefixLift 2116043
  have htrace : WordTrace (prefixWord ++ tailWord_2116043) baseStart_2116043 baseEnd_2116043 := by
    simpa [prefixWord, tailWord_2116043, baseEnd_2116043] using wordTrace_append hprefix tailTrace_2116043
  have hstable : (prefixWord ++ tailWord_2116043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116043).length < 2 ^ (prefixWord ++ tailWord_2116043).sum := by decide
  have hdescent : baseEnd_2116043 < baseStart_2116043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116071 : List Nat := [1, 1, 5, 2, 1, 1, 5, 1, 1, 3, 2]
def baseStart_2116071 : Nat := 118140960795 + 2116071 * 2 ^ 59
def prefixEnd_2116071 : Nat := 4983230072969 + 3 ^ 40 * 2116071 * 2
def baseEnd_2116071 : Nat := 1086561522040295596180873

theorem tailTrace_2116071 : CollatzResearch.WordTrace tailWord_2116071 prefixEnd_2116071 1086561522040295596180873 := by
  unfold tailWord_2116071
  simp only [CollatzResearch.WordTrace]
  refine ⟨77179449916843637999692067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51452966611229091999794711 77179449916843637999692067)
  ·
    refine ⟨115769174875265456999538101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77179449916843637999692067 115769174875265456999538101)
    ·
      refine ⟨10853360144556136593706697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115769174875265456999538101 10853360144556136593706697)
      ·
        refine ⟨8140020108417102445280023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10853360144556136593706697 8140020108417102445280023)
        ·
          refine ⟨12210030162625653667920035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8140020108417102445280023 12210030162625653667920035)
          ·
            refine ⟨18315045243938480501880053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12210030162625653667920035 18315045243938480501880053)
            ·
              refine ⟨1717035491619232547051255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18315045243938480501880053 1717035491619232547051255)
              ·
                refine ⟨2575553237428848820576883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1717035491619232547051255 2575553237428848820576883)
                ·
                  refine ⟨3863329856143273230865325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2575553237428848820576883 3863329856143273230865325)
                  ·
                    refine ⟨1448748696053727461574497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3863329856143273230865325 1448748696053727461574497)
                    ·
                      refine ⟨1086561522040295596180873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1448748696053727461574497 1086561522040295596180873)
                      ·
                        rfl

theorem cell23_2116071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_2116071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116071 prefixEnd_2116071 := by exact prefixLift 2116071
  have htrace : WordTrace (prefixWord ++ tailWord_2116071) baseStart_2116071 baseEnd_2116071 := by
    simpa [prefixWord, tailWord_2116071, baseEnd_2116071] using wordTrace_append hprefix tailTrace_2116071
  have hstable : (prefixWord ++ tailWord_2116071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116071).length < 2 ^ (prefixWord ++ tailWord_2116071).sum := by decide
  have hdescent : baseEnd_2116071 < baseStart_2116071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116073 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 11]
def baseStart_2116073 : Nat := 118140960795 + 2116073 * 2 ^ 59
def prefixEnd_2116073 : Nat := 4983230072969 + 3 ^ 40 * 2116073 * 2
def baseEnd_2116073 : Nat := 120729172111289398706207

theorem tailTrace_2116073 : CollatzResearch.WordTrace tailWord_2116073 prefixEnd_2116073 120729172111289398706207 := by
  unfold tailWord_2116073
  simp only [CollatzResearch.WordTrace]
  refine ⟨77179522862836392341264873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51453015241890928227509915 77179522862836392341264873)
  ·
    refine ⟨57884642147127294255948655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77179522862836392341264873 57884642147127294255948655)
    ·
      refine ⟨86826963220690941383922983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57884642147127294255948655 86826963220690941383922983)
      ·
        refine ⟨130240444831036412075884475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86826963220690941383922983 130240444831036412075884475)
        ·
          refine ⟨195360667246554618113826713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130240444831036412075884475 195360667246554618113826713)
          ·
            refine ⟨146520500434915963585370035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195360667246554618113826713 146520500434915963585370035)
            ·
              refine ⟨219780750652373945378055053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146520500434915963585370035 219780750652373945378055053)
              ·
                refine ⟨82417781494640229516770645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 219780750652373945378055053 82417781494640229516770645)
                ·
                  refine ⟨120729172111289398706207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 82417781494640229516770645 120729172111289398706207)
                  ·
                    rfl

theorem cell23_2116073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 11].length) (baseStart_2116073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116073 prefixEnd_2116073 := by exact prefixLift 2116073
  have htrace : WordTrace (prefixWord ++ tailWord_2116073) baseStart_2116073 baseEnd_2116073 := by
    simpa [prefixWord, tailWord_2116073, baseEnd_2116073] using wordTrace_append hprefix tailTrace_2116073
  have hstable : (prefixWord ++ tailWord_2116073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116073).length < 2 ^ (prefixWord ++ tailWord_2116073).sum := by decide
  have hdescent : baseEnd_2116073 < baseStart_2116073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116080 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 4]
def baseStart_2116080 : Nat := 118140960795 + 2116080 * 2 ^ 59
def prefixEnd_2116080 : Nat := 4983230072969 + 3 ^ 40 * 2116080 * 2
def baseEnd_2116080 : Nat := 1086566143366186060968331

theorem tailTrace_2116080 : CollatzResearch.WordTrace tailWord_2116080 prefixEnd_2116080 1086566143366186060968331 := by
  unfold tailWord_2116080
  simp only [CollatzResearch.WordTrace]
  refine ⟨38589889086905516268384847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51453185449207355024513129 38589889086905516268384847)
  ·
    refine ⟨57884833630358274402577271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38589889086905516268384847 57884833630358274402577271)
    ·
      refine ⟨86827250445537411603865907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57884833630358274402577271 86827250445537411603865907)
      ·
        refine ⟨130240875668306117405798861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86827250445537411603865907 130240875668306117405798861)
        ·
          refine ⟨48840328375614794027174573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130240875668306117405798861 48840328375614794027174573)
          ·
            refine ⟨18315123140855547760190465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48840328375614794027174573 18315123140855547760190465)
            ·
              refine ⟨13736342355641660820142849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18315123140855547760190465 13736342355641660820142849)
              ·
                refine ⟨10302256766731245615107137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13736342355641660820142849 10302256766731245615107137)
                ·
                  refine ⟨7726692575048434211330353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10302256766731245615107137 7726692575048434211330353)
                  ·
                    refine ⟨5795019431286325658497765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7726692575048434211330353 5795019431286325658497765)
                    ·
                      refine ⟨1086566143366186060968331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5795019431286325658497765 1086566143366186060968331)
                      ·
                        rfl

theorem cell23_2116080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 4].length) (baseStart_2116080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116080 prefixEnd_2116080 := by exact prefixLift 2116080
  have htrace : WordTrace (prefixWord ++ tailWord_2116080) baseStart_2116080 baseEnd_2116080 := by
    simpa [prefixWord, tailWord_2116080, baseEnd_2116080] using wordTrace_append hprefix tailTrace_2116080
  have hstable : (prefixWord ++ tailWord_2116080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116080).length < 2 ^ (prefixWord ++ tailWord_2116080).sum := by decide
  have hdescent : baseEnd_2116080 < baseStart_2116080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116097 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_2116097 : Nat := 118140960795 + 2116097 * 2 ^ 59
def prefixEnd_2116097 : Nat := 4983230072969 + 3 ^ 40 * 2116097 * 2
def baseEnd_2116097 : Nat := 1086574872537312494455753

theorem tailTrace_2116097 : CollatzResearch.WordTrace tailWord_2116097 prefixEnd_2116097 1086574872537312494455753 := by
  unfold tailWord_2116097
  simp only [CollatzResearch.WordTrace]
  refine ⟨77180398214749444440138545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51453598809832962960092363 77180398214749444440138545)
  ·
    refine ⟨57885298661062083330103909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77180398214749444440138545 57885298661062083330103909)
    ·
      refine ⟨10853493498949140624394483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57885298661062083330103909 10853493498949140624394483)
      ·
        refine ⟨16280240248423710936591725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10853493498949140624394483 16280240248423710936591725)
        ·
          refine ⟨6105090093158891601221897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16280240248423710936591725 6105090093158891601221897)
          ·
            refine ⟨4578817569869168700916423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6105090093158891601221897 4578817569869168700916423)
            ·
              refine ⟨6868226354803753051374635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4578817569869168700916423 6868226354803753051374635)
              ·
                refine ⟨10302339532205629577061953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6868226354803753051374635 10302339532205629577061953)
                ·
                  refine ⟨7726754649154222182796465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10302339532205629577061953 7726754649154222182796465)
                  ·
                    refine ⟨5795065986865666637097349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7726754649154222182796465 5795065986865666637097349)
                    ·
                      refine ⟨1086574872537312494455753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5795065986865666637097349 1086574872537312494455753)
                      ·
                        rfl

theorem cell23_2116097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_2116097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116097 prefixEnd_2116097 := by exact prefixLift 2116097
  have htrace : WordTrace (prefixWord ++ tailWord_2116097) baseStart_2116097 baseEnd_2116097 := by
    simpa [prefixWord, tailWord_2116097, baseEnd_2116097] using wordTrace_append hprefix tailTrace_2116097
  have hstable : (prefixWord ++ tailWord_2116097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116097).length < 2 ^ (prefixWord ++ tailWord_2116097).sum := by decide
  have hdescent : baseEnd_2116097 < baseStart_2116097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116124 : List Nat := [2, 2, 3, 1, 2, 3, 2, 3, 5]
def baseStart_2116124 : Nat := 118140960795 + 2116124 * 2 ^ 59
def prefixEnd_2116124 : Nat := 4983230072969 + 3 ^ 40 * 2116124 * 2
def baseEnd_2116124 : Nat := 120732081834998209868681

theorem tailTrace_2116124 : CollatzResearch.WordTrace tailWord_2116124 prefixEnd_2116124 120732081834998209868681 := by
  unfold tailWord_2116124
  simp only [CollatzResearch.WordTrace]
  refine ⟨38590691492825814025685713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51454255323767752034247617 38590691492825814025685713)
  ·
    refine ⟨28943018619619360519264285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38590691492825814025685713 28943018619619360519264285)
    ·
      refine ⟨10853631982357260194724107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28943018619619360519264285 10853631982357260194724107)
      ·
        refine ⟨16280447973535890292086161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10853631982357260194724107 16280447973535890292086161)
        ·
          refine ⟨12210335980151917719064621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16280447973535890292086161 12210335980151917719064621)
          ·
            refine ⟨4578875992556969144649233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12210335980151917719064621 4578875992556969144649233)
            ·
              refine ⟨3434156994417726858486925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4578875992556969144649233 3434156994417726858486925)
              ·
                refine ⟨1287808872906647571932597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3434156994417726858486925 1287808872906647571932597)
                ·
                  refine ⟨120732081834998209868681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1287808872906647571932597 120732081834998209868681)
                  ·
                    rfl

theorem cell23_2116124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 5].length) (baseStart_2116124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116124 prefixEnd_2116124 := by exact prefixLift 2116124
  have htrace : WordTrace (prefixWord ++ tailWord_2116124) baseStart_2116124 baseEnd_2116124 := by
    simpa [prefixWord, tailWord_2116124, baseEnd_2116124] using wordTrace_append hprefix tailTrace_2116124
  have hstable : (prefixWord ++ tailWord_2116124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116124).length < 2 ^ (prefixWord ++ tailWord_2116124).sum := by decide
  have hdescent : baseEnd_2116124 < baseStart_2116124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116157 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 1, 3, 4]
def baseStart_2116157 : Nat := 118140960795 + 2116157 * 2 ^ 59
def prefixEnd_2116157 : Nat := 4983230072969 + 3 ^ 40 * 2116157 * 2
def baseEnd_2116157 : Nat := 1086605681376582259705477

theorem tailTrace_2116157 : CollatzResearch.WordTrace tailWord_2116157 prefixEnd_2116157 1086605681376582259705477 := by
  unfold tailWord_2116157
  simp only [CollatzResearch.WordTrace]
  refine ⟨77182586594532074687322725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51455057729688049791548483 77182586594532074687322725)
  ·
    refine ⟨14471734986474764003873011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77182586594532074687322725 14471734986474764003873011)
    ·
      refine ⟨21707602479712146005809517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14471734986474764003873011 21707602479712146005809517)
      ·
        refine ⟨8140350929892054752178569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21707602479712146005809517 8140350929892054752178569)
        ·
          refine ⟨6105263197419041064133927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8140350929892054752178569 6105263197419041064133927)
          ·
            refine ⟨9157894796128561596200891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6105263197419041064133927 9157894796128561596200891)
            ·
              refine ⟨13736842194192842394301337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9157894796128561596200891 13736842194192842394301337)
              ·
                refine ⟨10302631645644631795726003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13736842194192842394301337 10302631645644631795726003)
                ·
                  refine ⟨15453947468466947693589005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10302631645644631795726003 15453947468466947693589005)
                  ·
                    refine ⟨5795230300675105385095877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15453947468466947693589005 5795230300675105385095877)
                    ·
                      refine ⟨1086605681376582259705477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5795230300675105385095877 1086605681376582259705477)
                      ·
                        rfl

theorem cell23_2116157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_2116157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116157 prefixEnd_2116157 := by exact prefixLift 2116157
  have htrace : WordTrace (prefixWord ++ tailWord_2116157) baseStart_2116157 baseEnd_2116157 := by
    simpa [prefixWord, tailWord_2116157, baseEnd_2116157] using wordTrace_append hprefix tailTrace_2116157
  have hstable : (prefixWord ++ tailWord_2116157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116157).length < 2 ^ (prefixWord ++ tailWord_2116157).sum := by decide
  have hdescent : baseEnd_2116157 < baseStart_2116157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116177 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 1, 4, 3]
def baseStart_2116177 : Nat := 118140960795 + 2116177 * 2 ^ 59
def prefixEnd_2116177 : Nat := 4983230072969 + 3 ^ 40 * 2116177 * 2
def baseEnd_2116177 : Nat := 1086615950989672181455385

theorem tailTrace_2116177 : CollatzResearch.WordTrace tailWord_2116177 prefixEnd_2116177 1086615950989672181455385 := by
  unfold tailWord_2116177
  simp only [CollatzResearch.WordTrace]
  refine ⟨77183316054459618103050785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51455544036306412068700523 77183316054459618103050785)
  ·
    refine ⟨57887487040844713577288089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77183316054459618103050785 57887487040844713577288089)
    ·
      refine ⟨43415615280633535182966067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57887487040844713577288089 43415615280633535182966067)
      ·
        refine ⟨65123422920950302774449101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43415615280633535182966067 65123422920950302774449101)
        ·
          refine ⟨24421283595356363540418413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65123422920950302774449101 24421283595356363540418413)
          ·
            refine ⟨9157981348258636327656905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24421283595356363540418413 9157981348258636327656905)
            ·
              refine ⟨6868486011193977245742679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9157981348258636327656905 6868486011193977245742679)
              ·
                refine ⟨10302729016790965868614019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6868486011193977245742679 10302729016790965868614019)
                ·
                  refine ⟨15454093525186448802921029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10302729016790965868614019 15454093525186448802921029)
                  ·
                    refine ⟨2897642535972459150547693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15454093525186448802921029 2897642535972459150547693)
                    ·
                      refine ⟨1086615950989672181455385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2897642535972459150547693 1086615950989672181455385)
                      ·
                        rfl

theorem cell23_2116177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 4, 3].length) (baseStart_2116177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116177 prefixEnd_2116177 := by exact prefixLift 2116177
  have htrace : WordTrace (prefixWord ++ tailWord_2116177) baseStart_2116177 baseEnd_2116177 := by
    simpa [prefixWord, tailWord_2116177, baseEnd_2116177] using wordTrace_append hprefix tailTrace_2116177
  have hstable : (prefixWord ++ tailWord_2116177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116177).length < 2 ^ (prefixWord ++ tailWord_2116177).sum := by decide
  have hdescent : baseEnd_2116177 < baseStart_2116177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116284 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 3, 2, 3]
def baseStart_2116284 : Nat := 118140960795 + 2116284 * 2 ^ 59
def prefixEnd_2116284 : Nat := 4983230072969 + 3 ^ 40 * 2116284 * 2
def baseEnd_2116284 : Nat := 1086670893419703262817393

theorem tailTrace_2116284 : CollatzResearch.WordTrace tailWord_2116284 prefixEnd_2116284 1086670893419703262817393 := by
  unfold tailWord_2116284
  simp only [CollatzResearch.WordTrace]
  refine ⟨38593609332535987688597953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51458145776714650251463937 38593609332535987688597953)
  ·
    refine ⟨28945206999401990766448465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38593609332535987688597953 28945206999401990766448465)
    ·
      refine ⟨21708905249551493074836349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28945206999401990766448465 21708905249551493074836349)
      ·
        refine ⟨8140839468581809903063631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21708905249551493074836349 8140839468581809903063631)
        ·
          refine ⟨12211259202872714854595447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8140839468581809903063631 12211259202872714854595447)
          ·
            refine ⟨18316888804309072281893171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12211259202872714854595447 18316888804309072281893171)
            ·
              refine ⟨27475333206463608422839757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18316888804309072281893171 27475333206463608422839757)
              ·
                refine ⟨10303249952423853158564909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27475333206463608422839757 10303249952423853158564909)
                ·
                  refine ⟨3863718732158944934461841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10303249952423853158564909 3863718732158944934461841)
                  ·
                    refine ⟨2897789049119208700846381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3863718732158944934461841 2897789049119208700846381)
                    ·
                      refine ⟨1086670893419703262817393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2897789049119208700846381 1086670893419703262817393)
                      ·
                        rfl

theorem cell23_2116284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_2116284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116284 prefixEnd_2116284 := by exact prefixLift 2116284
  have htrace : WordTrace (prefixWord ++ tailWord_2116284) baseStart_2116284 baseEnd_2116284 := by
    simpa [prefixWord, tailWord_2116284, baseEnd_2116284] using wordTrace_append hprefix tailTrace_2116284
  have hstable : (prefixWord ++ tailWord_2116284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116284).length < 2 ^ (prefixWord ++ tailWord_2116284).sum := by decide
  have hdescent : baseEnd_2116284 < baseStart_2116284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116298 : List Nat := [3, 1, 2, 1, 4, 3, 2, 1, 1, 1, 4]
def baseStart_2116298 : Nat := 118140960795 + 2116298 * 2 ^ 59
def prefixEnd_2116298 : Nat := 4983230072969 + 3 ^ 40 * 2116298 * 2
def baseEnd_2116298 : Nat := 1086678082148866208042329

theorem tailTrace_2116298 : CollatzResearch.WordTrace tailWord_2116298 prefixEnd_2116298 1086678082148866208042329 := by
  unfold tailWord_2116298
  simp only [CollatzResearch.WordTrace]
  refine ⟨19296932321755313942051387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51458486191347503845470365 19296932321755313942051387)
  ·
    refine ⟨28945398482632970913077081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19296932321755313942051387 28945398482632970913077081)
    ·
      refine ⟨21709048861974728184807811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28945398482632970913077081 21709048861974728184807811)
      ·
        refine ⟨32563573292962092277211717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21709048861974728184807811 32563573292962092277211717)
        ·
          refine ⟨6105669992430392301977197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32563573292962092277211717 6105669992430392301977197)
          ·
            refine ⟨2289626247161397113241449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6105669992430392301977197 2289626247161397113241449)
            ·
              refine ⟨1717219685371047834931087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2289626247161397113241449 1717219685371047834931087)
              ·
                refine ⟨2575829528056571752396631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1717219685371047834931087 2575829528056571752396631)
                ·
                  refine ⟨3863744292084857628594947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2575829528056571752396631 3863744292084857628594947)
                  ·
                    refine ⟨5795616438127286442892421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3863744292084857628594947 5795616438127286442892421)
                    ·
                      refine ⟨1086678082148866208042329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5795616438127286442892421 1086678082148866208042329)
                      ·
                        rfl

theorem cell23_2116298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 1, 1, 4].length) (baseStart_2116298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116298 prefixEnd_2116298 := by exact prefixLift 2116298
  have htrace : WordTrace (prefixWord ++ tailWord_2116298) baseStart_2116298 baseEnd_2116298 := by
    simpa [prefixWord, tailWord_2116298, baseEnd_2116298] using wordTrace_append hprefix tailTrace_2116298
  have hstable : (prefixWord ++ tailWord_2116298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116298).length < 2 ^ (prefixWord ++ tailWord_2116298).sum := by decide
  have hdescent : baseEnd_2116298 < baseStart_2116298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116328 : List Nat := [2, 1, 4, 1, 5, 1, 1, 1, 1, 2, 4]
def baseStart_2116328 : Nat := 118140960795 + 2116328 * 2 ^ 59
def prefixEnd_2116328 : Nat := 4983230072969 + 3 ^ 40 * 2116328 * 2
def baseEnd_2116328 : Nat := 1086693486568501090667191

theorem tailTrace_2116328 : CollatzResearch.WordTrace tailWord_2116328 prefixEnd_2116328 1086693486568501090667191 := by
  unfold tailWord_2116328
  simp only [CollatzResearch.WordTrace]
  refine ⟨38594411738456285445898819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51459215651275047261198425 38594411738456285445898819)
  ·
    refine ⟨57891617607684428168848229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38594411738456285445898819 57891617607684428168848229)
    ·
      refine ⟨10854678301440830281659043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57891617607684428168848229 10854678301440830281659043)
      ·
        refine ⟨16282017452161245422488565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10854678301440830281659043 16282017452161245422488565)
        ·
          refine ⟨1526439136140116758358303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16282017452161245422488565 1526439136140116758358303)
          ·
            refine ⟨2289658704210175137537455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1526439136140116758358303 2289658704210175137537455)
            ·
              refine ⟨3434488056315262706306183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2289658704210175137537455 3434488056315262706306183)
              ·
                refine ⟨5151732084472894059459275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3434488056315262706306183 5151732084472894059459275)
                ·
                  refine ⟨7727598126709341089188913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5151732084472894059459275 7727598126709341089188913)
                  ·
                    refine ⟨5795698595032005816891685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7727598126709341089188913 5795698595032005816891685)
                    ·
                      refine ⟨1086693486568501090667191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5795698595032005816891685 1086693486568501090667191)
                      ·
                        rfl

theorem cell23_2116328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_2116328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116328 prefixEnd_2116328 := by exact prefixLift 2116328
  have htrace : WordTrace (prefixWord ++ tailWord_2116328) baseStart_2116328 baseEnd_2116328 := by
    simpa [prefixWord, tailWord_2116328, baseEnd_2116328] using wordTrace_append hprefix tailTrace_2116328
  have hstable : (prefixWord ++ tailWord_2116328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116328).length < 2 ^ (prefixWord ++ tailWord_2116328).sum := by decide
  have hdescent : baseEnd_2116328 < baseStart_2116328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116371 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 4, 2, 2]
def baseStart_2116371 : Nat := 118140960795 + 2116371 * 2 ^ 59
def prefixEnd_2116371 : Nat := 4983230072969 + 3 ^ 40 * 2116371 * 2
def baseEnd_2116371 : Nat := 1086715566236644422429493

theorem tailTrace_2116371 : CollatzResearch.WordTrace tailWord_2116371 prefixEnd_2116371 1086715566236644422429493 := by
  unfold tailWord_2116371
  simp only [CollatzResearch.WordTrace]
  refine ⟨77190391815756789235612967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51460261210504526157075311 77190391815756789235612967)
  ·
    refine ⟨115785587723635183853419451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77190391815756789235612967 115785587723635183853419451)
    ·
      refine ⟨173678381585452775780129177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115785587723635183853419451 173678381585452775780129177)
      ·
        refine ⟨130258786189089581835096883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173678381585452775780129177 130258786189089581835096883)
        ·
          refine ⟨195388179283634372752645325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130258786189089581835096883 195388179283634372752645325)
          ·
            refine ⟨73270567231362889782241997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 195388179283634372752645325 73270567231362889782241997)
            ·
              refine ⟨27476462711761083668340749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73270567231362889782241997 27476462711761083668340749)
              ·
                refine ⟨10303673516910406375627781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27476462711761083668340749 10303673516910406375627781)
                ·
                  refine ⟨1931938784420701195430209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10303673516910406375627781 1931938784420701195430209)
                  ·
                    refine ⟨1448954088315525896572657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1931938784420701195430209 1448954088315525896572657)
                    ·
                      refine ⟨1086715566236644422429493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1448954088315525896572657 1086715566236644422429493)
                      ·
                        rfl

theorem cell23_2116371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 2, 2].length) (baseStart_2116371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116371 prefixEnd_2116371 := by exact prefixLift 2116371
  have htrace : WordTrace (prefixWord ++ tailWord_2116371) baseStart_2116371 baseEnd_2116371 := by
    simpa [prefixWord, tailWord_2116371, baseEnd_2116371] using wordTrace_append hprefix tailTrace_2116371
  have hstable : (prefixWord ++ tailWord_2116371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116371).length < 2 ^ (prefixWord ++ tailWord_2116371).sum := by decide
  have hdescent : baseEnd_2116371 < baseStart_2116371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116377 : List Nat := [1, 2, 1, 2, 1, 1, 1, 7, 7]
def baseStart_2116377 : Nat := 118140960795 + 2116377 * 2 ^ 59
def prefixEnd_2116377 : Nat := 4983230072969 + 3 ^ 40 * 2116377 * 2
def baseEnd_2116377 : Nat := 120746516346730155439385

theorem tailTrace_2116377 : CollatzResearch.WordTrace tailWord_2116377 prefixEnd_2116377 120746516346730155439385 := by
  unfold tailWord_2116377
  simp only [CollatzResearch.WordTrace]
  refine ⟨77190610653735052260331385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51460407102490034840220923 77190610653735052260331385)
  ·
    refine ⟨57892957990301289195248539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77190610653735052260331385 57892957990301289195248539)
    ·
      refine ⟨86839436985451933792872809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57892957990301289195248539 86839436985451933792872809)
      ·
        refine ⟨65129577739088950344654607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86839436985451933792872809 65129577739088950344654607)
        ·
          refine ⟨97694366608633425516981911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65129577739088950344654607 97694366608633425516981911)
          ·
            refine ⟨146541549912950138275472867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97694366608633425516981911 146541549912950138275472867)
            ·
              refine ⟨219812324869425207413209301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146541549912950138275472867 219812324869425207413209301)
              ·
                refine ⟨5151851364127153298747093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 219812324869425207413209301 5151851364127153298747093)
                ·
                  refine ⟨120746516346730155439385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5151851364127153298747093 120746516346730155439385)
                  ·
                    rfl

theorem cell23_2116377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 7].length) (baseStart_2116377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116377 prefixEnd_2116377 := by exact prefixLift 2116377
  have htrace : WordTrace (prefixWord ++ tailWord_2116377) baseStart_2116377 baseEnd_2116377 := by
    simpa [prefixWord, tailWord_2116377, baseEnd_2116377] using wordTrace_append hprefix tailTrace_2116377
  have hstable : (prefixWord ++ tailWord_2116377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116377).length < 2 ^ (prefixWord ++ tailWord_2116377).sum := by decide
  have hdescent : baseEnd_2116377 < baseStart_2116377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116424 : List Nat := [2, 1, 3, 1, 1, 3, 1, 4, 2, 5]
def baseStart_2116424 : Nat := 118140960795 + 2116424 * 2 ^ 59
def prefixEnd_2116424 : Nat := 4983230072969 + 3 ^ 40 * 2116424 * 2
def baseEnd_2116424 : Nat := 362247593570444238355583

theorem tailTrace_2116424 : CollatzResearch.WordTrace tailWord_2116424 prefixEnd_2116424 362247593570444238355583 := by
  unfold tailWord_2116424
  simp only [CollatzResearch.WordTrace]
  refine ⟨38596162442282389643646163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51461549923043186191528217 38596162442282389643646163)
  ·
    refine ⟨57894243663423584465469245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38596162442282389643646163 57894243663423584465469245)
    ·
      refine ⟨21710341373783844174550967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57894243663423584465469245 21710341373783844174550967)
      ·
        refine ⟨32565512060675766261826451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21710341373783844174550967 32565512060675766261826451)
        ·
          refine ⟨48848268091013649392739677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32565512060675766261826451 48848268091013649392739677)
          ·
            refine ⟨18318100534130118522277379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48848268091013649392739677 18318100534130118522277379)
            ·
              refine ⟨27477150801195177783416069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18318100534130118522277379 27477150801195177783416069)
              ·
                refine ⟨5151965775224095834390513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27477150801195177783416069 5151965775224095834390513)
                ·
                  refine ⟨3863974331418071875792885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5151965775224095834390513 3863974331418071875792885)
                  ·
                    refine ⟨362247593570444238355583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3863974331418071875792885 362247593570444238355583)
                    ·
                      rfl

theorem cell23_2116424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_2116424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116424 prefixEnd_2116424 := by exact prefixLift 2116424
  have htrace : WordTrace (prefixWord ++ tailWord_2116424) baseStart_2116424 baseEnd_2116424 := by
    simpa [prefixWord, tailWord_2116424, baseEnd_2116424] using wordTrace_append hprefix tailTrace_2116424
  have hstable : (prefixWord ++ tailWord_2116424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116424).length < 2 ^ (prefixWord ++ tailWord_2116424).sum := by decide
  have hdescent : baseEnd_2116424 < baseStart_2116424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116428 : List Nat := [2, 2, 1, 3, 3, 1, 4, 2, 5]
def baseStart_2116428 : Nat := 118140960795 + 2116428 * 2 ^ 59
def prefixEnd_2116428 : Nat := 4983230072969 + 3 ^ 40 * 2116428 * 2
def baseEnd_2116428 : Nat := 120749426070438966601859

theorem tailTrace_2116428 : CollatzResearch.WordTrace tailWord_2116428 prefixEnd_2116428 120749426070438966601859 := by
  unfold tailWord_2116428
  simp only [CollatzResearch.WordTrace]
  refine ⟨38596235388275143985218969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51461647184366858646958625 38596235388275143985218969)
  ·
    refine ⟨28947176541206357988914227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38596235388275143985218969 28947176541206357988914227)
    ·
      refine ⟨43420764811809536983371341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28947176541206357988914227 43420764811809536983371341)
      ·
        refine ⟨16282786804428576368764253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43420764811809536983371341 16282786804428576368764253)
        ·
          refine ⟨6106045051660716138286595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16282786804428576368764253 6106045051660716138286595)
          ·
            refine ⟨9159067577491074207429893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6106045051660716138286595 9159067577491074207429893)
            ·
              refine ⟨1717325170779576413893105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9159067577491074207429893 1717325170779576413893105)
              ·
                refine ⟨1287993878084682310419829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1717325170779576413893105 1287993878084682310419829)
                ·
                  refine ⟨120749426070438966601859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1287993878084682310419829 120749426070438966601859)
                  ·
                    rfl

theorem cell23_2116428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 5].length) (baseStart_2116428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116428 prefixEnd_2116428 := by exact prefixLift 2116428
  have htrace : WordTrace (prefixWord ++ tailWord_2116428) baseStart_2116428 baseEnd_2116428 := by
    simpa [prefixWord, tailWord_2116428, baseEnd_2116428] using wordTrace_append hprefix tailTrace_2116428
  have hstable : (prefixWord ++ tailWord_2116428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116428).length < 2 ^ (prefixWord ++ tailWord_2116428).sum := by decide
  have hdescent : baseEnd_2116428 < baseStart_2116428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116434 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_2116434 : Nat := 118140960795 + 2116434 * 2 ^ 59
def prefixEnd_2116434 : Nat := 4983230072969 + 3 ^ 40 * 2116434 * 2
def baseEnd_2116434 : Nat := 1086747915517877675941703

theorem tailTrace_2116434 : CollatzResearch.WordTrace tailWord_2116434 prefixEnd_2116434 1086747915517877675941703 := by
  unfold tailWord_2116434
  simp only [CollatzResearch.WordTrace]
  refine ⟨19298172403632137748789089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51461793076352367330104237 19298172403632137748789089)
  ·
    refine ⟨14473629302724103311591817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19298172403632137748789089 14473629302724103311591817)
    ·
      refine ⟨10855221977043077483693863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14473629302724103311591817 10855221977043077483693863)
      ·
        refine ⟨16282832965564616225540795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10855221977043077483693863 16282832965564616225540795)
        ·
          refine ⟨24424249448346924338311193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16282832965564616225540795 24424249448346924338311193)
          ·
            refine ⟨18318187086260193253733395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24424249448346924338311193 18318187086260193253733395)
            ·
              refine ⟨27477280629390289880600093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18318187086260193253733395 27477280629390289880600093)
              ·
                refine ⟨10303980236021358705225035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27477280629390289880600093 10303980236021358705225035)
                ·
                  refine ⟨15455970354032038057837553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10303980236021358705225035 15455970354032038057837553)
                  ·
                    refine ⟨11591977765524028543378165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15455970354032038057837553 11591977765524028543378165)
                    ·
                      refine ⟨1086747915517877675941703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11591977765524028543378165 1086747915517877675941703)
                      ·
                        rfl

theorem cell23_2116434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_2116434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116434 prefixEnd_2116434 := by exact prefixLift 2116434
  have htrace : WordTrace (prefixWord ++ tailWord_2116434) baseStart_2116434 baseEnd_2116434 := by
    simpa [prefixWord, tailWord_2116434, baseEnd_2116434] using wordTrace_append hprefix tailTrace_2116434
  have hstable : (prefixWord ++ tailWord_2116434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116434).length < 2 ^ (prefixWord ++ tailWord_2116434).sum := by decide
  have hdescent : baseEnd_2116434 < baseStart_2116434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116461 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 3, 6, 2]
def baseStart_2116461 : Nat := 118140960795 + 2116461 * 2 ^ 59
def prefixEnd_2116461 : Nat := 4983230072969 + 3 ^ 40 * 2116461 * 2
def baseEnd_2116461 : Nat := 1086761779495549070304079

theorem tailTrace_2116461 : CollatzResearch.WordTrace tailWord_2116461 prefixEnd_2116461 1086761779495549070304079 := by
  unfold tailWord_2116461
  simp only [CollatzResearch.WordTrace]
  refine ⟨77193674385430734606389237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51462449590287156404259491 77193674385430734606389237)
  ·
    refine ⟨7236906973634131369348991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77193674385430734606389237 7236906973634131369348991)
    ·
      refine ⟨10855360460451197054023487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7236906973634131369348991 10855360460451197054023487)
      ·
        refine ⟨16283040690676795581035231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10855360460451197054023487 16283040690676795581035231)
        ·
          refine ⟨24424561036015193371552847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16283040690676795581035231 24424561036015193371552847)
          ·
            refine ⟨36636841554022790057329271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24424561036015193371552847 36636841554022790057329271)
            ·
              refine ⟨54955262331034185085993907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36636841554022790057329271 54955262331034185085993907)
              ·
                refine ⟨82432893496551277628990861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54955262331034185085993907 82432893496551277628990861)
                ·
                  refine ⟨30912335061206729110871573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82432893496551277628990861 30912335061206729110871573)
                  ·
                    refine ⟨1449015705994065427072105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30912335061206729110871573 1449015705994065427072105)
                    ·
                      refine ⟨1086761779495549070304079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1449015705994065427072105 1086761779495549070304079)
                      ·
                        rfl

theorem cell23_2116461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_2116461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116461 prefixEnd_2116461 := by exact prefixLift 2116461
  have htrace : WordTrace (prefixWord ++ tailWord_2116461) baseStart_2116461 baseEnd_2116461 := by
    simpa [prefixWord, tailWord_2116461, baseEnd_2116461] using wordTrace_append hprefix tailTrace_2116461
  have hstable : (prefixWord ++ tailWord_2116461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116461).length < 2 ^ (prefixWord ++ tailWord_2116461).sum := by decide
  have hdescent : baseEnd_2116461 < baseStart_2116461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116488 : List Nat := [2, 1, 3, 3, 2, 2, 2, 1, 3, 4]
def baseStart_2116488 : Nat := 118140960795 + 2116488 * 2 ^ 59
def prefixEnd_2116488 : Nat := 4983230072969 + 3 ^ 40 * 2116488 * 2
def baseEnd_2116488 : Nat := 362258547824406821555485

theorem tailTrace_2116488 : CollatzResearch.WordTrace tailWord_2116488 prefixEnd_2116488 362258547824406821555485 := by
  unfold tailWord_2116488
  simp only [CollatzResearch.WordTrace]
  refine ⟨38597329578166459108811059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51463106104221945478414745 38597329578166459108811059)
  ·
    refine ⟨57895994367249688663216589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38597329578166459108811059 57895994367249688663216589)
    ·
      refine ⟨21710997887718633248706221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57895994367249688663216589 21710997887718633248706221)
      ·
        refine ⟨8141624207894487468264833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21710997887718633248706221 8141624207894487468264833)
        ·
          refine ⟨6106218155920865601198625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8141624207894487468264833 6106218155920865601198625)
          ·
            refine ⟨4579663616940649200898969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6106218155920865601198625 4579663616940649200898969)
            ·
              refine ⟨3434747712705486900674227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4579663616940649200898969 3434747712705486900674227)
              ·
                refine ⟨5152121569058230351011341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3434747712705486900674227 5152121569058230351011341)
                ·
                  refine ⟨1932045588396836381629253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5152121569058230351011341 1932045588396836381629253)
                  ·
                    refine ⟨362258547824406821555485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1932045588396836381629253 362258547824406821555485)
                    ·
                      rfl

theorem cell23_2116488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_2116488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116488 prefixEnd_2116488 := by exact prefixLift 2116488
  have htrace : WordTrace (prefixWord ++ tailWord_2116488) baseStart_2116488 baseEnd_2116488 := by
    simpa [prefixWord, tailWord_2116488, baseEnd_2116488] using wordTrace_append hprefix tailTrace_2116488
  have hstable : (prefixWord ++ tailWord_2116488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116488).length < 2 ^ (prefixWord ++ tailWord_2116488).sum := by decide
  have hdescent : baseEnd_2116488 < baseStart_2116488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116521 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 1, 5, 2]
def baseStart_2116521 : Nat := 118140960795 + 2116521 * 2 ^ 59
def prefixEnd_2116521 : Nat := 4983230072969 + 3 ^ 40 * 2116521 * 2
def baseEnd_2116521 : Nat := 1086792588334818835553803

theorem tailTrace_2116521 : CollatzResearch.WordTrace tailWord_2116521 prefixEnd_2116521 1086792588334818835553803 := by
  unfold tailWord_2116521
  simp only [CollatzResearch.WordTrace]
  refine ⟨77195862765213364853573417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51463908510142243235715611 77195862765213364853573417)
  ·
    refine ⟨57896897073910023640180063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77195862765213364853573417 57896897073910023640180063)
    ·
      refine ⟨86845345610865035460270095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57896897073910023640180063 86845345610865035460270095)
      ·
        refine ⟨130268018416297553190405143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86845345610865035460270095 130268018416297553190405143)
        ·
          refine ⟨195402027624446329785607715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130268018416297553190405143 195402027624446329785607715)
          ·
            refine ⟨293103041436669494678411573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195402027624446329785607715 293103041436669494678411573)
            ·
              refine ⟨27478410134687765126101085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 293103041436669494678411573 27478410134687765126101085)
              ·
                refine ⟨10304403800507911922287907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27478410134687765126101085 10304403800507911922287907)
                ·
                  refine ⟨15456605700761867883431861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10304403800507911922287907 15456605700761867883431861)
                  ·
                    refine ⟨1449056784446425114071737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15456605700761867883431861 1449056784446425114071737)
                    ·
                      refine ⟨1086792588334818835553803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1449056784446425114071737 1086792588334818835553803)
                      ·
                        rfl

theorem cell23_2116521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 5, 2].length) (baseStart_2116521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116521 prefixEnd_2116521 := by exact prefixLift 2116521
  have htrace : WordTrace (prefixWord ++ tailWord_2116521) baseStart_2116521 baseEnd_2116521 := by
    simpa [prefixWord, tailWord_2116521, baseEnd_2116521] using wordTrace_append hprefix tailTrace_2116521
  have hstable : (prefixWord ++ tailWord_2116521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116521).length < 2 ^ (prefixWord ++ tailWord_2116521).sum := by decide
  have hdescent : baseEnd_2116521 < baseStart_2116521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116538 : List Nat := [3, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2]
def baseStart_2116538 : Nat := 118140960795 + 2116538 * 2 ^ 59
def prefixEnd_2116538 : Nat := 4983230072969 + 3 ^ 40 * 2116538 * 2
def baseEnd_2116538 : Nat := 1086801317505945269041225

theorem tailTrace_2116538 : CollatzResearch.WordTrace tailWord_2116538 prefixEnd_2116538 1086801317505945269041225 := by
  unfold tailWord_2116538
  simp only [CollatzResearch.WordTrace]
  refine ⟨19299120701537944189235567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51464321870767851171294845 19299120701537944189235567)
  ·
    refine ⟨28948681052306916283853351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19299120701537944189235567 28948681052306916283853351)
    ·
      refine ⟨43423021578460374425780027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28948681052306916283853351 43423021578460374425780027)
      ·
        refine ⟨65134532367690561638670041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43423021578460374425780027 65134532367690561638670041)
        ·
          refine ⟨48850899275767921229002531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65134532367690561638670041 48850899275767921229002531)
          ·
            refine ⟨73276348913651881843503797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48850899275767921229002531 73276348913651881843503797)
            ·
              refine ⟨6869657710654863922828481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73276348913651881843503797 6869657710654863922828481)
              ·
                refine ⟨5152243282991147942121361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6869657710654863922828481 5152243282991147942121361)
                ·
                  refine ⟨3864182462243360956591021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5152243282991147942121361 3864182462243360956591021)
                  ·
                    refine ⟨1449068423341260358721633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3864182462243360956591021 1449068423341260358721633)
                    ·
                      refine ⟨1086801317505945269041225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1449068423341260358721633 1086801317505945269041225)
                      ·
                        rfl

theorem cell23_2116538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2].length) (baseStart_2116538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116538 prefixEnd_2116538 := by exact prefixLift 2116538
  have htrace : WordTrace (prefixWord ++ tailWord_2116538) baseStart_2116538 baseEnd_2116538 := by
    simpa [prefixWord, tailWord_2116538, baseEnd_2116538] using wordTrace_append hprefix tailTrace_2116538
  have hstable : (prefixWord ++ tailWord_2116538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116538).length < 2 ^ (prefixWord ++ tailWord_2116538).sum := by decide
  have hdescent : baseEnd_2116538 < baseStart_2116538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116565 : List Nat := [1, 3, 2, 3, 3, 2, 1, 2, 1, 5]
def baseStart_2116565 : Nat := 118140960795 + 2116565 * 2 ^ 59
def prefixEnd_2116565 : Nat := 4983230072969 + 3 ^ 40 * 2116565 * 2
def baseEnd_2116565 : Nat := 362271727161205554467867

theorem tailTrace_2116565 : CollatzResearch.WordTrace tailWord_2116565 prefixEnd_2116565 362271727161205554467867 := by
  unfold tailWord_2116565
  simp only [CollatzResearch.WordTrace]
  refine ⟨77197467577053960368175149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51464978384702640245450099 77197467577053960368175149)
  ·
    refine ⟨28949050341395235138065681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77197467577053960368175149 28949050341395235138065681)
    ·
      refine ⟨21711787756046426353549261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28949050341395235138065681 21711787756046426353549261)
      ·
        refine ⟨8141920408517409882580973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21711787756046426353549261 8141920408517409882580973)
        ·
          refine ⟨3053220153194028705967865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8141920408517409882580973 3053220153194028705967865)
          ·
            refine ⟨2289915114895521529475899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3053220153194028705967865 2289915114895521529475899)
            ·
              refine ⟨3434872672343282294213849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2289915114895521529475899 3434872672343282294213849)
              ·
                refine ⟨2576154504257461720660387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3434872672343282294213849 2576154504257461720660387)
                ·
                  refine ⟨3864231756386192580990581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2576154504257461720660387 3864231756386192580990581)
                  ·
                    refine ⟨362271727161205554467867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3864231756386192580990581 362271727161205554467867)
                    ·
                      rfl

theorem cell23_2116565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_2116565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116565 prefixEnd_2116565 := by exact prefixLift 2116565
  have htrace : WordTrace (prefixWord ++ tailWord_2116565) baseStart_2116565 baseEnd_2116565 := by
    simpa [prefixWord, tailWord_2116565, baseEnd_2116565] using wordTrace_append hprefix tailTrace_2116565
  have hstable : (prefixWord ++ tailWord_2116565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116565).length < 2 ^ (prefixWord ++ tailWord_2116565).sum := by decide
  have hdescent : baseEnd_2116565 < baseStart_2116565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116568 : List Nat := [2, 1, 2, 2, 2, 3, 3, 2, 1, 1, 4]
def baseStart_2116568 : Nat := 118140960795 + 2116568 * 2 ^ 59
def prefixEnd_2116568 : Nat := 4983230072969 + 3 ^ 40 * 2116568 * 2
def baseEnd_2116568 : Nat := 1086816721925580151666087

theorem tailTrace_2116568 : CollatzResearch.WordTrace tailWord_2116568 prefixEnd_2116568 1086816721925580151666087 := by
  unfold tailWord_2116568
  simp only [CollatzResearch.WordTrace]
  refine ⟨38598788498021545940267179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51465051330695394587022905 38598788498021545940267179)
  ·
    refine ⟨57898182747032318910400769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38598788498021545940267179 57898182747032318910400769)
    ·
      refine ⟨43423637060274239182800577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57898182747032318910400769 43423637060274239182800577)
      ·
        refine ⟨32567727795205679387100433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43423637060274239182800577 32567727795205679387100433)
        ·
          refine ⟨24425795846404259540325325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32567727795205679387100433 24425795846404259540325325)
          ·
            refine ⟨9159673442401597327621997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24425795846404259540325325 9159673442401597327621997)
            ·
              refine ⟨3434877540900598997858249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9159673442401597327621997 3434877540900598997858249)
              ·
                refine ⟨2576158155675449248393687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3434877540900598997858249 2576158155675449248393687)
                ·
                  refine ⟨3864237233513173872590531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2576158155675449248393687 3864237233513173872590531)
                  ·
                    refine ⟨5796355850269760808885797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3864237233513173872590531 5796355850269760808885797)
                    ·
                      refine ⟨1086816721925580151666087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5796355850269760808885797 1086816721925580151666087)
                      ·
                        rfl

theorem cell23_2116568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_2116568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116568 prefixEnd_2116568 := by exact prefixLift 2116568
  have htrace : WordTrace (prefixWord ++ tailWord_2116568) baseStart_2116568 baseEnd_2116568 := by
    simpa [prefixWord, tailWord_2116568, baseEnd_2116568] using wordTrace_append hprefix tailTrace_2116568
  have hstable : (prefixWord ++ tailWord_2116568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116568).length < 2 ^ (prefixWord ++ tailWord_2116568).sum := by decide
  have hdescent : baseEnd_2116568 < baseStart_2116568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116578 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 3, 6]
def baseStart_2116578 : Nat := 118140960795 + 2116578 * 2 ^ 59
def prefixEnd_2116578 : Nat := 4983230072969 + 3 ^ 40 * 2116578 * 2
def baseEnd_2116578 : Nat := 362273952244041704180347

theorem tailTrace_2116578 : CollatzResearch.WordTrace tailWord_2116578 prefixEnd_2116578 362273952244041704180347 := by
  unfold tailWord_2116578
  simp only [CollatzResearch.WordTrace]
  refine ⟨19299485431501715897099597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51465294484004575725598925 19299485431501715897099597)
  ·
    refine ⟨7237307036813143461412349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19299485431501715897099597 7237307036813143461412349)
    ·
      refine ⟨2713990138804928798029631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7237307036813143461412349 2713990138804928798029631)
      ·
        refine ⟨4070985208207393197044447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2713990138804928798029631 4070985208207393197044447)
        ·
          refine ⟨6106477812311089795566671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4070985208207393197044447 6106477812311089795566671)
          ·
            refine ⟨9159716718466634693350007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6106477812311089795566671 9159716718466634693350007)
            ·
              refine ⟨13739575077699952040025011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9159716718466634693350007 13739575077699952040025011)
              ·
                refine ⟨20609362616549928060037517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13739575077699952040025011 20609362616549928060037517)
                ·
                  refine ⟨7728510981206223022514069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20609362616549928060037517 7728510981206223022514069)
                  ·
                    refine ⟨362273952244041704180347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7728510981206223022514069 362273952244041704180347)
                    ·
                      rfl

theorem cell23_2116578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_2116578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116578 prefixEnd_2116578 := by exact prefixLift 2116578
  have htrace : WordTrace (prefixWord ++ tailWord_2116578) baseStart_2116578 baseEnd_2116578 := by
    simpa [prefixWord, tailWord_2116578, baseEnd_2116578] using wordTrace_append hprefix tailTrace_2116578
  have hstable : (prefixWord ++ tailWord_2116578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116578).length < 2 ^ (prefixWord ++ tailWord_2116578).sum := by decide
  have hdescent : baseEnd_2116578 < baseStart_2116578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116601 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 3, 3, 3]
def baseStart_2116601 : Nat := 118140960795 + 2116601 * 2 ^ 59
def prefixEnd_2116601 : Nat := 4983230072969 + 3 ^ 40 * 2116601 * 2
def baseEnd_2116601 : Nat := 1086833666787178522553435

theorem tailTrace_2116601 : CollatzResearch.WordTrace tailWord_2116601 prefixEnd_2116601 1086833666787178522553435 := by
  unfold tailWord_2116601
  simp only [CollatzResearch.WordTrace]
  refine ⟨77198780604923538516485657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51465853736615692344323771 77198780604923538516485657)
  ·
    refine ⟨57899085453692653887364243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77198780604923538516485657 57899085453692653887364243)
    ·
      refine ⟨86848628180538980831046365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57899085453692653887364243 86848628180538980831046365)
      ·
        refine ⟨32568235567702117811642387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86848628180538980831046365 32568235567702117811642387)
        ·
          refine ⟨48852353351553176717463581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32568235567702117811642387 48852353351553176717463581)
          ·
            refine ⟨18319632506832441269048843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48852353351553176717463581 18319632506832441269048843)
            ·
              refine ⟨27479448760248661903573265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18319632506832441269048843 27479448760248661903573265)
              ·
                refine ⟨20609586570186496427679949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27479448760248661903573265 20609586570186496427679949)
                ·
                  refine ⟨7728594963819936160379981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20609586570186496427679949 7728594963819936160379981)
                  ·
                    refine ⟨2898223111432476060142493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7728594963819936160379981 2898223111432476060142493)
                    ·
                      refine ⟨1086833666787178522553435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2898223111432476060142493 1086833666787178522553435)
                      ·
                        rfl

theorem cell23_2116601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_2116601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116601 prefixEnd_2116601 := by exact prefixLift 2116601
  have htrace : WordTrace (prefixWord ++ tailWord_2116601) baseStart_2116601 baseEnd_2116601 := by
    simpa [prefixWord, tailWord_2116601, baseEnd_2116601] using wordTrace_append hprefix tailTrace_2116601
  have hstable : (prefixWord ++ tailWord_2116601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116601).length < 2 ^ (prefixWord ++ tailWord_2116601).sum := by decide
  have hdescent : baseEnd_2116601 < baseStart_2116601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116618 : List Nat := [3, 1, 2, 2, 3, 1, 1, 3, 1, 3, 3]
def baseStart_2116618 : Nat := 118140960795 + 2116618 * 2 ^ 59
def prefixEnd_2116618 : Nat := 4983230072969 + 3 ^ 40 * 2116618 * 2
def baseEnd_2116618 : Nat := 1086842395958304956040857

theorem tailTrace_2116618 : CollatzResearch.WordTrace tailWord_2116618 prefixEnd_2116618 1086842395958304956040857 := by
  unfold tailWord_2116618
  simp only [CollatzResearch.WordTrace]
  refine ⟨19299850161465487604963627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51466267097241300279903005 19299850161465487604963627)
  ·
    refine ⟨28949775242198231407445441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19299850161465487604963627 28949775242198231407445441)
    ·
      refine ⟨21712331431648673555584081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28949775242198231407445441 21712331431648673555584081)
      ·
        refine ⟨16284248573736505166688061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21712331431648673555584081 16284248573736505166688061)
        ·
          refine ⟨6106593215151189437508023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16284248573736505166688061 6106593215151189437508023)
          ·
            refine ⟨9159889822726784156262035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6106593215151189437508023 9159889822726784156262035)
            ·
              refine ⟨13739834734090176234393053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9159889822726784156262035 13739834734090176234393053)
              ·
                refine ⟨5152438025283816087897395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13739834734090176234393053 5152438025283816087897395)
                ·
                  refine ⟨7728657037925724131846093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5152438025283816087897395 7728657037925724131846093)
                  ·
                    refine ⟨2898246389222146549442285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7728657037925724131846093 2898246389222146549442285)
                    ·
                      refine ⟨1086842395958304956040857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2898246389222146549442285 1086842395958304956040857)
                      ·
                        rfl

theorem cell23_2116618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_2116618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116618 prefixEnd_2116618 := by exact prefixLift 2116618
  have htrace : WordTrace (prefixWord ++ tailWord_2116618) baseStart_2116618 baseEnd_2116618 := by
    simpa [prefixWord, tailWord_2116618, baseEnd_2116618] using wordTrace_append hprefix tailTrace_2116618
  have hstable : (prefixWord ++ tailWord_2116618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116618).length < 2 ^ (prefixWord ++ tailWord_2116618).sum := by decide
  have hdescent : baseEnd_2116618 < baseStart_2116618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116624 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 10]
def baseStart_2116624 : Nat := 118140960795 + 2116624 * 2 ^ 59
def prefixEnd_2116624 : Nat := 4983230072969 + 3 ^ 40 * 2116624 * 2
def baseEnd_2116624 : Nat := 1086845476842231932565829

theorem tailTrace_2116624 : CollatzResearch.WordTrace tailWord_2116624 prefixEnd_2116624 1086845476842231932565829 := by
  unfold tailWord_2116624
  simp only [CollatzResearch.WordTrace]
  refine ⟨38599809741920106722286463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51466412989226808963048617 38599809741920106722286463)
  ·
    refine ⟨57899714612880160083429695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38599809741920106722286463 57899714612880160083429695)
    ·
      refine ⟨86849571919320240125144543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57899714612880160083429695 86849571919320240125144543)
      ·
        refine ⟨130274357878980360187716815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86849571919320240125144543 130274357878980360187716815)
        ·
          refine ⟨195411536818470540281575223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130274357878980360187716815 195411536818470540281575223)
          ·
            refine ⟨293117305227705810422362835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195411536818470540281575223 293117305227705810422362835)
            ·
              refine ⟨439675957841558715633544253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293117305227705810422362835 439675957841558715633544253)
              ·
                refine ⟨164878484190584518362579095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 439675957841558715633544253 164878484190584518362579095)
                ·
                  refine ⟨247317726285876777543868643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164878484190584518362579095 247317726285876777543868643)
                  ·
                    refine ⟨370976589428815166315802965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 247317726285876777543868643 370976589428815166315802965)
                    ·
                      refine ⟨1086845476842231932565829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 370976589428815166315802965 1086845476842231932565829)
                      ·
                        rfl

theorem cell23_2116624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_2116624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116624 prefixEnd_2116624 := by exact prefixLift 2116624
  have htrace : WordTrace (prefixWord ++ tailWord_2116624) baseStart_2116624 baseEnd_2116624 := by
    simpa [prefixWord, tailWord_2116624, baseEnd_2116624] using wordTrace_append hprefix tailTrace_2116624
  have hstable : (prefixWord ++ tailWord_2116624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116624).length < 2 ^ (prefixWord ++ tailWord_2116624).sum := by decide
  have hdescent : baseEnd_2116624 < baseStart_2116624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116645 : List Nat := [1, 3, 1, 2, 2, 2, 3, 3, 1, 3, 2]
def baseStart_2116645 : Nat := 118140960795 + 2116645 * 2 ^ 59
def prefixEnd_2116645 : Nat := 4983230072969 + 3 ^ 40 * 2116645 * 2
def baseEnd_2116645 : Nat := 1086856259935976350403233

theorem tailTrace_2116645 : CollatzResearch.WordTrace tailWord_2116645 prefixEnd_2116645 1086856259935976350403233 := by
  unfold tailWord_2116645
  simp only [CollatzResearch.WordTrace]
  refine ⟨77200385416764134031087389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51466923611176089354058259 77200385416764134031087389)
  ·
    refine ⟨28950144531286550261657771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77200385416764134031087389 28950144531286550261657771)
    ·
      refine ⟨43425216796929825392486657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28950144531286550261657771 43425216796929825392486657)
      ·
        refine ⟨32568912597697369044364993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43425216796929825392486657 32568912597697369044364993)
        ·
          refine ⟨24426684448273026783273745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32568912597697369044364993 24426684448273026783273745)
          ·
            refine ⟨18320013336204770087455309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24426684448273026783273745 18320013336204770087455309)
            ·
              refine ⟨6870005001076788782795741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18320013336204770087455309 6870005001076788782795741)
              ·
                refine ⟨2576251875403795793548403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6870005001076788782795741 2576251875403795793548403)
                ·
                  refine ⟨3864377813105693690322605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2576251875403795793548403 3864377813105693690322605)
                  ·
                    refine ⟨1449141679914635133870977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3864377813105693690322605 1449141679914635133870977)
                    ·
                      refine ⟨1086856259935976350403233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1449141679914635133870977 1086856259935976350403233)
                      ·
                        rfl

theorem cell23_2116645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 3, 2].length) (baseStart_2116645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116645 prefixEnd_2116645 := by exact prefixLift 2116645
  have htrace : WordTrace (prefixWord ++ tailWord_2116645) baseStart_2116645 baseEnd_2116645 := by
    simpa [prefixWord, tailWord_2116645, baseEnd_2116645] using wordTrace_append hprefix tailTrace_2116645
  have hstable : (prefixWord ++ tailWord_2116645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116645).length < 2 ^ (prefixWord ++ tailWord_2116645).sum := by decide
  have hdescent : baseEnd_2116645 < baseStart_2116645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116661 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_2116661 : Nat := 118140960795 + 2116661 * 2 ^ 59
def prefixEnd_2116661 : Nat := 4983230072969 + 3 ^ 40 * 2116661 * 2
def baseEnd_2116661 : Nat := 1086864475626448287803159

theorem tailTrace_2116661 : CollatzResearch.WordTrace tailWord_2116661 prefixEnd_2116661 1086864475626448287803159 := by
  unfold tailWord_2116661
  simp only [CollatzResearch.WordTrace]
  refine ⟨77200968984706168763669837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51467312656470779175779891 77200968984706168763669837)
  ·
    refine ⟨28950363369264813286376189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77200968984706168763669837 28950363369264813286376189)
    ·
      refine ⟨10856386263474304982391071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28950363369264813286376189 10856386263474304982391071)
      ·
        refine ⟨16284579395211457473586607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10856386263474304982391071 16284579395211457473586607)
        ·
          refine ⟨24426869092817186210379911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16284579395211457473586607 24426869092817186210379911)
          ·
            refine ⟨36640303639225779315569867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24426869092817186210379911 36640303639225779315569867)
            ·
              refine ⟨54960455458838668973354801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36640303639225779315569867 54960455458838668973354801)
              ·
                refine ⟨41220341594129001730016101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54960455458838668973354801 41220341594129001730016101)
                ·
                  refine ⟨7728814048899187824378019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41220341594129001730016101 7728814048899187824378019)
                  ·
                    refine ⟨11593221073348781736567029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7728814048899187824378019 11593221073348781736567029)
                    ·
                      refine ⟨1086864475626448287803159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11593221073348781736567029 1086864475626448287803159)
                      ·
                        rfl

theorem cell23_2116661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_2116661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116661 prefixEnd_2116661 := by exact prefixLift 2116661
  have htrace : WordTrace (prefixWord ++ tailWord_2116661) baseStart_2116661 baseEnd_2116661 := by
    simpa [prefixWord, tailWord_2116661, baseEnd_2116661] using wordTrace_append hprefix tailTrace_2116661
  have hstable : (prefixWord ++ tailWord_2116661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116661).length < 2 ^ (prefixWord ++ tailWord_2116661).sum := by decide
  have hdescent : baseEnd_2116661 < baseStart_2116661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116691 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 3]
def baseStart_2116691 : Nat := 118140960795 + 2116691 * 2 ^ 59
def prefixEnd_2116691 : Nat := 4983230072969 + 3 ^ 40 * 2116691 * 2
def baseEnd_2116691 : Nat := 1086879880046083170428021

theorem tailTrace_2116691 : CollatzResearch.WordTrace tailWord_2116691 prefixEnd_2116691 1086879880046083170428021 := by
  unfold tailWord_2116691
  simp only [CollatzResearch.WordTrace]
  refine ⟨77202063174597483887261927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51468042116398322591507951 77202063174597483887261927)
  ·
    refine ⟨115803094761896225830892891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77202063174597483887261927 115803094761896225830892891)
    ·
      refine ⟨173704642142844338746339337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115803094761896225830892891 173704642142844338746339337)
      ·
        refine ⟨130278481607133254059754503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173704642142844338746339337 130278481607133254059754503)
        ·
          refine ⟨195417722410699881089631755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130278481607133254059754503 195417722410699881089631755)
          ·
            refine ⟨293126583616049821634447633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195417722410699881089631755 293126583616049821634447633)
            ·
              refine ⟨219844937712037366225835725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 293126583616049821634447633 219844937712037366225835725)
              ·
                refine ⟨82441851642014012334688397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 219844937712037366225835725 82441851642014012334688397)
                ·
                  refine ⟨30915694365755254625508149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82441851642014012334688397 30915694365755254625508149)
                  ·
                    refine ⟨2898346346789555121141389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30915694365755254625508149 2898346346789555121141389)
                    ·
                      refine ⟨1086879880046083170428021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2898346346789555121141389 1086879880046083170428021)
                      ·
                        rfl

theorem cell23_2116691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 3].length) (baseStart_2116691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116691 prefixEnd_2116691 := by exact prefixLift 2116691
  have htrace : WordTrace (prefixWord ++ tailWord_2116691) baseStart_2116691 baseEnd_2116691 := by
    simpa [prefixWord, tailWord_2116691, baseEnd_2116691] using wordTrace_append hprefix tailTrace_2116691
  have hstable : (prefixWord ++ tailWord_2116691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116691).length < 2 ^ (prefixWord ++ tailWord_2116691).sum := by decide
  have hdescent : baseEnd_2116691 < baseStart_2116691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116698 : List Nat := [3, 1, 1, 2, 1, 1, 2, 7, 5]
def baseStart_2116698 : Nat := 118140960795 + 2116698 * 2 ^ 59
def prefixEnd_2116698 : Nat := 4983230072969 + 3 ^ 40 * 2116698 * 2
def baseEnd_2116698 : Nat := 120764830490073849226721

theorem tailTrace_2116698 : CollatzResearch.WordTrace tailWord_2116698 prefixEnd_2116698 120764830490073849226721 := by
  unfold tailWord_2116698
  simp only [CollatzResearch.WordTrace]
  refine ⟨19300579621393031020691687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51468212323714749388511165 19300579621393031020691687)
  ·
    refine ⟨28950869432089546531037531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19300579621393031020691687 28950869432089546531037531)
    ·
      refine ⟨43426304148134319796556297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28950869432089546531037531 43426304148134319796556297)
      ·
        refine ⟨32569728111100739847417223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43426304148134319796556297 32569728111100739847417223)
        ·
          refine ⟨48854592166651109771125835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32569728111100739847417223 48854592166651109771125835)
          ·
            refine ⟨73281888249976664656688753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48854592166651109771125835 73281888249976664656688753)
            ·
              refine ⟨54961416187482498492516565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73281888249976664656688753 54961416187482498492516565)
              ·
                refine ⟨1288158191894121058418357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 54961416187482498492516565 1288158191894121058418357)
                ·
                  refine ⟨120764830490073849226721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1288158191894121058418357 120764830490073849226721)
                  ·
                    rfl

theorem cell23_2116698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 5].length) (baseStart_2116698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116698 prefixEnd_2116698 := by exact prefixLift 2116698
  have htrace : WordTrace (prefixWord ++ tailWord_2116698) baseStart_2116698 baseEnd_2116698 := by
    simpa [prefixWord, tailWord_2116698, baseEnd_2116698] using wordTrace_append hprefix tailTrace_2116698
  have hstable : (prefixWord ++ tailWord_2116698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116698).length < 2 ^ (prefixWord ++ tailWord_2116698).sum := by decide
  have hdescent : baseEnd_2116698 < baseStart_2116698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116731 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 4]
def baseStart_2116731 : Nat := 118140960795 + 2116731 * 2 ^ 59
def prefixEnd_2116731 : Nat := 4983230072969 + 3 ^ 40 * 2116731 * 2
def baseEnd_2116731 : Nat := 1086900419272263013927837

theorem tailTrace_2116731 : CollatzResearch.WordTrace tailWord_2116731 prefixEnd_2116731 1086900419272263013927837 := by
  unfold tailWord_2116731
  simp only [CollatzResearch.WordTrace]
  refine ⟨77203522094452570718718047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51469014729635047145812031 77203522094452570718718047)
  ·
    refine ⟨115805283141678856078077071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77203522094452570718718047 115805283141678856078077071)
    ·
      refine ⟨173707924712518284117115607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115805283141678856078077071 173707924712518284117115607)
      ·
        refine ⟨260561887068777426175673411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173707924712518284117115607 260561887068777426175673411)
        ·
          refine ⟨390842830603166139263510117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260561887068777426175673411 390842830603166139263510117)
          ·
            refine ⟨73283030738093651111908147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 390842830603166139263510117 73283030738093651111908147)
            ·
              refine ⟨109924546107140476667862221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73283030738093651111908147 109924546107140476667862221)
              ·
                refine ⟨41221704790177678750448333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109924546107140476667862221 41221704790177678750448333)
                ·
                  refine ⟨15458139296316629531418125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41221704790177678750448333 15458139296316629531418125)
                  ·
                    refine ⟨5796802236118736074281797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15458139296316629531418125 5796802236118736074281797)
                    ·
                      refine ⟨1086900419272263013927837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5796802236118736074281797 1086900419272263013927837)
                      ·
                        rfl

theorem cell23_2116731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 4].length) (baseStart_2116731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116731 prefixEnd_2116731 := by exact prefixLift 2116731
  have htrace : WordTrace (prefixWord ++ tailWord_2116731) baseStart_2116731 baseEnd_2116731 := by
    simpa [prefixWord, tailWord_2116731, baseEnd_2116731] using wordTrace_append hprefix tailTrace_2116731
  have hstable : (prefixWord ++ tailWord_2116731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116731).length < 2 ^ (prefixWord ++ tailWord_2116731).sum := by decide
  have hdescent : baseEnd_2116731 < baseStart_2116731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116765 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 2, 4, 2]
def baseStart_2116765 : Nat := 118140960795 + 2116765 * 2 ^ 59
def prefixEnd_2116765 : Nat := 4983230072969 + 3 ^ 40 * 2116765 * 2
def baseEnd_2116765 : Nat := 1086917877614515880902681

theorem tailTrace_2116765 : CollatzResearch.WordTrace tailWord_2116765 prefixEnd_2116765 1086917877614515880902681 := by
  unfold tailWord_2116765
  simp only [CollatzResearch.WordTrace]
  refine ⟨77204762176329394525455749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51469841450886263016970499 77204762176329394525455749)
  ·
    refine ⟨14475892908061761473522953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77204762176329394525455749 14475892908061761473522953)
    ·
      refine ⟨10856919681046321105142215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14475892908061761473522953 10856919681046321105142215)
      ·
        refine ⟨16285379521569481657713323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10856919681046321105142215 16285379521569481657713323)
        ·
          refine ⟨24428069282354222486569985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16285379521569481657713323 24428069282354222486569985)
          ·
            refine ⟨18321051961765666864927489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24428069282354222486569985 18321051961765666864927489)
            ·
              refine ⟨13740788971324250148695617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18321051961765666864927489 13740788971324250148695617)
              ·
                refine ⟨10305591728493187611521713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13740788971324250148695617 10305591728493187611521713)
                ·
                  refine ⟨7729193796369890708641285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10305591728493187611521713 7729193796369890708641285)
                  ·
                    refine ⟨1449223836819354507870241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7729193796369890708641285 1449223836819354507870241)
                    ·
                      refine ⟨1086917877614515880902681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1449223836819354507870241 1086917877614515880902681)
                      ·
                        rfl

theorem cell23_2116765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_2116765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116765 prefixEnd_2116765 := by exact prefixLift 2116765
  have htrace : WordTrace (prefixWord ++ tailWord_2116765) baseStart_2116765 baseEnd_2116765 := by
    simpa [prefixWord, tailWord_2116765, baseEnd_2116765] using wordTrace_append hprefix tailTrace_2116765
  have hstable : (prefixWord ++ tailWord_2116765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116765).length < 2 ^ (prefixWord ++ tailWord_2116765).sum := by decide
  have hdescent : baseEnd_2116765 < baseStart_2116765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116771 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 8]
def baseStart_2116771 : Nat := 118140960795 + 2116771 * 2 ^ 59
def prefixEnd_2116771 : Nat := 4983230072969 + 3 ^ 40 * 2116771 * 2
def baseEnd_2116771 : Nat := 120768995388715873047517

theorem tailTrace_2116771 : CollatzResearch.WordTrace tailWord_2116771 prefixEnd_2116771 120768995388715873047517 := by
  unfold tailWord_2116771
  simp only [CollatzResearch.WordTrace]
  refine ⟨77204981014307657550174167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51469987342871771700116111 77204981014307657550174167)
  ·
    refine ⟨115807471521461486325261251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77204981014307657550174167 115807471521461486325261251)
    ·
      refine ⟨173711207282192229487891877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115807471521461486325261251 173711207282192229487891877)
      ·
        refine ⟨32570851365411043028979727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173711207282192229487891877 32570851365411043028979727)
        ·
          refine ⟨48856277048116564543469591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32570851365411043028979727 48856277048116564543469591)
          ·
            refine ⟨73284415572174846815204387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48856277048116564543469591 73284415572174846815204387)
            ·
              refine ⟨109926623358262270222806581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73284415572174846815204387 109926623358262270222806581)
              ·
                refine ⟨10305620939837087833388117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109926623358262270222806581 10305620939837087833388117)
                ·
                  refine ⟨120768995388715873047517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10305620939837087833388117 120768995388715873047517)
                  ·
                    rfl

theorem cell23_2116771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 8].length) (baseStart_2116771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116771 prefixEnd_2116771 := by exact prefixLift 2116771
  have htrace : WordTrace (prefixWord ++ tailWord_2116771) baseStart_2116771 baseEnd_2116771 := by
    simpa [prefixWord, tailWord_2116771, baseEnd_2116771] using wordTrace_append hprefix tailTrace_2116771
  have hstable : (prefixWord ++ tailWord_2116771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116771).length < 2 ^ (prefixWord ++ tailWord_2116771).sum := by decide
  have hdescent : baseEnd_2116771 < baseStart_2116771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116822 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 8]
def baseStart_2116822 : Nat := 118140960795 + 2116822 * 2 ^ 59
def prefixEnd_2116822 : Nat := 4983230072969 + 3 ^ 40 * 2116822 * 2
def baseEnd_2116822 : Nat := 120771905112424684209991

theorem tailTrace_2116822 : CollatzResearch.WordTrace tailWord_2116822 prefixEnd_2116822 120771905112424684209991 := by
  unfold tailWord_2116822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4825427571070180828767545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51471227424748595506853813 4825427571070180828767545)
  ·
    refine ⟨3619070678302635621575659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4825427571070180828767545 3619070678302635621575659)
    ·
      refine ⟨5428606017453953432363489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3619070678302635621575659 5428606017453953432363489)
      ·
        refine ⟨4071454513090465074272617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5428606017453953432363489 4071454513090465074272617)
        ·
          refine ⟨3053590884817848805704463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4071454513090465074272617 3053590884817848805704463)
          ·
            refine ⟨4580386327226773208556695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3053590884817848805704463 4580386327226773208556695)
            ·
              refine ⟨6870579490840159812835043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4580386327226773208556695 6870579490840159812835043)
              ·
                refine ⟨10305869236260239719252565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6870579490840159812835043 10305869236260239719252565)
                ·
                  refine ⟨120771905112424684209991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10305869236260239719252565 120771905112424684209991)
                  ·
                    rfl

theorem cell23_2116822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_2116822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116822 prefixEnd_2116822 := by exact prefixLift 2116822
  have htrace : WordTrace (prefixWord ++ tailWord_2116822) baseStart_2116822 baseEnd_2116822 := by
    simpa [prefixWord, tailWord_2116822, baseEnd_2116822] using wordTrace_append hprefix tailTrace_2116822
  have hstable : (prefixWord ++ tailWord_2116822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116822).length < 2 ^ (prefixWord ++ tailWord_2116822).sum := by decide
  have hdescent : baseEnd_2116822 < baseStart_2116822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116825 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 4, 3, 2]
def baseStart_2116825 : Nat := 118140960795 + 2116825 * 2 ^ 59
def prefixEnd_2116825 : Nat := 4983230072969 + 3 ^ 40 * 2116825 * 2
def baseEnd_2116825 : Nat := 1086948686453785646152405

theorem tailTrace_2116825 : CollatzResearch.WordTrace tailWord_2116825 prefixEnd_2116825 1086948686453785646152405 := by
  unfold tailWord_2116825
  simp only [CollatzResearch.WordTrace]
  refine ⟨77206950556112024772639929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51471300370741349848426619 77206950556112024772639929)
  ·
    refine ⟨57905212917084018579479947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77206950556112024772639929 57905212917084018579479947)
    ·
      refine ⟨86857819375626027869219921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57905212917084018579479947 86857819375626027869219921)
      ·
        refine ⟨65143364531719520901914941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86857819375626027869219921 65143364531719520901914941)
        ·
          refine ⟨24428761699394820338218103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65143364531719520901914941 24428761699394820338218103)
          ·
            refine ⟨36643142549092230507327155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24428761699394820338218103 36643142549092230507327155)
            ·
              refine ⟨54964713823638345760990733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36643142549092230507327155 54964713823638345760990733)
              ·
                refine ⟨20611767683864379660371525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54964713823638345760990733 20611767683864379660371525)
                ·
                  refine ⟨3864706440724571186319661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20611767683864379660371525 3864706440724571186319661)
                  ·
                    refine ⟨1449264915271714194869873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3864706440724571186319661 1449264915271714194869873)
                    ·
                      refine ⟨1086948686453785646152405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1449264915271714194869873 1086948686453785646152405)
                      ·
                        rfl

theorem cell23_2116825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 3, 2].length) (baseStart_2116825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116825 prefixEnd_2116825 := by exact prefixLift 2116825
  have htrace : WordTrace (prefixWord ++ tailWord_2116825) baseStart_2116825 baseEnd_2116825 := by
    simpa [prefixWord, tailWord_2116825, baseEnd_2116825] using wordTrace_append hprefix tailTrace_2116825
  have hstable : (prefixWord ++ tailWord_2116825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116825).length < 2 ^ (prefixWord ++ tailWord_2116825).sum := by decide
  have hdescent : baseEnd_2116825 < baseStart_2116825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116832 : List Nat := [2, 1, 1, 3, 1, 5, 2, 1, 3, 1, 3]
def baseStart_2116832 : Nat := 118140960795 + 2116832 * 2 ^ 59
def prefixEnd_2116832 : Nat := 4983230072969 + 3 ^ 40 * 2116832 * 2
def baseEnd_2116832 : Nat := 1086952280818367118764873

theorem tailTrace_2116832 : CollatzResearch.WordTrace tailWord_2116832 prefixEnd_2116832 1086952280818367118764873 := by
  unfold tailWord_2116832
  simp only [CollatzResearch.WordTrace]
  refine ⟨38603602933543332484072375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51471470578057776645429833 38603602933543332484072375)
  ·
    refine ⟨57905404400314998726108563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38603602933543332484072375 57905404400314998726108563)
    ·
      refine ⟨86858106600472498089162845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57905404400314998726108563 86858106600472498089162845)
      ·
        refine ⟨32571789975177186783436067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86858106600472498089162845 32571789975177186783436067)
        ·
          refine ⟨48857684962765780175154101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32571789975177186783436067 48857684962765780175154101)
          ·
            refine ⟨4580407965259291891420697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48857684962765780175154101 4580407965259291891420697)
            ·
              refine ⟨3435305973944468918565523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4580407965259291891420697 3435305973944468918565523)
              ·
                refine ⟨5152958960916703377848285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3435305973944468918565523 5152958960916703377848285)
                ·
                  refine ⟨1932359610343763766693107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5152958960916703377848285 1932359610343763766693107)
                  ·
                    refine ⟨2898539415515645650039661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1932359610343763766693107 2898539415515645650039661)
                    ·
                      refine ⟨1086952280818367118764873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2898539415515645650039661 1086952280818367118764873)
                      ·
                        rfl

theorem cell23_2116832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_2116832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116832 prefixEnd_2116832 := by exact prefixLift 2116832
  have htrace : WordTrace (prefixWord ++ tailWord_2116832) baseStart_2116832 baseEnd_2116832 := by
    simpa [prefixWord, tailWord_2116832, baseEnd_2116832] using wordTrace_append hprefix tailTrace_2116832
  have hstable : (prefixWord ++ tailWord_2116832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116832).length < 2 ^ (prefixWord ++ tailWord_2116832).sum := by decide
  have hdescent : baseEnd_2116832 < baseStart_2116832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116858 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5]
def baseStart_2116858 : Nat := 118140960795 + 2116858 * 2 ^ 59
def prefixEnd_2116858 : Nat := 4983230072969 + 3 ^ 40 * 2116858 * 2
def baseEnd_2116858 : Nat := 1086965631315384017039753

theorem tailTrace_2116858 : CollatzResearch.WordTrace tailWord_2116858 prefixEnd_2116858 1086965631315384017039753 := by
  unfold tailWord_2116858
  simp only [CollatzResearch.WordTrace]
  refine ⟨19302038541248117852147807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51472102776661647605727485 19302038541248117852147807)
  ·
    refine ⟨28953057811872176778221711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19302038541248117852147807 28953057811872176778221711)
    ·
      refine ⟨43429586717808265167332567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28953057811872176778221711 43429586717808265167332567)
      ·
        refine ⟨65144380076712397750998851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43429586717808265167332567 65144380076712397750998851)
        ·
          refine ⟨97716570115068596626498277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65144380076712397750998851 97716570115068596626498277)
          ·
            refine ⟨18321856896575361867468427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97716570115068596626498277 18321856896575361867468427)
            ·
              refine ⟨27482785344863042801202641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18321856896575361867468427 27482785344863042801202641)
              ·
                refine ⟨20612089008647282100901981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27482785344863042801202641 20612089008647282100901981)
                ·
                  refine ⟨7729533378242730787838243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20612089008647282100901981 7729533378242730787838243)
                  ·
                    refine ⟨11594300067364096181757365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7729533378242730787838243 11594300067364096181757365)
                    ·
                      refine ⟨1086965631315384017039753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11594300067364096181757365 1086965631315384017039753)
                      ·
                        rfl

theorem cell23_2116858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_2116858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116858 prefixEnd_2116858 := by exact prefixLift 2116858
  have htrace : WordTrace (prefixWord ++ tailWord_2116858) baseStart_2116858 baseEnd_2116858 := by
    simpa [prefixWord, tailWord_2116858, baseEnd_2116858] using wordTrace_append hprefix tailTrace_2116858
  have hstable : (prefixWord ++ tailWord_2116858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116858).length < 2 ^ (prefixWord ++ tailWord_2116858).sum := by decide
  have hdescent : baseEnd_2116858 < baseStart_2116858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116865 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 4, 4]
def baseStart_2116865 : Nat := 118140960795 + 2116865 * 2 ^ 59
def prefixEnd_2116865 : Nat := 4983230072969 + 3 ^ 40 * 2116865 * 2
def baseEnd_2116865 : Nat := 362323075226655163217407

theorem tailTrace_2116865 : CollatzResearch.WordTrace tailWord_2116865 prefixEnd_2116865 362323075226655163217407 := by
  unfold tailWord_2116865
  simp only [CollatzResearch.WordTrace]
  refine ⟨77208409475967111604096049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51472272983978074402730699 77208409475967111604096049)
  ·
    refine ⟨57906307106975333703072037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77208409475967111604096049 57906307106975333703072037)
    ·
      refine ⟨10857432582557875069326007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57906307106975333703072037 10857432582557875069326007)
      ·
        refine ⟨16286148873836812603989011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10857432582557875069326007 16286148873836812603989011)
        ·
          refine ⟨24429223310755218905983517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16286148873836812603989011 24429223310755218905983517)
          ·
            refine ⟨9160958741533207089743819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24429223310755218905983517 9160958741533207089743819)
            ·
              refine ⟨13741438112299810634615729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9160958741533207089743819 13741438112299810634615729)
              ·
                refine ⟨10306078584224857975961797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13741438112299810634615729 10306078584224857975961797)
                ·
                  refine ⟨1932389734542160870492837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10306078584224857975961797 1932389734542160870492837)
                  ·
                    refine ⟨362323075226655163217407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1932389734542160870492837 362323075226655163217407)
                    ·
                      rfl

theorem cell23_2116865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_2116865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116865 prefixEnd_2116865 := by exact prefixLift 2116865
  have htrace : WordTrace (prefixWord ++ tailWord_2116865) baseStart_2116865 baseEnd_2116865 := by
    simpa [prefixWord, tailWord_2116865, baseEnd_2116865] using wordTrace_append hprefix tailTrace_2116865
  have hstable : (prefixWord ++ tailWord_2116865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116865).length < 2 ^ (prefixWord ++ tailWord_2116865).sum := by decide
  have hdescent : baseEnd_2116865 < baseStart_2116865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116875 : List Nat := [1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 5]
def baseStart_2116875 : Nat := 118140960795 + 2116875 * 2 ^ 59
def prefixEnd_2116875 : Nat := 4983230072969 + 3 ^ 40 * 2116875 * 2
def baseEnd_2116875 : Nat := 1086974360486510450527175

theorem tailTrace_2116875 : CollatzResearch.WordTrace tailWord_2116875 prefixEnd_2116875 1086974360486510450527175 := by
  unfold tailWord_2116875
  simp only [CollatzResearch.WordTrace]
  refine ⟨77208774205930883311960079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51472516137287255541306719 77208774205930883311960079)
  ·
    refine ⟨115813161308896324967940119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77208774205930883311960079 115813161308896324967940119)
    ·
      refine ⟨173719741963344487451910179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115813161308896324967940119 173719741963344487451910179)
      ·
        refine ⟨260579612945016731177865269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173719741963344487451910179 260579612945016731177865269)
        ·
          refine ⟨24429338713595318547924869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 260579612945016731177865269 24429338713595318547924869)
          ·
            refine ⟨4580501008799122227735913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24429338713595318547924869 4580501008799122227735913)
            ·
              refine ⟨3435375756599341670801935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4580501008799122227735913 3435375756599341670801935)
              ·
                refine ⟨5153063634899012506202903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3435375756599341670801935 5153063634899012506202903)
                ·
                  refine ⟨7729595452348518759304355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5153063634899012506202903 7729595452348518759304355)
                  ·
                    refine ⟨11594393178522778138956533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7729595452348518759304355 11594393178522778138956533)
                    ·
                      refine ⟨1086974360486510450527175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11594393178522778138956533 1086974360486510450527175)
                      ·
                        rfl

theorem cell23_2116875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 5].length) (baseStart_2116875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116875 prefixEnd_2116875 := by exact prefixLift 2116875
  have htrace : WordTrace (prefixWord ++ tailWord_2116875) baseStart_2116875 baseEnd_2116875 := by
    simpa [prefixWord, tailWord_2116875, baseEnd_2116875] using wordTrace_append hprefix tailTrace_2116875
  have hstable : (prefixWord ++ tailWord_2116875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116875).length < 2 ^ (prefixWord ++ tailWord_2116875).sum := by decide
  have hdescent : baseEnd_2116875 < baseStart_2116875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116878 : List Nat := [4, 1, 1, 2, 1, 3, 11]
def baseStart_2116878 : Nat := 118140960795 + 2116878 * 2 ^ 59
def prefixEnd_2116878 : Nat := 4983230072969 + 3 ^ 40 * 2116878 * 2
def baseEnd_2116878 : Nat := 13419455567018196775181

theorem tailTrace_2116878 : CollatzResearch.WordTrace tailWord_2116878 prefixEnd_2116878 13419455567018196775181 := by
  unfold tailWord_2116878
  simp only [CollatzResearch.WordTrace]
  refine ⟨9651110453115001853039911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51472589083280009882879525 9651110453115001853039911)
  ·
    refine ⟨14476665679672502779559867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9651110453115001853039911 14476665679672502779559867)
    ·
      refine ⟨21714998519508754169339801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14476665679672502779559867 21714998519508754169339801)
      ·
        refine ⟨16286248889631565627004851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21714998519508754169339801 16286248889631565627004851)
        ·
          refine ⟨24429373334447348440507277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16286248889631565627004851 24429373334447348440507277)
          ·
            refine ⟨9161015000417755665190229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24429373334447348440507277 9161015000417755665190229)
            ·
              refine ⟨13419455567018196775181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 9161015000417755665190229 13419455567018196775181)
              ·
                rfl

theorem cell23_2116878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 11].length) (baseStart_2116878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116878 prefixEnd_2116878 := by exact prefixLift 2116878
  have htrace : WordTrace (prefixWord ++ tailWord_2116878) baseStart_2116878 baseEnd_2116878 := by
    simpa [prefixWord, tailWord_2116878, baseEnd_2116878] using wordTrace_append hprefix tailTrace_2116878
  have hstable : (prefixWord ++ tailWord_2116878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116878).length < 2 ^ (prefixWord ++ tailWord_2116878).sum := by decide
  have hdescent : baseEnd_2116878 < baseStart_2116878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116895 : List Nat := [1, 1, 2, 4, 4, 1, 2, 8]
def baseStart_2116895 : Nat := 118140960795 + 2116895 * 2 ^ 59
def prefixEnd_2116895 : Nat := 4983230072969 + 3 ^ 40 * 2116895 * 2
def baseEnd_2116895 : Nat := 40258690003688902676929

theorem tailTrace_2116895 : CollatzResearch.WordTrace tailWord_2116895 prefixEnd_2116895 40258690003688902676929 := by
  unfold tailWord_2116895
  simp only [CollatzResearch.WordTrace]
  refine ⟨77209503665858426727688139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51473002443905617818458759 77209503665858426727688139)
  ·
    refine ⟨115814255498787640091532209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77209503665858426727688139 115814255498787640091532209)
    ·
      refine ⟨86860691624090730068649157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115814255498787640091532209 86860691624090730068649157)
      ·
        refine ⟨16286379679517011887871717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86860691624090730068649157 16286379679517011887871717)
        ·
          refine ⟨3053696189909439728975947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16286379679517011887871717 3053696189909439728975947)
          ·
            refine ⟨4580544284864159593463921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3053696189909439728975947 4580544284864159593463921)
            ·
              refine ⟨3435408213648119695097941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4580544284864159593463921 3435408213648119695097941)
              ·
                refine ⟨40258690003688902676929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3435408213648119695097941 40258690003688902676929)
                ·
                  rfl

theorem cell23_2116895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 8].length) (baseStart_2116895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116895 prefixEnd_2116895 := by exact prefixLift 2116895
  have htrace : WordTrace (prefixWord ++ tailWord_2116895) baseStart_2116895 baseEnd_2116895 := by
    simpa [prefixWord, tailWord_2116895, baseEnd_2116895] using wordTrace_append hprefix tailTrace_2116895
  have hstable : (prefixWord ++ tailWord_2116895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116895).length < 2 ^ (prefixWord ++ tailWord_2116895).sum := by decide
  have hdescent : baseEnd_2116895 < baseStart_2116895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116899 : List Nat := [1, 1, 1, 4, 2, 5, 2, 1, 2, 4]
def baseStart_2116899 : Nat := 118140960795 + 2116899 * 2 ^ 59
def prefixEnd_2116899 : Nat := 4983230072969 + 3 ^ 40 * 2116899 * 2
def baseEnd_2116899 : Nat := 362328894674072785542355

theorem tailTrace_2116899 : CollatzResearch.WordTrace tailWord_2116899 prefixEnd_2116899 362328894674072785542355 := by
  unfold tailWord_2116899
  simp only [CollatzResearch.WordTrace]
  refine ⟨77209649557843935410833751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51473099705229290273889167 77209649557843935410833751)
  ·
    refine ⟨115814474336765903116250627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77209649557843935410833751 115814474336765903116250627)
    ·
      refine ⟨173721711505148854674375941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115814474336765903116250627 173721711505148854674375941)
      ·
        refine ⟨32572820907215410251445489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173721711505148854674375941 32572820907215410251445489)
        ·
          refine ⟨24429615680411557688584117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32572820907215410251445489 24429615680411557688584117)
          ·
            refine ⟨2290276470038583533304761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24429615680411557688584117 2290276470038583533304761)
            ·
              refine ⟨1717707352528937649978571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2290276470038583533304761 1717707352528937649978571)
              ·
                refine ⟨2576561028793406474967857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1717707352528937649978571 2576561028793406474967857)
                ·
                  refine ⟨1932420771595054856225893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2576561028793406474967857 1932420771595054856225893)
                  ·
                    refine ⟨362328894674072785542355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1932420771595054856225893 362328894674072785542355)
                    ·
                      rfl

theorem cell23_2116899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 2, 4].length) (baseStart_2116899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116899 prefixEnd_2116899 := by exact prefixLift 2116899
  have htrace : WordTrace (prefixWord ++ tailWord_2116899) baseStart_2116899 baseEnd_2116899 := by
    simpa [prefixWord, tailWord_2116899, baseEnd_2116899] using wordTrace_append hprefix tailTrace_2116899
  have hstable : (prefixWord ++ tailWord_2116899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116899).length < 2 ^ (prefixWord ++ tailWord_2116899).sum := by decide
  have hdescent : baseEnd_2116899 < baseStart_2116899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116909 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_2116909 : Nat := 118140960795 + 2116909 * 2 ^ 59
def prefixEnd_2116909 : Nat := 4983230072969 + 3 ^ 40 * 2116909 * 2
def baseEnd_2116909 : Nat := 1086991818828763317502019

theorem tailTrace_2116909 : CollatzResearch.WordTrace tailWord_2116909 prefixEnd_2116909 1086991818828763317502019 := by
  unfold tailWord_2116909
  simp only [CollatzResearch.WordTrace]
  refine ⟨77210014287807707118697781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51473342858538471412465187 77210014287807707118697781)
  ·
    refine ⟨7238438839481972542377917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77210014287807707118697781 7238438839481972542377917)
    ·
      refine ⟨2714414564805739703391719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7238438839481972542377917 2714414564805739703391719)
      ·
        refine ⟨4071621847208609555087579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2714414564805739703391719 4071621847208609555087579)
        ·
          refine ⟨6107432770812914332631369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4071621847208609555087579 6107432770812914332631369)
          ·
            refine ⟨4580574578109685749473527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6107432770812914332631369 4580574578109685749473527)
            ·
              refine ⟨6870861867164528624210291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4580574578109685749473527 6870861867164528624210291)
              ·
                refine ⟨10306292800746792936315437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6870861867164528624210291 10306292800746792936315437)
                ·
                  refine ⟨3864859800280047351118289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10306292800746792936315437 3864859800280047351118289)
                  ·
                    refine ⟨2898644850210035513338717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3864859800280047351118289 2898644850210035513338717)
                    ·
                      refine ⟨1086991818828763317502019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2898644850210035513338717 1086991818828763317502019)
                      ·
                        rfl

theorem cell23_2116909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_2116909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116909 prefixEnd_2116909 := by exact prefixLift 2116909
  have htrace : WordTrace (prefixWord ++ tailWord_2116909) baseStart_2116909 baseEnd_2116909 := by
    simpa [prefixWord, tailWord_2116909, baseEnd_2116909] using wordTrace_append hprefix tailTrace_2116909
  have hstable : (prefixWord ++ tailWord_2116909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116909).length < 2 ^ (prefixWord ++ tailWord_2116909).sum := by decide
  have hdescent : baseEnd_2116909 < baseStart_2116909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116934 : List Nat := [6, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3]
def baseStart_2116934 : Nat := 118140960795 + 2116934 * 2 ^ 59
def prefixEnd_2116934 : Nat := 4983230072969 + 3 ^ 40 * 2116934 * 2
def baseEnd_2116934 : Nat := 1087004655845125719689405

theorem tailTrace_2116934 : CollatzResearch.WordTrace tailWord_2116934 prefixEnd_2116934 1087004655845125719689405 := by
  unfold tailWord_2116934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2412841441022410512136183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51473950741811424258905237 2412841441022410512136183)
  ·
    refine ⟨3619262161533615768204275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2412841441022410512136183 3619262161533615768204275)
    ·
      refine ⟨5428893242300423652306413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3619262161533615768204275 5428893242300423652306413)
      ·
        refine ⟨2035834965862658869614905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5428893242300423652306413 2035834965862658869614905)
        ·
          refine ⟨1526876224396994152211179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2035834965862658869614905 1526876224396994152211179)
          ·
            refine ⟨2290314336595491228316769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1526876224396994152211179 2290314336595491228316769)
            ·
              refine ⟨1717735752446618421237577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2290314336595491228316769 1717735752446618421237577)
              ·
                refine ⟨1288301814334963815928183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1717735752446618421237577 1288301814334963815928183)
                ·
                  refine ⟨1932452721502445723892275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1288301814334963815928183 1932452721502445723892275)
                  ·
                    refine ⟨2898679082253668585838413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1932452721502445723892275 2898679082253668585838413)
                    ·
                      refine ⟨1087004655845125719689405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2898679082253668585838413 1087004655845125719689405)
                      ·
                        rfl

theorem cell23_2116934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_2116934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116934 prefixEnd_2116934 := by exact prefixLift 2116934
  have htrace : WordTrace (prefixWord ++ tailWord_2116934) baseStart_2116934 baseEnd_2116934 := by
    simpa [prefixWord, tailWord_2116934, baseEnd_2116934] using wordTrace_append hprefix tailTrace_2116934
  have hstable : (prefixWord ++ tailWord_2116934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116934).length < 2 ^ (prefixWord ++ tailWord_2116934).sum := by decide
  have hdescent : baseEnd_2116934 < baseStart_2116934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116938 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 3, 8]
def baseStart_2116938 : Nat := 118140960795 + 2116938 * 2 ^ 59
def prefixEnd_2116938 : Nat := 4983230072969 + 3 ^ 40 * 2116938 * 2
def baseEnd_2116938 : Nat := 362335569922581234679795

theorem tailTrace_2116938 : CollatzResearch.WordTrace tailWord_2116938 prefixEnd_2116938 362335569922581234679795 := by
  unfold tailWord_2116938
  simp only [CollatzResearch.WordTrace]
  refine ⟨19302768001175661267875867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51474048003135096714335645 19302768001175661267875867)
  ·
    refine ⟨28954152001763491901813801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19302768001175661267875867 28954152001763491901813801)
    ·
      refine ⟨21715614001322618926360351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28954152001763491901813801 21715614001322618926360351)
      ·
        refine ⟨32573421001983928389540527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21715614001322618926360351 32573421001983928389540527)
        ·
          refine ⟨48860131502975892584310791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32573421001983928389540527 48860131502975892584310791)
          ·
            refine ⟨73290197254463838876466187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48860131502975892584310791 73290197254463838876466187)
            ·
              refine ⟨109935295881695758314699281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73290197254463838876466187 109935295881695758314699281)
              ·
                refine ⟨82451471911271818736024461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109935295881695758314699281 82451471911271818736024461)
                ·
                  refine ⟨30919301966726932026009173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82451471911271818736024461 30919301966726932026009173)
                  ·
                    refine ⟨362335569922581234679795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30919301966726932026009173 362335569922581234679795)
                    ·
                      rfl

theorem cell23_2116938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_2116938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116938 prefixEnd_2116938 := by exact prefixLift 2116938
  have htrace : WordTrace (prefixWord ++ tailWord_2116938) baseStart_2116938 baseEnd_2116938 := by
    simpa [prefixWord, tailWord_2116938, baseEnd_2116938] using wordTrace_append hprefix tailTrace_2116938
  have hstable : (prefixWord ++ tailWord_2116938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116938).length < 2 ^ (prefixWord ++ tailWord_2116938).sum := by decide
  have hdescent : baseEnd_2116938 < baseStart_2116938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116965 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 2, 4, 3]
def baseStart_2116965 : Nat := 118140960795 + 2116965 * 2 ^ 59
def prefixEnd_2116965 : Nat := 4983230072969 + 3 ^ 40 * 2116965 * 2
def baseEnd_2116965 : Nat := 1087020573745415098401761

theorem tailTrace_2116965 : CollatzResearch.WordTrace tailWord_2116965 prefixEnd_2116965 1087020573745415098401761 := by
  unfold tailWord_2116965
  simp only [CollatzResearch.WordTrace]
  refine ⟨77212056775604828682736349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51474704517069885788490899 77212056775604828682736349)
  ·
    refine ⟨28954521290851810756026131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77212056775604828682736349 28954521290851810756026131)
    ·
      refine ⟨43431781936277716134039197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28954521290851810756026131 43431781936277716134039197)
      ·
        refine ⟨16286918226104143550264699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43431781936277716134039197 16286918226104143550264699)
        ·
          refine ⟨24430377339156215325397049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16286918226104143550264699 24430377339156215325397049)
          ·
            refine ⟨18322783004367161494047787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24430377339156215325397049 18322783004367161494047787)
            ·
              refine ⟨27484174506550742241071681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18322783004367161494047787 27484174506550742241071681)
              ·
                refine ⟨20613130879913056680803761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27484174506550742241071681 20613130879913056680803761)
                ·
                  refine ⟨15459848159934792510602821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20613130879913056680803761 15459848159934792510602821)
                  ·
                    refine ⟨2898721529987773595738029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15459848159934792510602821 2898721529987773595738029)
                    ·
                      refine ⟨1087020573745415098401761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2898721529987773595738029 1087020573745415098401761)
                      ·
                        rfl

theorem cell23_2116965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_2116965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116965 prefixEnd_2116965 := by exact prefixLift 2116965
  have htrace : WordTrace (prefixWord ++ tailWord_2116965) baseStart_2116965 baseEnd_2116965 := by
    simpa [prefixWord, tailWord_2116965, baseEnd_2116965] using wordTrace_append hprefix tailTrace_2116965
  have hstable : (prefixWord ++ tailWord_2116965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116965).length < 2 ^ (prefixWord ++ tailWord_2116965).sum := by decide
  have hdescent : baseEnd_2116965 < baseStart_2116965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116990 : List Nat := [4, 2, 3, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2116990 : Nat := 118140960795 + 2116990 * 2 ^ 59
def prefixEnd_2116990 : Nat := 4983230072969 + 3 ^ 40 * 2116990 * 2
def baseEnd_2116990 : Nat := 1087033410761777500589147

theorem tailTrace_2116990 : CollatzResearch.WordTrace tailWord_2116990 prefixEnd_2116990 1087033410761777500589147 := by
  unfold tailWord_2116990
  simp only [CollatzResearch.WordTrace]
  refine ⟨9651621075064282244049553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51475312400342838634930949 9651621075064282244049553)
  ·
    refine ⟨7238715806298211683037165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9651621075064282244049553 7238715806298211683037165)
    ·
      refine ⟨2714518427361829381138937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7238715806298211683037165 2714518427361829381138937)
      ·
        refine ⟨2035888820521372035854203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2714518427361829381138937 2035888820521372035854203)
        ·
          refine ⟨3053833230782058053781305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2035888820521372035854203 3053833230782058053781305)
          ·
            refine ⟨2290374923086543540335979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3053833230782058053781305 2290374923086543540335979)
            ·
              refine ⟨3435562384629815310503969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2290374923086543540335979 3435562384629815310503969)
              ·
                refine ⟨2576671788472361482877977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3435562384629815310503969 2576671788472361482877977)
                ·
                  refine ⟨1932503841354271112158483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2576671788472361482877977 1932503841354271112158483)
                  ·
                    refine ⟨2898755762031406668237725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1932503841354271112158483 2898755762031406668237725)
                    ·
                      refine ⟨1087033410761777500589147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2898755762031406668237725 1087033410761777500589147)
                      ·
                        rfl

theorem cell23_2116990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2116990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116990 prefixEnd_2116990 := by exact prefixLift 2116990
  have htrace : WordTrace (prefixWord ++ tailWord_2116990) baseStart_2116990 baseEnd_2116990 := by
    simpa [prefixWord, tailWord_2116990, baseEnd_2116990] using wordTrace_append hprefix tailTrace_2116990
  have hstable : (prefixWord ++ tailWord_2116990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116990).length < 2 ^ (prefixWord ++ tailWord_2116990).sum := by decide
  have hdescent : baseEnd_2116990 < baseStart_2116990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116996 : List Nat := [2, 3, 2, 1, 1, 3, 3, 2, 2, 2, 2]
def baseStart_2116996 : Nat := 118140960795 + 2116996 * 2 ^ 59
def prefixEnd_2116996 : Nat := 4983230072969 + 3 ^ 40 * 2116996 * 2
def baseEnd_2116996 : Nat := 1087036491645704477114119

theorem tailTrace_2116996 : CollatzResearch.WordTrace tailWord_2116996 prefixEnd_2116996 1087036491645704477114119 := by
  unfold tailWord_2116996
  simp only [CollatzResearch.WordTrace]
  refine ⟨38606593719246260488557421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51475458292328347318076561 38606593719246260488557421)
  ·
    refine ⟨14477472644717347683209033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38606593719246260488557421 14477472644717347683209033)
    ·
      refine ⟨10858104483538010762406775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14477472644717347683209033 10858104483538010762406775)
      ·
        refine ⟨16287156725307016143610163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10858104483538010762406775 16287156725307016143610163)
        ·
          refine ⟨24430735087960524215415245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16287156725307016143610163 24430735087960524215415245)
          ·
            refine ⟨9161525657985196580780717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24430735087960524215415245 9161525657985196580780717)
            ·
              refine ⟨3435572121744448717792769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9161525657985196580780717 3435572121744448717792769)
              ·
                refine ⟨2576679091308336538344577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3435572121744448717792769 2576679091308336538344577)
                ·
                  refine ⟨1932509318481252403758433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2576679091308336538344577 1932509318481252403758433)
                  ·
                    refine ⟨1449381988860939302818825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1932509318481252403758433 1449381988860939302818825)
                    ·
                      refine ⟨1087036491645704477114119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1449381988860939302818825 1087036491645704477114119)
                      ·
                        rfl

theorem cell23_2116996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_2116996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2116996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2116996 prefixEnd_2116996 := by exact prefixLift 2116996
  have htrace : WordTrace (prefixWord ++ tailWord_2116996) baseStart_2116996 baseEnd_2116996 := by
    simpa [prefixWord, tailWord_2116996, baseEnd_2116996] using wordTrace_append hprefix tailTrace_2116996
  have hstable : (prefixWord ++ tailWord_2116996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116996).length < 2 ^ (prefixWord ++ tailWord_2116996).sum := by decide
  have hdescent : baseEnd_2116996 < baseStart_2116996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117089 : List Nat := [1, 2, 3, 1, 2, 4, 2, 1, 2, 2, 3]
def baseStart_2117089 : Nat := 118140960795 + 2117089 * 2 ^ 59
def prefixEnd_2117089 : Nat := 4983230072969 + 3 ^ 40 * 2117089 * 2
def baseEnd_2117089 : Nat := 1087084245346572613251191

theorem tailTrace_2117089 : CollatzResearch.WordTrace tailWord_2117089 prefixEnd_2117089 1087084245346572613251191 := by
  unfold tailWord_2117089
  simp only [CollatzResearch.WordTrace]
  refine ⟨77216579427155597860250321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51477719618103731906833547 77216579427155597860250321)
  ·
    refine ⟨57912434570366698395187741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77216579427155597860250321 57912434570366698395187741)
    ·
      refine ⟨21717162963887511898195403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57912434570366698395187741 21717162963887511898195403)
      ·
        refine ⟨32575744445831267847293105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21717162963887511898195403 32575744445831267847293105)
        ·
          refine ⟨24431808334373450885469829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32575744445831267847293105 24431808334373450885469829)
          ·
            refine ⟨4580964062695022041025593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24431808334373450885469829 4580964062695022041025593)
            ·
              refine ⟨3435723047021266530769195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4580964062695022041025593 3435723047021266530769195)
              ·
                refine ⟨5153584570531899796153793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3435723047021266530769195 5153584570531899796153793)
                ·
                  refine ⟨3865188427898924847115345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5153584570531899796153793 3865188427898924847115345)
                  ·
                    refine ⟨2898891320924193635336509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3865188427898924847115345 2898891320924193635336509)
                    ·
                      refine ⟨1087084245346572613251191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2898891320924193635336509 1087084245346572613251191)
                      ·
                        rfl

theorem cell23_2117089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_2117089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117089 prefixEnd_2117089 := by exact prefixLift 2117089
  have htrace : WordTrace (prefixWord ++ tailWord_2117089) baseStart_2117089 baseEnd_2117089 := by
    simpa [prefixWord, tailWord_2117089, baseEnd_2117089] using wordTrace_append hprefix tailTrace_2117089
  have hstable : (prefixWord ++ tailWord_2117089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117089).length < 2 ^ (prefixWord ++ tailWord_2117089).sum := by decide
  have hdescent : baseEnd_2117089 < baseStart_2117089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117109 : List Nat := [1, 3, 5, 1, 1, 1, 1, 4, 6]
def baseStart_2117109 : Nat := 118140960795 + 2117109 * 2 ^ 59
def prefixEnd_2117109 : Nat := 4983230072969 + 3 ^ 40 * 2117109 * 2
def baseEnd_2117109 : Nat := 120788279439962503889011

theorem tailTrace_2117109 : CollatzResearch.WordTrace tailWord_2117109 prefixEnd_2117109 120788279439962503889011 := by
  unfold tailWord_2117109
  simp only [CollatzResearch.WordTrace]
  refine ⟨77217308887083141275978381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51478205924722094183985587 77217308887083141275978381)
  ·
    refine ⟨28956490832656177978491893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77217308887083141275978381 28956490832656177978491893)
    ·
      refine ⟨2714671015561516685483615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28956490832656177978491893 2714671015561516685483615)
      ·
        refine ⟨4072006523342275028225423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2714671015561516685483615 4072006523342275028225423)
        ·
          refine ⟨6108009785013412542338135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4072006523342275028225423 6108009785013412542338135)
          ·
            refine ⟨9162014677520118813507203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6108009785013412542338135 9162014677520118813507203)
            ·
              refine ⟨13743022016280178220260805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9162014677520118813507203 13743022016280178220260805)
              ·
                refine ⟨2576816628052533416298901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13743022016280178220260805 2576816628052533416298901)
                ·
                  refine ⟨120788279439962503889011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2576816628052533416298901 120788279439962503889011)
                  ·
                    rfl

theorem cell23_2117109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 6].length) (baseStart_2117109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117109 prefixEnd_2117109 := by exact prefixLift 2117109
  have htrace : WordTrace (prefixWord ++ tailWord_2117109) baseStart_2117109 baseEnd_2117109 := by
    simpa [prefixWord, tailWord_2117109, baseEnd_2117109] using wordTrace_append hprefix tailTrace_2117109
  have hstable : (prefixWord ++ tailWord_2117109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117109).length < 2 ^ (prefixWord ++ tailWord_2117109).sum := by decide
  have hdescent : baseEnd_2117109 < baseStart_2117109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117140 : List Nat := [2, 4, 3, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_2117140 : Nat := 118140960795 + 2117140 * 2 ^ 59
def prefixEnd_2117140 : Nat := 4983230072969 + 3 ^ 40 * 2117140 * 2
def baseEnd_2117140 : Nat := 1087110432859951913713457

theorem tailTrace_2117140 : CollatzResearch.WordTrace tailWord_2117140 prefixEnd_2117140 1087110432859951913713457 := by
  unfold tailWord_2117140
  simp only [CollatzResearch.WordTrace]
  refine ⟨38609219774985416785178437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51478959699980555713571249 38609219774985416785178437)
  ·
    refine ⟨7239228707809765647220957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38609219774985416785178437 7239228707809765647220957)
    ·
      refine ⟨2714710765428662117707859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7239228707809765647220957 2714710765428662117707859)
      ·
        refine ⟨4072066148142993176561789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2714710765428662117707859 4072066148142993176561789)
        ·
          refine ⟨1527024805553622441210671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4072066148142993176561789 1527024805553622441210671)
          ·
            refine ⟨2290537208330433661816007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527024805553622441210671 2290537208330433661816007)
            ·
              refine ⟨3435805812495650492724011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2290537208330433661816007 3435805812495650492724011)
              ·
                refine ⟨5153708718743475739086017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3435805812495650492724011 5153708718743475739086017)
                ·
                  refine ⟨3865281539057606804314513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5153708718743475739086017 3865281539057606804314513)
                  ·
                    refine ⟨2898961154293205103235885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3865281539057606804314513 2898961154293205103235885)
                    ·
                      refine ⟨1087110432859951913713457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2898961154293205103235885 1087110432859951913713457)
                      ·
                        rfl

theorem cell23_2117140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_2117140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117140 prefixEnd_2117140 := by exact prefixLift 2117140
  have htrace : WordTrace (prefixWord ++ tailWord_2117140) baseStart_2117140 baseEnd_2117140 := by
    simpa [prefixWord, tailWord_2117140, baseEnd_2117140] using wordTrace_append hprefix tailTrace_2117140
  have hstable : (prefixWord ++ tailWord_2117140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117140).length < 2 ^ (prefixWord ++ tailWord_2117140).sum := by decide
  have hdescent : baseEnd_2117140 < baseStart_2117140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117145 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 2, 5, 5]
def baseStart_2117145 : Nat := 118140960795 + 2117145 * 2 ^ 59
def prefixEnd_2117145 : Nat := 4983230072969 + 3 ^ 40 * 2117145 * 2
def baseEnd_2117145 : Nat := 1087113000263224394150933

theorem tailTrace_2117145 : CollatzResearch.WordTrace tailWord_2117145 prefixEnd_2117145 1087113000263224394150933 := by
  unfold tailWord_2117145
  simp only [CollatzResearch.WordTrace]
  refine ⟨77218621914952719424288889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51479081276635146282859259 77218621914952719424288889)
  ·
    refine ⟨57913966436214539568216667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77218621914952719424288889 57913966436214539568216667)
    ·
      refine ⟨86870949654321809352325001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57913966436214539568216667 86870949654321809352325001)
      ·
        refine ⟨65153212240741357014243751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86870949654321809352325001 65153212240741357014243751)
        ·
          refine ⟨97729818361112035521365627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65153212240741357014243751 97729818361112035521365627)
          ·
            refine ⟨146594727541668053282048441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97729818361112035521365627 146594727541668053282048441)
            ·
              refine ⟨109946045656251039961536331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146594727541668053282048441 109946045656251039961536331)
              ·
                refine ⟨164919068484376559942304497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109946045656251039961536331 164919068484376559942304497)
                ·
                  refine ⟨123689301363282419956728373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164919068484376559942304497 123689301363282419956728373)
                  ·
                    refine ⟨11595872002807726870943285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 123689301363282419956728373 11595872002807726870943285)
                    ·
                      refine ⟨1087113000263224394150933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11595872002807726870943285 1087113000263224394150933)
                      ·
                        rfl

theorem cell23_2117145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_2117145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117145 prefixEnd_2117145 := by exact prefixLift 2117145
  have htrace : WordTrace (prefixWord ++ tailWord_2117145) baseStart_2117145 baseEnd_2117145 := by
    simpa [prefixWord, tailWord_2117145, baseEnd_2117145] using wordTrace_append hprefix tailTrace_2117145
  have hstable : (prefixWord ++ tailWord_2117145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117145).length < 2 ^ (prefixWord ++ tailWord_2117145).sum := by decide
  have hdescent : baseEnd_2117145 < baseStart_2117145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117153 : List Nat := [1, 2, 3, 2, 2, 3, 2, 3, 1, 1, 3]
def baseStart_2117153 : Nat := 118140960795 + 2117153 * 2 ^ 59
def prefixEnd_2117153 : Nat := 4983230072969 + 3 ^ 40 * 2117153 * 2
def baseEnd_2117153 : Nat := 1087117108108460362850897

theorem tailTrace_2117153 : CollatzResearch.WordTrace tailWord_2117153 prefixEnd_2117153 1087117108108460362850897 := by
  unfold tailWord_2117153
  simp only [CollatzResearch.WordTrace]
  refine ⟨77218913698923736790580113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51479275799282491193720075 77218913698923736790580113)
  ·
    refine ⟨57914185274192802592935085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77218913698923736790580113 57914185274192802592935085)
    ·
      refine ⟨21717819477822300972350657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57914185274192802592935085 21717819477822300972350657)
      ·
        refine ⟨16288364608366725729262993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21717819477822300972350657 16288364608366725729262993)
        ·
          refine ⟨12216273456275044296947245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16288364608366725729262993 12216273456275044296947245)
          ·
            refine ⟨4581102546103141611355217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12216273456275044296947245 4581102546103141611355217)
            ·
              refine ⟨3435826909577356208516413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4581102546103141611355217 3435826909577356208516413)
              ·
                refine ⟨1288435091091508578193655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3435826909577356208516413 1288435091091508578193655)
                ·
                  refine ⟨1932652636637262867290483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1288435091091508578193655 1932652636637262867290483)
                  ·
                    refine ⟨2898978954955894300935725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1932652636637262867290483 2898978954955894300935725)
                    ·
                      refine ⟨1087117108108460362850897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2898978954955894300935725 1087117108108460362850897)
                      ·
                        rfl

theorem cell23_2117153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_2117153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117153 prefixEnd_2117153 := by exact prefixLift 2117153
  have htrace : WordTrace (prefixWord ++ tailWord_2117153) baseStart_2117153 baseEnd_2117153 := by
    simpa [prefixWord, tailWord_2117153, baseEnd_2117153] using wordTrace_append hprefix tailTrace_2117153
  have hstable : (prefixWord ++ tailWord_2117153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117153).length < 2 ^ (prefixWord ++ tailWord_2117153).sum := by decide
  have hdescent : baseEnd_2117153 < baseStart_2117153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117176 : List Nat := [2, 1, 2, 1, 4, 2, 1, 3, 3, 2, 2]
def baseStart_2117176 : Nat := 118140960795 + 2117176 * 2 ^ 59
def prefixEnd_2117176 : Nat := 4983230072969 + 3 ^ 40 * 2117176 * 2
def baseEnd_2117176 : Nat := 1087128918163513772863291

theorem tailTrace_2117176 : CollatzResearch.WordTrace tailWord_2117176 prefixEnd_2117176 1087128918163513772863291 := by
  unfold tailWord_2117176
  simp only [CollatzResearch.WordTrace]
  refine ⟨38609876288920205859333691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51479835051893607812444921 38609876288920205859333691)
  ·
    refine ⟨57914814433380308789000537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38609876288920205859333691 57914814433380308789000537)
    ·
      refine ⟨43436110825035231591750403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57914814433380308789000537 43436110825035231591750403)
      ·
        refine ⟨65154166237552847387625605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43436110825035231591750403 65154166237552847387625605)
        ·
          refine ⟨12216406169541158885179801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65154166237552847387625605 12216406169541158885179801)
          ·
            refine ⟨9162304627155869163884851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12216406169541158885179801 9162304627155869163884851)
            ·
              refine ⟨13743456940733803745827277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9162304627155869163884851 13743456940733803745827277)
              ·
                refine ⟨5153796352775176404685229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13743456940733803745827277 5153796352775176404685229)
                ·
                  refine ⟨1932673632290691151756961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5153796352775176404685229 1932673632290691151756961)
                  ·
                    refine ⟨1449505224218018363817721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1932673632290691151756961 1449505224218018363817721)
                    ·
                      refine ⟨1087128918163513772863291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1449505224218018363817721 1087128918163513772863291)
                      ·
                        rfl

theorem cell23_2117176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 3, 2, 2].length) (baseStart_2117176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117176 prefixEnd_2117176 := by exact prefixLift 2117176
  have htrace : WordTrace (prefixWord ++ tailWord_2117176) baseStart_2117176 baseEnd_2117176 := by
    simpa [prefixWord, tailWord_2117176, baseEnd_2117176] using wordTrace_append hprefix tailTrace_2117176
  have hstable : (prefixWord ++ tailWord_2117176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117176).length < 2 ^ (prefixWord ++ tailWord_2117176).sum := by decide
  have hdescent : baseEnd_2117176 < baseStart_2117176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117196 : List Nat := [2, 2, 1, 3, 1, 4, 2, 2, 1, 2, 3]
def baseStart_2117196 : Nat := 118140960795 + 2117196 * 2 ^ 59
def prefixEnd_2117196 : Nat := 4983230072969 + 3 ^ 40 * 2117196 * 2
def baseEnd_2117196 : Nat := 1087139187776603694613199

theorem tailTrace_2117196 : CollatzResearch.WordTrace tailWord_2117196 prefixEnd_2117196 1087139187776603694613199 := by
  unfold tailWord_2117196
  simp only [CollatzResearch.WordTrace]
  refine ⟨38610241018883977567197721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51480321358511970089596961 38610241018883977567197721)
  ·
    refine ⟨28957680764162983175398291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38610241018883977567197721 28957680764162983175398291)
    ·
      refine ⟨43436521146244474763097437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28957680764162983175398291 43436521146244474763097437)
      ·
        refine ⟨16288695429841678036161539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43436521146244474763097437 16288695429841678036161539)
        ·
          refine ⟨24433043144762517054242309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16288695429841678036161539 24433043144762517054242309)
          ·
            refine ⟨4581195589642971947670433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24433043144762517054242309 4581195589642971947670433)
            ·
              refine ⟨3435896692232228960752825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4581195589642971947670433 3435896692232228960752825)
              ·
                refine ⟨2576922519174171720564619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3435896692232228960752825 2576922519174171720564619)
                ·
                  refine ⟨3865383778761257580846929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2576922519174171720564619 3865383778761257580846929)
                  ·
                    refine ⟨2899037834070943185635197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3865383778761257580846929 2899037834070943185635197)
                    ·
                      refine ⟨1087139187776603694613199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2899037834070943185635197 1087139187776603694613199)
                      ·
                        rfl

theorem cell23_2117196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_2117196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117196 prefixEnd_2117196 := by exact prefixLift 2117196
  have htrace : WordTrace (prefixWord ++ tailWord_2117196) baseStart_2117196 baseEnd_2117196 := by
    simpa [prefixWord, tailWord_2117196, baseEnd_2117196] using wordTrace_append hprefix tailTrace_2117196
  have hstable : (prefixWord ++ tailWord_2117196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117196).length < 2 ^ (prefixWord ++ tailWord_2117196).sum := by decide
  have hdescent : baseEnd_2117196 < baseStart_2117196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117213 : List Nat := [1, 4, 4, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2117213 : Nat := 118140960795 + 2117213 * 2 ^ 59
def prefixEnd_2117213 : Nat := 4983230072969 + 3 ^ 40 * 2117213 * 2
def baseEnd_2117213 : Nat := 1087147916947730128100621

theorem tailTrace_2117213 : CollatzResearch.WordTrace tailWord_2117213 prefixEnd_2117213 1087147916947730128100621 := by
  unfold tailWord_2117213
  simp only [CollatzResearch.WordTrace]
  refine ⟨77221102078706367037764293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51480734719137578025176195 77221102078706367037764293)
  ·
    refine ⟨14478956639757443819580805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77221102078706367037764293 14478956639757443819580805)
    ·
      refine ⟨2714804369954520716171401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14478956639757443819580805 2714804369954520716171401)
      ·
        refine ⟨2036103277465890537128551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2714804369954520716171401 2036103277465890537128551)
        ·
          refine ⟨3054154916198835805692827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2036103277465890537128551 3054154916198835805692827)
          ·
            refine ⟨4581232374298253708539241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3054154916198835805692827 4581232374298253708539241)
            ·
              refine ⟨3435924280723690281404431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4581232374298253708539241 3435924280723690281404431)
              ·
                refine ⟨5153886421085535422106647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3435924280723690281404431 5153886421085535422106647)
                ·
                  refine ⟨7730829631628303133159971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5153886421085535422106647 7730829631628303133159971)
                  ·
                    refine ⟨11596244447442454699739957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7730829631628303133159971 11596244447442454699739957)
                    ·
                      refine ⟨1087147916947730128100621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11596244447442454699739957 1087147916947730128100621)
                      ·
                        rfl

theorem cell23_2117213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2117213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117213 prefixEnd_2117213 := by exact prefixLift 2117213
  have htrace : WordTrace (prefixWord ++ tailWord_2117213) baseStart_2117213 baseEnd_2117213 := by
    simpa [prefixWord, tailWord_2117213, baseEnd_2117213] using wordTrace_append hprefix tailTrace_2117213
  have hstable : (prefixWord ++ tailWord_2117213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117213).length < 2 ^ (prefixWord ++ tailWord_2117213).sum := by decide
  have hdescent : baseEnd_2117213 < baseStart_2117213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117226 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 4, 1, 3]
def baseStart_2117226 : Nat := 118140960795 + 2117226 * 2 ^ 59
def prefixEnd_2117226 : Nat := 4983230072969 + 3 ^ 40 * 2117226 * 2
def baseEnd_2117226 : Nat := 1087154592196238577238061

theorem tailTrace_2117226 : CollatzResearch.WordTrace tailWord_2117226 prefixEnd_2117226 1087154592196238577238061 := by
  unfold tailWord_2117226
  simp only [CollatzResearch.WordTrace]
  refine ⟨19305394056914817564496883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51481050818439513505325021 19305394056914817564496883)
  ·
    refine ⟨28958091085372226346745325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19305394056914817564496883 28958091085372226346745325)
    ·
      refine ⟨10859284157014584880029497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28958091085372226346745325 10859284157014584880029497)
      ·
        refine ⟨8144463117760938660022123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10859284157014584880029497 8144463117760938660022123)
        ·
          refine ⟨12216694676641407990033185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8144463117760938660022123 12216694676641407990033185)
          ·
            refine ⟨9162521007481055992524889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12216694676641407990033185 9162521007481055992524889)
            ·
              refine ⟨6871890755610791994393667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9162521007481055992524889 6871890755610791994393667)
              ·
                refine ⟨10307836133416187991590501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6871890755610791994393667 10307836133416187991590501)
                ·
                  refine ⟨1932719275015535248423219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10307836133416187991590501 1932719275015535248423219)
                  ·
                    refine ⟨2899078912523302872634829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1932719275015535248423219 2899078912523302872634829)
                    ·
                      refine ⟨1087154592196238577238061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2899078912523302872634829 1087154592196238577238061)
                      ·
                        rfl

theorem cell23_2117226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_2117226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117226 prefixEnd_2117226 := by exact prefixLift 2117226
  have htrace : WordTrace (prefixWord ++ tailWord_2117226) baseStart_2117226 baseEnd_2117226 := by
    simpa [prefixWord, tailWord_2117226, baseEnd_2117226] using wordTrace_append hprefix tailTrace_2117226
  have hstable : (prefixWord ++ tailWord_2117226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117226).length < 2 ^ (prefixWord ++ tailWord_2117226).sum := by decide
  have hdescent : baseEnd_2117226 < baseStart_2117226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117283 : List Nat := [1, 1, 1, 4, 1, 1, 6, 2, 2, 2, 2]
def baseStart_2117283 : Nat := 118140960795 + 2117283 * 2 ^ 59
def prefixEnd_2117283 : Nat := 4983230072969 + 3 ^ 40 * 2117283 * 2
def baseEnd_2117283 : Nat := 1087183860593544854225299

theorem tailTrace_2117283 : CollatzResearch.WordTrace tailWord_2117283 prefixEnd_2117283 1087183860593544854225299 := by
  unfold tailWord_2117283
  simp only [CollatzResearch.WordTrace]
  refine ⟨77223655188452768992812503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51482436792301845995208335 77223655188452768992812503)
  ·
    refine ⟨115835482782679153489218755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77223655188452768992812503 115835482782679153489218755)
    ·
      refine ⟨173753224174018730233828133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115835482782679153489218755 173753224174018730233828133)
      ·
        refine ⟨32578729532628511918842775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173753224174018730233828133 32578729532628511918842775)
        ·
          refine ⟨48868094298942767878264163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32578729532628511918842775 48868094298942767878264163)
          ·
            refine ⟨73302141448414151817396245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48868094298942767878264163 73302141448414151817396245)
            ·
              refine ⟨3436037880394413366440449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73302141448414151817396245 3436037880394413366440449)
              ·
                refine ⟨2577028410295810024830337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3436037880394413366440449 2577028410295810024830337)
                ·
                  refine ⟨1932771307721857518622753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2577028410295810024830337 1932771307721857518622753)
                  ·
                    refine ⟨1449578480791393138967065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1932771307721857518622753 1449578480791393138967065)
                    ·
                      refine ⟨1087183860593544854225299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1449578480791393138967065 1087183860593544854225299)
                      ·
                        rfl

theorem cell23_2117283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 2, 2].length) (baseStart_2117283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117283 prefixEnd_2117283 := by exact prefixLift 2117283
  have htrace : WordTrace (prefixWord ++ tailWord_2117283) baseStart_2117283 baseEnd_2117283 := by
    simpa [prefixWord, tailWord_2117283, baseEnd_2117283] using wordTrace_append hprefix tailTrace_2117283
  have hstable : (prefixWord ++ tailWord_2117283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117283).length < 2 ^ (prefixWord ++ tailWord_2117283).sum := by decide
  have hdescent : baseEnd_2117283 < baseStart_2117283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117299 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 3]
def baseStart_2117299 : Nat := 118140960795 + 2117299 * 2 ^ 59
def prefixEnd_2117299 : Nat := 4983230072969 + 3 ^ 40 * 2117299 * 2
def baseEnd_2117299 : Nat := 1087192076284016791625225

theorem tailTrace_2117299 : CollatzResearch.WordTrace tailWord_2117299 prefixEnd_2117299 1087192076284016791625225 := by
  unfold tailWord_2117299
  simp only [CollatzResearch.WordTrace]
  refine ⟨77224238756394803725394951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51482825837596535816929967 77224238756394803725394951)
  ·
    refine ⟨115836358134592205588092427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77224238756394803725394951 115836358134592205588092427)
    ·
      refine ⟨173754537201888308382138641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115836358134592205588092427 173754537201888308382138641)
      ·
        refine ⟨130315902901416231286603981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173754537201888308382138641 130315902901416231286603981)
        ·
          refine ⟨48868463588031086732476493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130315902901416231286603981 48868463588031086732476493)
          ·
            refine ⟨18325673845511657524678685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48868463588031086732476493 18325673845511657524678685)
            ·
              refine ⟨6872127692066871571754507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18325673845511657524678685 6872127692066871571754507)
              ·
                refine ⟨10308191538100307357631761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6872127692066871571754507 10308191538100307357631761)
                ·
                  refine ⟨7731143653575230518223821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10308191538100307357631761 7731143653575230518223821)
                  ·
                    refine ⟨2899178870090711444333933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7731143653575230518223821 2899178870090711444333933)
                    ·
                      refine ⟨1087192076284016791625225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2899178870090711444333933 1087192076284016791625225)
                      ·
                        rfl

theorem cell23_2117299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 3].length) (baseStart_2117299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117299 prefixEnd_2117299 := by exact prefixLift 2117299
  have htrace : WordTrace (prefixWord ++ tailWord_2117299) baseStart_2117299 baseEnd_2117299 := by
    simpa [prefixWord, tailWord_2117299, baseEnd_2117299] using wordTrace_append hprefix tailTrace_2117299
  have hstable : (prefixWord ++ tailWord_2117299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117299).length < 2 ^ (prefixWord ++ tailWord_2117299).sum := by decide
  have hdescent : baseEnd_2117299 < baseStart_2117299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117356 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 2, 4, 2]
def baseStart_2117356 : Nat := 118140960795 + 2117356 * 2 ^ 59
def prefixEnd_2117356 : Nat := 4983230072969 + 3 ^ 40 * 2117356 * 2
def baseEnd_2117356 : Nat := 1087221344681323068612463

theorem tailTrace_2117356 : CollatzResearch.WordTrace tailWord_2117356 prefixEnd_2117356 1087221344681323068612463 := by
  unfold tailWord_2117356
  simp only [CollatzResearch.WordTrace]
  refine ⟨38613158858594151230109961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51484211811458868306813281 38613158858594151230109961)
  ·
    refine ⟨28959869143945613422582471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38613158858594151230109961 28959869143945613422582471)
    ·
      refine ⟨43439803715918420133873707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28959869143945613422582471 43439803715918420133873707)
      ·
        refine ⟨65159705573877630200810561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43439803715918420133873707 65159705573877630200810561)
        ·
          refine ⟨48869779180408222650607921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65159705573877630200810561 48869779180408222650607921)
          ·
            refine ⟨36652334385306166987955941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48869779180408222650607921 36652334385306166987955941)
            ·
              refine ⟨6872312697244906310241739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36652334385306166987955941 6872312697244906310241739)
              ·
                refine ⟨10308469045867359465362609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6872312697244906310241739 10308469045867359465362609)
                ·
                  refine ⟨7731351784400519599021957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10308469045867359465362609 7731351784400519599021957)
                  ·
                    refine ⟨1449628459575097424816617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7731351784400519599021957 1449628459575097424816617)
                    ·
                      refine ⟨1087221344681323068612463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1449628459575097424816617 1087221344681323068612463)
                      ·
                        rfl

theorem cell23_2117356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 4, 2].length) (baseStart_2117356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117356 prefixEnd_2117356 := by exact prefixLift 2117356
  have htrace : WordTrace (prefixWord ++ tailWord_2117356) baseStart_2117356 baseEnd_2117356 := by
    simpa [prefixWord, tailWord_2117356, baseEnd_2117356] using wordTrace_append hprefix tailTrace_2117356
  have hstable : (prefixWord ++ tailWord_2117356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117356).length < 2 ^ (prefixWord ++ tailWord_2117356).sum := by decide
  have hdescent : baseEnd_2117356 < baseStart_2117356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117359 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 3]
def baseStart_2117359 : Nat := 118140960795 + 2117359 * 2 ^ 59
def prefixEnd_2117359 : Nat := 4983230072969 + 3 ^ 40 * 2117359 * 2
def baseEnd_2117359 : Nat := 1087222885123286556874949

theorem tailTrace_2117359 : CollatzResearch.WordTrace tailWord_2117359 prefixEnd_2117359 1087222885123286556874949 := by
  unfold tailWord_2117359
  simp only [CollatzResearch.WordTrace]
  refine ⟨77226427136177433972579131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51484284757451622648386087 77226427136177433972579131)
  ·
    refine ⟨115839640704266150958868697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77226427136177433972579131 115839640704266150958868697)
    ·
      refine ⟨86879730528199613219151523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115839640704266150958868697 86879730528199613219151523)
      ·
        refine ⟨130319595792299419828727285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86879730528199613219151523 130319595792299419828727285)
        ·
          refine ⟨12217462105528070608943183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130319595792299419828727285 12217462105528070608943183)
          ·
            refine ⟨18326193158292105913414775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12217462105528070608943183 18326193158292105913414775)
            ·
              refine ⟨27489289737438158870122163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18326193158292105913414775 27489289737438158870122163)
              ·
                refine ⟨41233934606157238305183245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27489289737438158870122163 41233934606157238305183245)
                ·
                  refine ⟨15462725477308964364443717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41233934606157238305183245 15462725477308964364443717)
                  ·
                    refine ⟨2899261026995430818333197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15462725477308964364443717 2899261026995430818333197)
                    ·
                      refine ⟨1087222885123286556874949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2899261026995430818333197 1087222885123286556874949)
                      ·
                        rfl

theorem cell23_2117359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 3].length) (baseStart_2117359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117359 prefixEnd_2117359 := by exact prefixLift 2117359
  have htrace : WordTrace (prefixWord ++ tailWord_2117359) baseStart_2117359 baseEnd_2117359 := by
    simpa [prefixWord, tailWord_2117359, baseEnd_2117359] using wordTrace_append hprefix tailTrace_2117359
  have hstable : (prefixWord ++ tailWord_2117359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117359).length < 2 ^ (prefixWord ++ tailWord_2117359).sum := by decide
  have hdescent : baseEnd_2117359 < baseStart_2117359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117413 : List Nat := [1, 3, 1, 2, 3, 4, 2, 1, 6]
def baseStart_2117413 : Nat := 118140960795 + 2117413 * 2 ^ 59
def prefixEnd_2117413 : Nat := 4983230072969 + 3 ^ 40 * 2117413 * 2
def baseEnd_2117413 : Nat := 120805623675403260622189

theorem tailTrace_2117413 : CollatzResearch.WordTrace tailWord_2117413 prefixEnd_2117413 120805623675403260622189 := by
  unfold tailWord_2117413
  simp only [CollatzResearch.WordTrace]
  refine ⟨77228396677981801195044893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51485597785321200796696595 77228396677981801195044893)
  ·
    refine ⟨28960648754243175448141835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77228396677981801195044893 28960648754243175448141835)
    ·
      refine ⟨43440973131364763172212753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28960648754243175448141835 43440973131364763172212753)
      ·
        refine ⟨32580729848523572379159565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43440973131364763172212753 32580729848523572379159565)
        ·
          refine ⟨12217773693196339642184837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32580729848523572379159565 12217773693196339642184837)
          ·
            refine ⟨2290832567474313682909657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12217773693196339642184837 2290832567474313682909657)
            ·
              refine ⟨1718124425605735262182243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2290832567474313682909657 1718124425605735262182243)
              ·
                refine ⟨2577186638408602893273365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1718124425605735262182243 2577186638408602893273365)
                ·
                  refine ⟨120805623675403260622189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2577186638408602893273365 120805623675403260622189)
                  ·
                    rfl

theorem cell23_2117413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 6].length) (baseStart_2117413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117413 prefixEnd_2117413 := by exact prefixLift 2117413
  have htrace : WordTrace (prefixWord ++ tailWord_2117413) baseStart_2117413 baseEnd_2117413 := by
    simpa [prefixWord, tailWord_2117413, baseEnd_2117413] using wordTrace_append hprefix tailTrace_2117413
  have hstable : (prefixWord ++ tailWord_2117413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117413).length < 2 ^ (prefixWord ++ tailWord_2117413).sum := by decide
  have hdescent : baseEnd_2117413 < baseStart_2117413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117426 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 3, 5]
def baseStart_2117426 : Nat := 118140960795 + 2117426 * 2 ^ 59
def prefixEnd_2117426 : Nat := 4983230072969 + 3 ^ 40 * 2117426 * 2
def baseEnd_2117426 : Nat := 362419096109045931579047

theorem tailTrace_2117426 : CollatzResearch.WordTrace tailWord_2117426 prefixEnd_2117426 362419096109045931579047 := by
  unfold tailWord_2117426
  simp only [CollatzResearch.WordTrace]
  refine ⟨19307217706733676103817033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51485913884623136276845421 19307217706733676103817033)
  ·
    refine ⟨14480413280050257077862775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19307217706733676103817033 14480413280050257077862775)
    ·
      refine ⟨21720619920075385616794163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14480413280050257077862775 21720619920075385616794163)
      ·
        refine ⟨32580929880113078425191245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21720619920075385616794163 32580929880113078425191245)
        ·
          refine ⟨12217848705042404409446717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32580929880113078425191245 12217848705042404409446717)
          ·
            refine ⟨4581693264390901653542519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12217848705042404409446717 4581693264390901653542519)
            ·
              refine ⟨6872539896586352480313779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4581693264390901653542519 6872539896586352480313779)
              ·
                refine ⟨10308809844879528720470669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6872539896586352480313779 10308809844879528720470669)
                ·
                  refine ⟨3865803691829823270176501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10308809844879528720470669 3865803691829823270176501)
                  ·
                    refine ⟨362419096109045931579047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3865803691829823270176501 362419096109045931579047)
                    ·
                      rfl

theorem cell23_2117426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_2117426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117426 prefixEnd_2117426 := by exact prefixLift 2117426
  have htrace : WordTrace (prefixWord ++ tailWord_2117426) baseStart_2117426 baseEnd_2117426 := by
    simpa [prefixWord, tailWord_2117426, baseEnd_2117426] using wordTrace_append hprefix tailTrace_2117426
  have hstable : (prefixWord ++ tailWord_2117426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117426).length < 2 ^ (prefixWord ++ tailWord_2117426).sum := by decide
  have hdescent : baseEnd_2117426 < baseStart_2117426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117443 : List Nat := [1, 1, 1, 3, 1, 6, 3, 1, 1, 5]
def baseStart_2117443 : Nat := 118140960795 + 2117443 * 2 ^ 59
def prefixEnd_2117443 : Nat := 4983230072969 + 3 ^ 40 * 2117443 * 2
def baseEnd_2117443 : Nat := 362422005832754742741521

theorem tailTrace_2117443 : CollatzResearch.WordTrace tailWord_2117443 prefixEnd_2117443 362422005832754742741521 := by
  unfold tailWord_2117443
  simp only [CollatzResearch.WordTrace]
  refine ⟨77229490867873116318636983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51486327245248744212424655 77229490867873116318636983)
  ·
    refine ⟨115844236301809674477955475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77229490867873116318636983 115844236301809674477955475)
    ·
      refine ⟨173766354452714511716933213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115844236301809674477955475 173766354452714511716933213)
      ·
        refine ⟨65162382919767941893849955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173766354452714511716933213 65162382919767941893849955)
        ·
          refine ⟨97743574379651912840774933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65162382919767941893849955 97743574379651912840774933)
          ·
            refine ⟨4581730049046183414411325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 97743574379651912840774933 4581730049046183414411325)
            ·
              refine ⟨1718148768392318780404247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4581730049046183414411325 1718148768392318780404247)
              ·
                refine ⟨2577223152588478170606371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1718148768392318780404247 2577223152588478170606371)
                ·
                  refine ⟨3865834728882717255909557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2577223152588478170606371 3865834728882717255909557)
                  ·
                    refine ⟨362422005832754742741521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3865834728882717255909557 362422005832754742741521)
                    ·
                      rfl

theorem cell23_2117443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 1, 5].length) (baseStart_2117443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117443 prefixEnd_2117443 := by exact prefixLift 2117443
  have htrace : WordTrace (prefixWord ++ tailWord_2117443) baseStart_2117443 baseEnd_2117443 := by
    simpa [prefixWord, tailWord_2117443, baseEnd_2117443] using wordTrace_append hprefix tailTrace_2117443
  have hstable : (prefixWord ++ tailWord_2117443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117443).length < 2 ^ (prefixWord ++ tailWord_2117443).sum := by decide
  have hdescent : baseEnd_2117443 < baseStart_2117443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117457 : List Nat := [1, 2, 2, 1, 5, 1, 4, 2, 1, 1, 3]
def baseStart_2117457 : Nat := 118140960795 + 2117457 * 2 ^ 59
def prefixEnd_2117457 : Nat := 4983230072969 + 3 ^ 40 * 2117457 * 2
def baseEnd_2117457 : Nat := 1087273206227427173449499

theorem tailTrace_2117457 : CollatzResearch.WordTrace tailWord_2117457 prefixEnd_2117457 1087273206227427173449499 := by
  unfold tailWord_2117457
  simp only [CollatzResearch.WordTrace]
  refine ⟨77230001489822396709646625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51486667659881597806431083 77230001489822396709646625)
  ·
    refine ⟨57922501117366797532234969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77230001489822396709646625 57922501117366797532234969)
    ·
      refine ⟨43441875838025098149176227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57922501117366797532234969 43441875838025098149176227)
      ·
        refine ⟨65162813757037647223764341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43441875838025098149176227 65162813757037647223764341)
        ·
          refine ⟨6109013789722279427227907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65162813757037647223764341 6109013789722279427227907)
          ·
            refine ⟨9163520684583419140841861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6109013789722279427227907 9163520684583419140841861)
            ·
              refine ⟨1718160128359391088907849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9163520684583419140841861 1718160128359391088907849)
              ·
                refine ⟨1288620096269543316680887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1718160128359391088907849 1288620096269543316680887)
                ·
                  refine ⟨1932930144404314975021331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1288620096269543316680887 1932930144404314975021331)
                  ·
                    refine ⟨2899395216606472462531997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1932930144404314975021331 2899395216606472462531997)
                    ·
                      refine ⟨1087273206227427173449499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2899395216606472462531997 1087273206227427173449499)
                      ·
                        rfl

theorem cell23_2117457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 1, 1, 3].length) (baseStart_2117457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117457 prefixEnd_2117457 := by exact prefixLift 2117457
  have htrace : WordTrace (prefixWord ++ tailWord_2117457) baseStart_2117457 baseEnd_2117457 := by
    simpa [prefixWord, tailWord_2117457, baseEnd_2117457] using wordTrace_append hprefix tailTrace_2117457
  have hstable : (prefixWord ++ tailWord_2117457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117457).length < 2 ^ (prefixWord ++ tailWord_2117457).sum := by decide
  have hdescent : baseEnd_2117457 < baseStart_2117457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117466 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3]
def baseStart_2117466 : Nat := 118140960795 + 2117466 * 2 ^ 59
def prefixEnd_2117466 : Nat := 4983230072969 + 3 ^ 40 * 2117466 * 2
def baseEnd_2117466 : Nat := 1087277827553317638236957

theorem tailTrace_2117466 : CollatzResearch.WordTrace tailWord_2117466 prefixEnd_2117466 1087277827553317638236957 := by
  unfold tailWord_2117466
  simp only [CollatzResearch.WordTrace]
  refine ⟨19307582436697447811681063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51486886497859860831149501 19307582436697447811681063)
  ·
    refine ⟨28961373655046171717521595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19307582436697447811681063 28961373655046171717521595)
    ·
      refine ⟨43442060482569257576282393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28961373655046171717521595 43442060482569257576282393)
      ·
        refine ⟨32581545361926943182211795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43442060482569257576282393 32581545361926943182211795)
        ·
          refine ⟨48872318042890414773317693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32581545361926943182211795 48872318042890414773317693)
          ·
            refine ⟨18327119266083905539994135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48872318042890414773317693 18327119266083905539994135)
            ·
              refine ⟨27490678899125858309991203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18327119266083905539994135 27490678899125858309991203)
              ·
                refine ⟨41236018348688787464986805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27490678899125858309991203 41236018348688787464986805)
                ·
                  refine ⟨3865876720189573824842513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41236018348688787464986805 3865876720189573824842513)
                  ·
                    refine ⟨2899407540142180368631885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3865876720189573824842513 2899407540142180368631885)
                    ·
                      refine ⟨1087277827553317638236957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2899407540142180368631885 1087277827553317638236957)
                      ·
                        rfl

theorem cell23_2117466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_2117466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117466 prefixEnd_2117466 := by exact prefixLift 2117466
  have htrace : WordTrace (prefixWord ++ tailWord_2117466) baseStart_2117466 baseEnd_2117466 := by
    simpa [prefixWord, tailWord_2117466, baseEnd_2117466] using wordTrace_append hprefix tailTrace_2117466
  have hstable : (prefixWord ++ tailWord_2117466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117466).length < 2 ^ (prefixWord ++ tailWord_2117466).sum := by decide
  have hdescent : baseEnd_2117466 < baseStart_2117466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
