import V185TrunkScan23Chunk0830

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4917043 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 2, 4, 2]
def baseStart_4917043 : Nat := 118140960795 + 4917043 * 2 ^ 59
def prefixEnd_4917043 : Nat := 4983230072969 + 3 ^ 40 * 4917043 * 2
def baseEnd_4917043 : Nat := 2524806457825510780349437

theorem tailTrace_4917043 : CollatzResearch.WordTrace tailWord_4917043 prefixEnd_4917043 2524806457825510780349437 := by
  unfold tailWord_4917043
  simp only [CollatzResearch.WordTrace]
  refine ⟨179339291525400449932475783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119559527683600299954983855 179339291525400449932475783)
  ·
    refine ⟨269008937288100674898713675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179339291525400449932475783 269008937288100674898713675)
    ·
      refine ⟨403513405932151012348070513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269008937288100674898713675 403513405932151012348070513)
      ·
        refine ⟨302635054449113259261052885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 403513405932151012348070513 302635054449113259261052885)
        ·
          refine ⟨7093009088651092013930927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 302635054449113259261052885 7093009088651092013930927)
          ·
            refine ⟨10639513632976638020896391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7093009088651092013930927 10639513632976638020896391)
            ·
              refine ⟨15959270449464957031344587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10639513632976638020896391 15959270449464957031344587)
              ·
                refine ⟨23938905674197435547016881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15959270449464957031344587 23938905674197435547016881)
                ·
                  refine ⟨17954179255648076660262661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23938905674197435547016881 17954179255648076660262661)
                  ·
                    refine ⟨3366408610434014373799249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17954179255648076660262661 3366408610434014373799249)
                    ·
                      refine ⟨2524806457825510780349437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3366408610434014373799249 2524806457825510780349437)
                      ·
                        rfl

theorem cell23_4917043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 4, 2].length) (baseStart_4917043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917043 prefixEnd_4917043 := by exact prefixLift 4917043
  have htrace : WordTrace (prefixWord ++ tailWord_4917043) baseStart_4917043 baseEnd_4917043 := by
    simpa [prefixWord, tailWord_4917043, baseEnd_4917043] using wordTrace_append hprefix tailTrace_4917043
  have hstable : (prefixWord ++ tailWord_4917043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917043).length < 2 ^ (prefixWord ++ tailWord_4917043).sum := by decide
  have hdescent : baseEnd_4917043 < baseStart_4917043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917053 : List Nat := [1, 4, 1, 4, 1, 2, 1, 2, 3, 4]
def baseStart_4917053 : Nat := 118140960795 + 4917053 * 2 ^ 59
def prefixEnd_4917053 : Nat := 4983230072969 + 3 ^ 40 * 4917053 * 2
def baseEnd_4917053 : Nat := 841603864210685247074797

theorem tailTrace_4917053 : CollatzResearch.WordTrace tailWord_4917053 prefixEnd_4917053 841603864210685247074797 := by
  unfold tailWord_4917053
  simp only [CollatzResearch.WordTrace]
  refine ⟨179339656255364221640339813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119559770836909481093559875 179339656255364221640339813)
  ·
    refine ⟨33626185547880791557563715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179339656255364221640339813 33626185547880791557563715)
    ·
      refine ⟨50439278321821187336345573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33626185547880791557563715 50439278321821187336345573)
      ·
        refine ⟨9457364685341472625564795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50439278321821187336345573 9457364685341472625564795)
        ·
          refine ⟨14186047028012208938347193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9457364685341472625564795 14186047028012208938347193)
          ·
            refine ⟨10639535271009156703760395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14186047028012208938347193 10639535271009156703760395)
            ·
              refine ⟨15959302906513735055640593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10639535271009156703760395 15959302906513735055640593)
              ·
                refine ⟨11969477179885301291730445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15959302906513735055640593 11969477179885301291730445)
                ·
                  refine ⟨4488553942456987984398917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11969477179885301291730445 4488553942456987984398917)
                  ·
                    refine ⟨841603864210685247074797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4488553942456987984398917 841603864210685247074797)
                    ·
                      rfl

theorem cell23_4917053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_4917053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917053 prefixEnd_4917053 := by exact prefixLift 4917053
  have htrace : WordTrace (prefixWord ++ tailWord_4917053) baseStart_4917053 baseEnd_4917053 := by
    simpa [prefixWord, tailWord_4917053, baseEnd_4917053] using wordTrace_append hprefix tailTrace_4917053
  have hstable : (prefixWord ++ tailWord_4917053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917053).length < 2 ^ (prefixWord ++ tailWord_4917053).sum := by decide
  have hdescent : baseEnd_4917053 < baseStart_4917053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917119 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 5]
def baseStart_4917119 : Nat := 118140960795 + 4917119 * 2 ^ 59
def prefixEnd_4917119 : Nat := 4983230072969 + 3 ^ 40 * 4917119 * 2
def baseEnd_4917119 : Nat := 2524845482355252482999087

theorem tailTrace_4917119 : CollatzResearch.WordTrace tailWord_4917119 prefixEnd_4917119 2524845482355252482999087 := by
  unfold tailWord_4917119
  simp only [CollatzResearch.WordTrace]
  refine ⟨179342063473125114912242411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119561375648750076608161607 179342063473125114912242411)
  ·
    refine ⟨269013095209687672368363617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179342063473125114912242411 269013095209687672368363617)
    ·
      refine ⟨201759821407265754276272713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269013095209687672368363617 201759821407265754276272713)
      ·
        refine ⟨151319866055449315707204535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201759821407265754276272713 151319866055449315707204535)
        ·
          refine ⟨226979799083173973560806803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151319866055449315707204535 226979799083173973560806803)
          ·
            refine ⟨340469698624760960341210205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226979799083173973560806803 340469698624760960341210205)
            ·
              refine ⟨127676136984285360127953827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 340469698624760960341210205 127676136984285360127953827)
              ·
                refine ⟨191514205476428040191930741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127676136984285360127953827 191514205476428040191930741)
                ·
                  refine ⟨17954456763415128767993507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 191514205476428040191930741 17954456763415128767993507)
                  ·
                    refine ⟨26931685145122693151990261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17954456763415128767993507 26931685145122693151990261)
                    ·
                      refine ⟨2524845482355252482999087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26931685145122693151990261 2524845482355252482999087)
                      ·
                        rfl

theorem cell23_4917119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_4917119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917119 prefixEnd_4917119 := by exact prefixLift 4917119
  have htrace : WordTrace (prefixWord ++ tailWord_4917119) baseStart_4917119 baseEnd_4917119 := by
    simpa [prefixWord, tailWord_4917119, baseEnd_4917119] using wordTrace_append hprefix tailTrace_4917119
  have hstable : (prefixWord ++ tailWord_4917119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917119).length < 2 ^ (prefixWord ++ tailWord_4917119).sum := by decide
  have hdescent : baseEnd_4917119 < baseStart_4917119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917144 : List Nat := [2, 1, 2, 6, 2, 1, 1, 1, 3, 1, 3]
def baseStart_4917144 : Nat := 118140960795 + 4917144 * 2 ^ 59
def prefixEnd_4917144 : Nat := 4983230072969 + 3 ^ 40 * 4917144 * 2
def baseEnd_4917144 : Nat := 2524858319371614885186473

theorem tailTrace_4917144 : CollatzResearch.WordTrace tailWord_4917144 prefixEnd_4917144 2524858319371614885186473 := by
  unfold tailWord_4917144
  simp only [CollatzResearch.WordTrace]
  refine ⟨89671487649017272090951243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119561983532023029454601657 89671487649017272090951243)
  ·
    refine ⟨134507231473525908136426865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89671487649017272090951243 134507231473525908136426865)
    ·
      refine ⟨100880423605144431102320149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134507231473525908136426865 100880423605144431102320149)
      ·
        refine ⟨4728769856491145207921257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 100880423605144431102320149 4728769856491145207921257)
        ·
          refine ⟨3546577392368358905940943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4728769856491145207921257 3546577392368358905940943)
          ·
            refine ⟨5319866088552538358911415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3546577392368358905940943 5319866088552538358911415)
            ·
              refine ⟨7979799132828807538367123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5319866088552538358911415 7979799132828807538367123)
              ·
                refine ⟨11969698699243211307550685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7979799132828807538367123 11969698699243211307550685)
                ·
                  refine ⟨4488637012216204240331507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11969698699243211307550685 4488637012216204240331507)
                  ·
                    refine ⟨6732955518324306360497261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4488637012216204240331507 6732955518324306360497261)
                    ·
                      refine ⟨2524858319371614885186473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6732955518324306360497261 2524858319371614885186473)
                      ·
                        rfl

theorem cell23_4917144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_4917144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917144 prefixEnd_4917144 := by exact prefixLift 4917144
  have htrace : WordTrace (prefixWord ++ tailWord_4917144) baseStart_4917144 baseEnd_4917144 := by
    simpa [prefixWord, tailWord_4917144, baseEnd_4917144] using wordTrace_append hprefix tailTrace_4917144
  have hstable : (prefixWord ++ tailWord_4917144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917144).length < 2 ^ (prefixWord ++ tailWord_4917144).sum := by decide
  have hdescent : baseEnd_4917144 < baseStart_4917144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917146 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6]
def baseStart_4917146 : Nat := 118140960795 + 4917146 * 2 ^ 59
def prefixEnd_4917146 : Nat := 4983230072969 + 3 ^ 40 * 4917146 * 2
def baseEnd_4917146 : Nat := 2524859346332923877361463

theorem tailTrace_4917146 : CollatzResearch.WordTrace tailWord_4917146 prefixEnd_4917146 2524859346332923877361463 := by
  unfold tailWord_4917146
  simp only [CollatzResearch.WordTrace]
  refine ⟨44835762061006824630868823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119562032162684865682316861 44835762061006824630868823)
  ·
    refine ⟨67253643091510236946303235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44835762061006824630868823 67253643091510236946303235)
    ·
      refine ⟨100880464637265355419454853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67253643091510236946303235 100880464637265355419454853)
      ·
        refine ⟨18915087119487254141147785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100880464637265355419454853 18915087119487254141147785)
        ·
          refine ⟨14186315339615440605860839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18915087119487254141147785 14186315339615440605860839)
          ·
            refine ⟨21279473009423160908791259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14186315339615440605860839 21279473009423160908791259)
            ·
              refine ⟨31919209514134741363186889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21279473009423160908791259 31919209514134741363186889)
              ·
                refine ⟨23939407135601056022390167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31919209514134741363186889 23939407135601056022390167)
                ·
                  refine ⟨35909110703401584033585251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23939407135601056022390167 35909110703401584033585251)
                  ·
                    refine ⟨53863666055102376050377877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35909110703401584033585251 53863666055102376050377877)
                    ·
                      refine ⟨2524859346332923877361463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53863666055102376050377877 2524859346332923877361463)
                      ·
                        rfl

theorem cell23_4917146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_4917146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917146 prefixEnd_4917146 := by exact prefixLift 4917146
  have htrace : WordTrace (prefixWord ++ tailWord_4917146) baseStart_4917146 baseEnd_4917146 := by
    simpa [prefixWord, tailWord_4917146, baseEnd_4917146] using wordTrace_append hprefix tailTrace_4917146
  have hstable : (prefixWord ++ tailWord_4917146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917146).length < 2 ^ (prefixWord ++ tailWord_4917146).sum := by decide
  have hdescent : baseEnd_4917146 < baseStart_4917146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917156 : List Nat := [2, 3, 1, 2, 1, 4, 2, 8]
def baseStart_4917156 : Nat := 118140960795 + 4917156 * 2 ^ 59
def prefixEnd_4917156 : Nat := 4983230072969 + 3 ^ 40 * 4917156 * 2
def baseEnd_4917156 : Nat := 93513499301461808823571

theorem tailTrace_4917156 : CollatzResearch.WordTrace tailWord_4917156 prefixEnd_4917156 93513499301461808823571 := by
  unfold tailWord_4917156
  simp only [CollatzResearch.WordTrace]
  refine ⟨89671706486995535115669661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119562275315994046820892881 89671706486995535115669661)
  ·
    refine ⟨33626889932623325668376123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89671706486995535115669661 33626889932623325668376123)
    ·
      refine ⟨50440334898934988502564185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33626889932623325668376123 50440334898934988502564185)
      ·
        refine ⟨37830251174201241376923139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50440334898934988502564185 37830251174201241376923139)
        ·
          refine ⟨56745376761301862065384709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37830251174201241376923139 56745376761301862065384709)
          ·
            refine ⟨10639758142744099137259633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56745376761301862065384709 10639758142744099137259633)
            ·
              refine ⟨7979818607058074352944725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10639758142744099137259633 7979818607058074352944725)
              ·
                refine ⟨93513499301461808823571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7979818607058074352944725 93513499301461808823571)
                ·
                  rfl

theorem cell23_4917156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 8].length) (baseStart_4917156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917156 prefixEnd_4917156 := by exact prefixLift 4917156
  have htrace : WordTrace (prefixWord ++ tailWord_4917156) baseStart_4917156 baseEnd_4917156 := by
    simpa [prefixWord, tailWord_4917156, baseEnd_4917156] using wordTrace_append hprefix tailTrace_4917156
  have hstable : (prefixWord ++ tailWord_4917156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917156).length < 2 ^ (prefixWord ++ tailWord_4917156).sum := by decide
  have hdescent : baseEnd_4917156 < baseStart_4917156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917180 : List Nat := [2, 2, 2, 5, 1, 1, 1, 2, 1, 2, 4]
def baseStart_4917180 : Nat := 118140960795 + 4917180 * 2 ^ 59
def prefixEnd_4917180 : Nat := 4983230072969 + 3 ^ 40 * 4917180 * 2
def baseEnd_4917180 : Nat := 2524876804675176744336307

theorem tailTrace_4917180 : CollatzResearch.WordTrace tailWord_4917180 prefixEnd_4917180 2524876804675176744336307 := by
  unfold tailWord_4917180
  simp only [CollatzResearch.WordTrace]
  refine ⟨89672144162952061165106497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119562858883936081553475329 89672144162952061165106497)
  ·
    refine ⟨67254108122214045873829873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89672144162952061165106497 67254108122214045873829873)
    ·
      refine ⟨50440581091660534405372405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67254108122214045873829873 50440581091660534405372405)
      ·
        refine ⟨4728804477343175100503663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50440581091660534405372405 4728804477343175100503663)
        ·
          refine ⟨7093206716014762650755495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4728804477343175100503663 7093206716014762650755495)
          ·
            refine ⟨10639810074022143976133243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7093206716014762650755495 10639810074022143976133243)
            ·
              refine ⟨15959715111033215964199865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10639810074022143976133243 15959715111033215964199865)
              ·
                refine ⟨11969786333274911973149899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15959715111033215964199865 11969786333274911973149899)
                ·
                  refine ⟨17954679499912367959724849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11969786333274911973149899 17954679499912367959724849)
                  ·
                    refine ⟨13466009624934275969793637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17954679499912367959724849 13466009624934275969793637)
                    ·
                      refine ⟨2524876804675176744336307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13466009624934275969793637 2524876804675176744336307)
                      ·
                        rfl

theorem cell23_4917180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_4917180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917180 prefixEnd_4917180 := by exact prefixLift 4917180
  have htrace : WordTrace (prefixWord ++ tailWord_4917180) baseStart_4917180 baseEnd_4917180 := by
    simpa [prefixWord, tailWord_4917180, baseEnd_4917180] using wordTrace_append hprefix tailTrace_4917180
  have hstable : (prefixWord ++ tailWord_4917180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917180).length < 2 ^ (prefixWord ++ tailWord_4917180).sum := by decide
  have hdescent : baseEnd_4917180 < baseStart_4917180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917274 : List Nat := [3, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2]
def baseStart_4917274 : Nat := 118140960795 + 4917274 * 2 ^ 59
def prefixEnd_4917274 : Nat := 4983230072969 + 3 ^ 40 * 4917274 * 2
def baseEnd_4917274 : Nat := 2524925071856699376560875

theorem tailTrace_4917274 : CollatzResearch.WordTrace tailWord_4917274 prefixEnd_4917274 2524925071856699376560875 := by
  unfold tailWord_4917274
  simp only [CollatzResearch.WordTrace]
  refine ⟨44836929196890894096033719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119565144525042384256089917 44836929196890894096033719)
  ·
    refine ⟨67255393795336341144050579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44836929196890894096033719 67255393795336341144050579)
    ·
      refine ⟨100883090693004511716075869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67255393795336341144050579 100883090693004511716075869)
      ·
        refine ⟨37831159009876691893528451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100883090693004511716075869 37831159009876691893528451)
        ·
          refine ⟨56746738514815037840292677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37831159009876691893528451 56746738514815037840292677)
          ·
            refine ⟨10640013471527819595054877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56746738514815037840292677 10640013471527819595054877)
            ·
              refine ⟨3990005051822932348145579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10640013471527819595054877 3990005051822932348145579)
              ·
                refine ⟨5985007577734398522218369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3990005051822932348145579 5985007577734398522218369)
                ·
                  refine ⟨4488755683300798891663777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5985007577734398522218369 4488755683300798891663777)
                  ·
                    refine ⟨3366566762475599168747833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4488755683300798891663777 3366566762475599168747833)
                    ·
                      refine ⟨2524925071856699376560875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3366566762475599168747833 2524925071856699376560875)
                      ·
                        rfl

theorem cell23_4917274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_4917274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917274 prefixEnd_4917274 := by exact prefixLift 4917274
  have htrace : WordTrace (prefixWord ++ tailWord_4917274) baseStart_4917274 baseEnd_4917274 := by
    simpa [prefixWord, tailWord_4917274, baseEnd_4917274] using wordTrace_append hprefix tailTrace_4917274
  have hstable : (prefixWord ++ tailWord_4917274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917274).length < 2 ^ (prefixWord ++ tailWord_4917274).sum := by decide
  have hdescent : baseEnd_4917274 < baseStart_4917274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917357 : List Nat := [1, 5, 1, 1, 2, 1, 2, 5, 1, 4]
def baseStart_4917357 : Nat := 118140960795 + 4917357 * 2 ^ 59
def prefixEnd_4917357 : Nat := 4983230072969 + 3 ^ 40 * 4917357 * 2
def baseEnd_4917357 : Nat := 841655896917007517274331

theorem tailTrace_4917357 : CollatzResearch.WordTrace tailWord_4917357 prefixEnd_4917357 841655896917007517274331 := by
  unfold tailWord_4917357
  simp only [CollatzResearch.WordTrace]
  refine ⟨179350744046262881559406325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119567162697508587706270883 179350744046262881559406325)
  ·
    refine ⟨16814132254337145146194343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 179350744046262881559406325 16814132254337145146194343)
    ·
      refine ⟨25221198381505717719291515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16814132254337145146194343 25221198381505717719291515)
      ·
        refine ⟨37831797572258576578937273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25221198381505717719291515 37831797572258576578937273)
        ·
          refine ⟨28373848179193932434202955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37831797572258576578937273 28373848179193932434202955)
          ·
            refine ⟨42560772268790898651304433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28373848179193932434202955 42560772268790898651304433)
            ·
              refine ⟨31920579201593173988478325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42560772268790898651304433 31920579201593173988478325)
              ·
                refine ⟨2992554300149360061419843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31920579201593173988478325 2992554300149360061419843)
                ·
                  refine ⟨4488831450224040092129765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2992554300149360061419843 4488831450224040092129765)
                  ·
                    refine ⟨841655896917007517274331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4488831450224040092129765 841655896917007517274331)
                    ·
                      rfl

theorem cell23_4917357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_4917357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917357 prefixEnd_4917357 := by exact prefixLift 4917357
  have htrace : WordTrace (prefixWord ++ tailWord_4917357) baseStart_4917357 baseEnd_4917357 := by
    simpa [prefixWord, tailWord_4917357, baseEnd_4917357] using wordTrace_append hprefix tailTrace_4917357
  have hstable : (prefixWord ++ tailWord_4917357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917357).length < 2 ^ (prefixWord ++ tailWord_4917357).sum := by decide
  have hdescent : baseEnd_4917357 < baseStart_4917357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917383 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 3, 5]
def baseStart_4917383 : Nat := 118140960795 + 4917383 * 2 ^ 59
def prefixEnd_4917383 : Nat := 4983230072969 + 3 ^ 40 * 4917383 * 2
def baseEnd_4917383 : Nat := 841660347082679816699291

theorem tailTrace_4917383 : CollatzResearch.WordTrace tailWord_4917383 prefixEnd_4917383 841660347082679816699291 := by
  unfold tailWord_4917383
  simp only [CollatzResearch.WordTrace]
  refine ⟨179351692344168687999852803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119567794896112458666568535 179351692344168687999852803)
  ·
    refine ⟨269027538516253031999779205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179351692344168687999852803 269027538516253031999779205)
    ·
      refine ⟨50442663471797443499958601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 269027538516253031999779205 50442663471797443499958601)
      ·
        refine ⟨37831997603848082624968951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50442663471797443499958601 37831997603848082624968951)
        ·
          refine ⟨56747996405772123937453427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37831997603848082624968951 56747996405772123937453427)
          ·
            refine ⟨85121994608658185906180141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56747996405772123937453427 85121994608658185906180141)
            ·
              refine ⟨31920747978246819714817553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85121994608658185906180141 31920747978246819714817553)
              ·
                refine ⟨23940560983685114786113165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31920747978246819714817553 23940560983685114786113165)
                ·
                  refine ⟨8977710368881918044792437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23940560983685114786113165 8977710368881918044792437)
                  ·
                    refine ⟨841660347082679816699291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8977710368881918044792437 841660347082679816699291)
                    ·
                      rfl

theorem cell23_4917383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_4917383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917383 prefixEnd_4917383 := by exact prefixLift 4917383
  have htrace : WordTrace (prefixWord ++ tailWord_4917383) baseStart_4917383 baseEnd_4917383 := by
    simpa [prefixWord, tailWord_4917383, baseEnd_4917383] using wordTrace_append hprefix tailTrace_4917383
  have hstable : (prefixWord ++ tailWord_4917383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917383).length < 2 ^ (prefixWord ++ tailWord_4917383).sum := by decide
  have hdescent : baseEnd_4917383 < baseStart_4917383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917403 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 4]
def baseStart_4917403 : Nat := 118140960795 + 4917403 * 2 ^ 59
def prefixEnd_4917403 : Nat := 4983230072969 + 3 ^ 40 * 4917403 * 2
def baseEnd_4917403 : Nat := 2524991310861129371847781

theorem tailTrace_4917403 : CollatzResearch.WordTrace tailWord_4917403 prefixEnd_4917403 2524991310861129371847781 := by
  unfold tailWord_4917403
  simp only [CollatzResearch.WordTrace]
  refine ⟨179352421804096231415580863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119568281202730820943720575 179352421804096231415580863)
  ·
    refine ⟨269028632706144347123371295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179352421804096231415580863 269028632706144347123371295)
    ·
      refine ⟨403542949059216520685056943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269028632706144347123371295 403542949059216520685056943)
      ·
        refine ⟨605314423588824781027585415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403542949059216520685056943 605314423588824781027585415)
        ·
          refine ⟨907971635383237171541378123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605314423588824781027585415 907971635383237171541378123)
          ·
            refine ⟨1361957453074855757312067185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907971635383237171541378123 1361957453074855757312067185)
            ·
              refine ⟨1021468089806141817984050389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1361957453074855757312067185 1021468089806141817984050389)
              ·
                refine ⟨23940658354831448859001181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1021468089806141817984050389 23940658354831448859001181)
                ·
                  refine ⟨8977746883061793322125443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23940658354831448859001181 8977746883061793322125443)
                  ·
                    refine ⟨13466620324592689983188165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8977746883061793322125443 13466620324592689983188165)
                    ·
                      refine ⟨2524991310861129371847781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13466620324592689983188165 2524991310861129371847781)
                      ·
                        rfl

theorem cell23_4917403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 4].length) (baseStart_4917403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917403 prefixEnd_4917403 := by exact prefixLift 4917403
  have htrace : WordTrace (prefixWord ++ tailWord_4917403) baseStart_4917403 baseEnd_4917403 := by
    simpa [prefixWord, tailWord_4917403, baseEnd_4917403] using wordTrace_append hprefix tailTrace_4917403
  have hstable : (prefixWord ++ tailWord_4917403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917403).length < 2 ^ (prefixWord ++ tailWord_4917403).sum := by decide
  have hdescent : baseEnd_4917403 < baseStart_4917403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917407 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 1, 5, 2]
def baseStart_4917407 : Nat := 118140960795 + 4917407 * 2 ^ 59
def prefixEnd_4917407 : Nat := 4983230072969 + 3 ^ 40 * 4917407 * 2
def baseEnd_4917407 : Nat := 2524993364783747356197763

theorem tailTrace_4917407 : CollatzResearch.WordTrace tailWord_4917407 prefixEnd_4917407 2524993364783747356197763 := by
  unfold tailWord_4917407
  simp only [CollatzResearch.WordTrace]
  refine ⟨179352567696081740098726475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119568378464054493399150983 179352567696081740098726475)
  ·
    refine ⟨269028851544122610148089713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179352567696081740098726475 269028851544122610148089713)
    ·
      refine ⟨201771638658091957611067285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269028851544122610148089713 201771638658091957611067285)
      ·
        refine ⟨9458045562098060513018779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 201771638658091957611067285 9458045562098060513018779)
        ·
          refine ⟨14187068343147090769528169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9458045562098060513018779 14187068343147090769528169)
          ·
            refine ⟨10640301257360318077146127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14187068343147090769528169 10640301257360318077146127)
            ·
              refine ⟨15960451886040477115719191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10640301257360318077146127 15960451886040477115719191)
              ·
                refine ⟨23940677829060715673578787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15960451886040477115719191 23940677829060715673578787)
                ·
                  refine ⟨35911016743591073510368181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23940677829060715673578787 35911016743591073510368181)
                  ·
                    refine ⟨3366657819711663141597017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35911016743591073510368181 3366657819711663141597017)
                    ·
                      refine ⟨2524993364783747356197763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3366657819711663141597017 2524993364783747356197763)
                      ·
                        rfl

theorem cell23_4917407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_4917407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917407 prefixEnd_4917407 := by exact prefixLift 4917407
  have htrace : WordTrace (prefixWord ++ tailWord_4917407) baseStart_4917407 baseEnd_4917407 := by
    simpa [prefixWord, tailWord_4917407, baseEnd_4917407] using wordTrace_append hprefix tailTrace_4917407
  have hstable : (prefixWord ++ tailWord_4917407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917407).length < 2 ^ (prefixWord ++ tailWord_4917407).sum := by decide
  have hdescent : baseEnd_4917407 < baseStart_4917407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917413 : List Nat := [1, 3, 1, 2, 1, 3, 1, 4, 1, 6]
def baseStart_4917413 : Nat := 118140960795 + 4917413 * 2 ^ 59
def prefixEnd_4917413 : Nat := 4983230072969 + 3 ^ 40 * 4917413 * 2
def baseEnd_4917413 : Nat := 841665481889224777574245

theorem tailTrace_4917413 : CollatzResearch.WordTrace tailWord_4917413 prefixEnd_4917413 841665481889224777574245 := by
  unfold tailWord_4917413
  simp only [CollatzResearch.WordTrace]
  refine ⟨179352786534060003123444893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119568524356040002082296595 179352786534060003123444893)
  ·
    refine ⟨67257294950272501171291835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179352786534060003123444893 67257294950272501171291835)
    ·
      refine ⟨100885942425408751756937753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67257294950272501171291835 100885942425408751756937753)
      ·
        refine ⟨75664456819056563817703315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100885942425408751756937753 75664456819056563817703315)
        ·
          refine ⟨113496685228584845726554973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75664456819056563817703315 113496685228584845726554973)
          ·
            refine ⟨42561256960719317147458115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113496685228584845726554973 42561256960719317147458115)
            ·
              refine ⟨63841885441078975721187173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42561256960719317147458115 63841885441078975721187173)
              ·
                refine ⟨11970353520202307947722595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63841885441078975721187173 11970353520202307947722595)
                ·
                  refine ⟨17955530280303461921583893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11970353520202307947722595 17955530280303461921583893)
                  ·
                    refine ⟨841665481889224777574245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17955530280303461921583893 841665481889224777574245)
                    ·
                      rfl

theorem cell23_4917413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_4917413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917413 prefixEnd_4917413 := by exact prefixLift 4917413
  have htrace : WordTrace (prefixWord ++ tailWord_4917413) baseStart_4917413 baseEnd_4917413 := by
    simpa [prefixWord, tailWord_4917413, baseEnd_4917413] using wordTrace_append hprefix tailTrace_4917413
  have hstable : (prefixWord ++ tailWord_4917413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917413).length < 2 ^ (prefixWord ++ tailWord_4917413).sum := by decide
  have hdescent : baseEnd_4917413 < baseStart_4917413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917423 : List Nat := [1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 5]
def baseStart_4917423 : Nat := 118140960795 + 4917423 * 2 ^ 59
def prefixEnd_4917423 : Nat := 4983230072969 + 3 ^ 40 * 4917423 * 2
def baseEnd_4917423 : Nat := 2525001580474219293597689

theorem tailTrace_4917423 : CollatzResearch.WordTrace tailWord_4917423 prefixEnd_4917423 2525001580474219293597689 := by
  unfold tailWord_4917423
  simp only [CollatzResearch.WordTrace]
  refine ⟨179353151264023774831308923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119568767509349183220872615 179353151264023774831308923)
  ·
    refine ⟨269029726896035662246963385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179353151264023774831308923 269029726896035662246963385)
    ·
      refine ⟨201772295172026746685222539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269029726896035662246963385 201772295172026746685222539)
      ·
        refine ⟨302658442758040120027833809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201772295172026746685222539 302658442758040120027833809)
        ·
          refine ⟨226993832068530090020875357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302658442758040120027833809 226993832068530090020875357)
          ·
            refine ⟨85122687025698783757828259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 226993832068530090020875357 85122687025698783757828259)
            ·
              refine ⟨127684030538548175636742389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85122687025698783757828259 127684030538548175636742389)
              ·
                refine ⟨11970377862988891465944599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127684030538548175636742389 11970377862988891465944599)
                ·
                  refine ⟨17955566794483337198916899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11970377862988891465944599 17955566794483337198916899)
                  ·
                    refine ⟨26933350191725005798375349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17955566794483337198916899 26933350191725005798375349)
                    ·
                      refine ⟨2525001580474219293597689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26933350191725005798375349 2525001580474219293597689)
                      ·
                        rfl

theorem cell23_4917423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 5].length) (baseStart_4917423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917423 prefixEnd_4917423 := by exact prefixLift 4917423
  have htrace : WordTrace (prefixWord ++ tailWord_4917423) baseStart_4917423 baseEnd_4917423 := by
    simpa [prefixWord, tailWord_4917423, baseEnd_4917423] using wordTrace_append hprefix tailTrace_4917423
  have hstable : (prefixWord ++ tailWord_4917423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917423).length < 2 ^ (prefixWord ++ tailWord_4917423).sum := by decide
  have hdescent : baseEnd_4917423 < baseStart_4917423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917433 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 1, 1, 6]
def baseStart_4917433 : Nat := 118140960795 + 4917433 * 2 ^ 59
def prefixEnd_4917433 : Nat := 4983230072969 + 3 ^ 40 * 4917433 * 2
def baseEnd_4917433 : Nat := 2525006715280764254472643

theorem tailTrace_4917433 : CollatzResearch.WordTrace tailWord_4917433 prefixEnd_4917433 2525006715280764254472643 := by
  unfold tailWord_4917433
  simp only [CollatzResearch.WordTrace]
  refine ⟨179353515993987546539172953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119569010662658364359448635 179353515993987546539172953)
  ·
    refine ⟨134515136995490659904379715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179353515993987546539172953 134515136995490659904379715)
    ·
      refine ⟨201772705493235989856569573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134515136995490659904379715 201772705493235989856569573)
      ·
        refine ⟨37832382279981748098106795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201772705493235989856569573 37832382279981748098106795)
        ·
          refine ⟨56748573419972622147160193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37832382279981748098106795 56748573419972622147160193)
          ·
            refine ⟨42561430064979466610370145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56748573419972622147160193 42561430064979466610370145)
            ·
              refine ⟨31921072548734599957777609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42561430064979466610370145 31921072548734599957777609)
              ·
                refine ⟨23940804411550949968333207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31921072548734599957777609 23940804411550949968333207)
                ·
                  refine ⟨35911206617326424952499811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23940804411550949968333207 35911206617326424952499811)
                  ·
                    refine ⟨53866809925989637428749717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35911206617326424952499811 53866809925989637428749717)
                    ·
                      refine ⟨2525006715280764254472643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53866809925989637428749717 2525006715280764254472643)
                      ·
                        rfl

theorem cell23_4917433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_4917433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917433 prefixEnd_4917433 := by exact prefixLift 4917433
  have htrace : WordTrace (prefixWord ++ tailWord_4917433) baseStart_4917433 baseEnd_4917433 := by
    simpa [prefixWord, tailWord_4917433, baseEnd_4917433] using wordTrace_append hprefix tailTrace_4917433
  have hstable : (prefixWord ++ tailWord_4917433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917433).length < 2 ^ (prefixWord ++ tailWord_4917433).sum := by decide
  have hdescent : baseEnd_4917433 < baseStart_4917433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917440 : List Nat := [2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 5]
def baseStart_4917440 : Nat := 118140960795 + 4917440 * 2 ^ 59
def prefixEnd_4917440 : Nat := 4983230072969 + 3 ^ 40 * 4917440 * 2
def baseEnd_4917440 : Nat := 2525010309645345727085111

theorem tailTrace_4917440 : CollatzResearch.WordTrace tailWord_4917440 prefixEnd_4917440 2525010309645345727085111 := by
  unfold tailWord_4917440
  simp only [CollatzResearch.WordTrace]
  refine ⟨89676885652481093367338887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119569180869974791156451849 89676885652481093367338887)
  ·
    refine ⟨134515328478721640051008331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89676885652481093367338887 134515328478721640051008331)
    ·
      refine ⟨201772992718082460076512497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134515328478721640051008331 201772992718082460076512497)
      ·
        refine ⟨151329744538561845057384373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201772992718082460076512497 151329744538561845057384373)
        ·
          refine ⟨14187163550490172974129785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 151329744538561845057384373 14187163550490172974129785)
          ·
            refine ⟨10640372662867629730597339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14187163550490172974129785 10640372662867629730597339)
            ·
              refine ⟨15960558994301444595896009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10640372662867629730597339 15960558994301444595896009)
              ·
                refine ⟨11970419245726083446922007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15960558994301444595896009 11970419245726083446922007)
                ·
                  refine ⟨17955628868589125170383011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11970419245726083446922007 17955628868589125170383011)
                  ·
                    refine ⟨26933443302883687755574517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17955628868589125170383011 26933443302883687755574517)
                    ·
                      refine ⟨2525010309645345727085111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26933443302883687755574517 2525010309645345727085111)
                      ·
                        rfl

theorem cell23_4917440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_4917440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917440 prefixEnd_4917440 := by exact prefixLift 4917440
  have htrace : WordTrace (prefixWord ++ tailWord_4917440) baseStart_4917440 baseEnd_4917440 := by
    simpa [prefixWord, tailWord_4917440, baseEnd_4917440] using wordTrace_append hprefix tailTrace_4917440
  have hstable : (prefixWord ++ tailWord_4917440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917440).length < 2 ^ (prefixWord ++ tailWord_4917440).sum := by decide
  have hdescent : baseEnd_4917440 < baseStart_4917440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917454 : List Nat := [4, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2]
def baseStart_4917454 : Nat := 118140960795 + 4917454 * 2 ^ 59
def prefixEnd_4917454 : Nat := 4983230072969 + 3 ^ 40 * 4917454 * 2
def baseEnd_4917454 : Nat := 2525017498374508672310047

theorem tailTrace_4917454 : CollatzResearch.WordTrace tailWord_4917454 prefixEnd_4917454 2525017498374508672310047 := by
  unfold tailWord_4917454
  simp only [CollatzResearch.WordTrace]
  refine ⟨22419285240863933390710927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119569521284607644750458277 22419285240863933390710927)
  ·
    refine ⟨33628927861295900086066391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22419285240863933390710927 33628927861295900086066391)
    ·
      refine ⟨50443391791943850129099587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33628927861295900086066391 50443391791943850129099587)
      ·
        refine ⟨75665087687915775193649381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50443391791943850129099587 75665087687915775193649381)
        ·
          refine ⟨14187203941484207848809259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75665087687915775193649381 14187203941484207848809259)
          ·
            refine ⟨21280805912226311773213889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14187203941484207848809259 21280805912226311773213889)
            ·
              refine ⟨15960604434169733829910417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21280805912226311773213889 15960604434169733829910417)
              ·
                refine ⟨11970453325627300372432813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15960604434169733829910417 11970453325627300372432813)
                ·
                  refine ⟨4488919997110237639662305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11970453325627300372432813 4488919997110237639662305)
                  ·
                    refine ⟨3366689997832678229746729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4488919997110237639662305 3366689997832678229746729)
                    ·
                      refine ⟨2525017498374508672310047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3366689997832678229746729 2525017498374508672310047)
                      ·
                        rfl

theorem cell23_4917454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2].length) (baseStart_4917454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917454 prefixEnd_4917454 := by exact prefixLift 4917454
  have htrace : WordTrace (prefixWord ++ tailWord_4917454) baseStart_4917454 baseEnd_4917454 := by
    simpa [prefixWord, tailWord_4917454, baseEnd_4917454] using wordTrace_append hprefix tailTrace_4917454
  have hstable : (prefixWord ++ tailWord_4917454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917454).length < 2 ^ (prefixWord ++ tailWord_4917454).sum := by decide
  have hdescent : baseEnd_4917454 < baseStart_4917454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917483 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 5]
def baseStart_4917483 : Nat := 118140960795 + 4917483 * 2 ^ 59
def prefixEnd_4917483 : Nat := 4983230072969 + 3 ^ 40 * 4917483 * 2
def baseEnd_4917483 : Nat := 2525032389313489058847413

theorem tailTrace_4917483 : CollatzResearch.WordTrace tailWord_4917483 prefixEnd_4917483 2525032389313489058847413 := by
  unfold tailWord_4917483
  simp only [CollatzResearch.WordTrace]
  refine ⟨179355339643806405078493103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119570226429204270052328735 179355339643806405078493103)
  ·
    refine ⟨269033009465709607617739655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179355339643806405078493103 269033009465709607617739655)
    ·
      refine ⟨403549514198564411426609483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269033009465709607617739655 403549514198564411426609483)
      ·
        refine ⟨605324271297846617139914225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403549514198564411426609483 605324271297846617139914225)
        ·
          refine ⟨453993203473384962854935669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 605324271297846617139914225 453993203473384962854935669)
          ·
            refine ⟨42561862825629840267650219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 453993203473384962854935669 42561862825629840267650219)
            ·
              refine ⟨63842794238444760401475329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42561862825629840267650219 63842794238444760401475329)
              ·
                refine ⟨47882095678833570301106497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63842794238444760401475329 47882095678833570301106497)
                ·
                  refine ⟨35911571759125177725829873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47882095678833570301106497 35911571759125177725829873)
                  ·
                    refine ⟨26933678819343883294372405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35911571759125177725829873 26933678819343883294372405)
                    ·
                      refine ⟨2525032389313489058847413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26933678819343883294372405 2525032389313489058847413)
                      ·
                        rfl

theorem cell23_4917483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 5].length) (baseStart_4917483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917483 prefixEnd_4917483 := by exact prefixLift 4917483
  have htrace : WordTrace (prefixWord ++ tailWord_4917483) baseStart_4917483 baseEnd_4917483 := by
    simpa [prefixWord, tailWord_4917483, baseEnd_4917483] using wordTrace_append hprefix tailTrace_4917483
  have hstable : (prefixWord ++ tailWord_4917483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917483).length < 2 ^ (prefixWord ++ tailWord_4917483).sum := by decide
  have hdescent : baseEnd_4917483 < baseStart_4917483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917487 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 4, 1, 3]
def baseStart_4917487 : Nat := 118140960795 + 4917487 * 2 ^ 59
def prefixEnd_4917487 : Nat := 4983230072969 + 3 ^ 40 * 4917487 * 2
def baseEnd_4917487 : Nat := 2525034443236107043197395

theorem tailTrace_4917487 : CollatzResearch.WordTrace tailWord_4917487 prefixEnd_4917487 2525034443236107043197395 := by
  unfold tailWord_4917487
  simp only [CollatzResearch.WordTrace]
  refine ⟨179355485535791913761638715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119570323690527942507759143 179355485535791913761638715)
  ·
    refine ⟨269033228303687870642458073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179355485535791913761638715 269033228303687870642458073)
    ·
      refine ⟨201774921227765902981843555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269033228303687870642458073 201774921227765902981843555)
      ·
        refine ⟨302662381841648854472765333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201774921227765902981843555 302662381841648854472765333)
        ·
          refine ⟨14187299148827290053410875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 302662381841648854472765333 14187299148827290053410875)
          ·
            refine ⟨21280948723240935080116313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14187299148827290053410875 21280948723240935080116313)
            ·
              refine ⟨15960711542430701310087235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21280948723240935080116313 15960711542430701310087235)
              ·
                refine ⟨23941067313646051965130853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15960711542430701310087235 23941067313646051965130853)
                ·
                  refine ⟨4488950121308634743462035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23941067313646051965130853 4488950121308634743462035)
                  ·
                    refine ⟨6733425181962952115193053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4488950121308634743462035 6733425181962952115193053)
                    ·
                      refine ⟨2525034443236107043197395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6733425181962952115193053 2525034443236107043197395)
                      ·
                        rfl

theorem cell23_4917487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 1, 3].length) (baseStart_4917487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917487 prefixEnd_4917487 := by exact prefixLift 4917487
  have htrace : WordTrace (prefixWord ++ tailWord_4917487) baseStart_4917487 baseEnd_4917487 := by
    simpa [prefixWord, tailWord_4917487, baseEnd_4917487] using wordTrace_append hprefix tailTrace_4917487
  have hstable : (prefixWord ++ tailWord_4917487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917487).length < 2 ^ (prefixWord ++ tailWord_4917487).sum := by decide
  have hdescent : baseEnd_4917487 < baseStart_4917487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917503 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 1, 8]
def baseStart_4917503 : Nat := 118140960795 + 4917503 * 2 ^ 59
def prefixEnd_4917503 : Nat := 4983230072969 + 3 ^ 40 * 4917503 * 2
def baseEnd_4917503 : Nat := 841680886308859660199107

theorem tailTrace_4917503 : CollatzResearch.WordTrace tailWord_4917503 prefixEnd_4917503 841680886308859660199107 := by
  unfold tailWord_4917503
  simp only [CollatzResearch.WordTrace]
  refine ⟨179356069103733948494221163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119570712735822632329480775 179356069103733948494221163)
  ·
    refine ⟨269034103655600922741331745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179356069103733948494221163 269034103655600922741331745)
    ·
      refine ⟨201775577741700692055998809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269034103655600922741331745 201775577741700692055998809)
      ·
        refine ⟨151331683306275519041999107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201775577741700692055998809 151331683306275519041999107)
        ·
          refine ⟨226997524959413278562998661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151331683306275519041999107 226997524959413278562998661)
          ·
            refine ⟨42562035929889989730562249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 226997524959413278562998661 42562035929889989730562249)
            ·
              refine ⟨31921526947417492297921687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42562035929889989730562249 31921526947417492297921687)
              ·
                refine ⟨47882290421126238446882531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31921526947417492297921687 47882290421126238446882531)
                ·
                  refine ⟨71823435631689357670323797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47882290421126238446882531 71823435631689357670323797)
                  ·
                    refine ⟨841680886308859660199107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71823435631689357670323797 841680886308859660199107)
                    ·
                      rfl

theorem cell23_4917503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 8].length) (baseStart_4917503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917503 prefixEnd_4917503 := by exact prefixLift 4917503
  have htrace : WordTrace (prefixWord ++ tailWord_4917503) baseStart_4917503 baseEnd_4917503 := by
    simpa [prefixWord, tailWord_4917503, baseEnd_4917503] using wordTrace_append hprefix tailTrace_4917503
  have hstable : (prefixWord ++ tailWord_4917503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917503).length < 2 ^ (prefixWord ++ tailWord_4917503).sum := by decide
  have hdescent : baseEnd_4917503 < baseStart_4917503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917504 : List Nat := [2, 1, 1, 2, 1, 1, 8, 1, 2, 1, 3]
def baseStart_4917504 : Nat := 118140960795 + 4917504 * 2 ^ 59
def prefixEnd_4917504 : Nat := 4983230072969 + 3 ^ 40 * 4917504 * 2
def baseEnd_4917504 : Nat := 2525043172407233476684817

theorem tailTrace_4917504 : CollatzResearch.WordTrace tailWord_4917504 prefixEnd_4917504 2525043172407233476684817 := by
  unfold tailWord_4917504
  simp only [CollatzResearch.WordTrace]
  refine ⟨89678052788365162832503783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119570737051153550443338377 89678052788365162832503783)
  ·
    refine ⟨134517079182547744248755675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89678052788365162832503783 134517079182547744248755675)
    ·
      refine ⟨201775618773821616373133513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134517079182547744248755675 201775618773821616373133513)
      ·
        refine ⟨151331714080366212279850135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201775618773821616373133513 151331714080366212279850135)
        ·
          refine ⟨226997571120549318419775203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151331714080366212279850135 226997571120549318419775203)
          ·
            refine ⟨340496356680823977629662805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226997571120549318419775203 340496356680823977629662805)
            ·
              refine ⟨3990191679853405987847611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 340496356680823977629662805 3990191679853405987847611)
              ·
                refine ⟨5985287519780108981771417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3990191679853405987847611 5985287519780108981771417)
                ·
                  refine ⟨4488965639835081736328563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5985287519780108981771417 4488965639835081736328563)
                  ·
                    refine ⟨6733448459752622604492845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4488965639835081736328563 6733448459752622604492845)
                    ·
                      refine ⟨2525043172407233476684817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6733448459752622604492845 2525043172407233476684817)
                      ·
                        rfl

theorem cell23_4917504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 2, 1, 3].length) (baseStart_4917504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917504 prefixEnd_4917504 := by exact prefixLift 4917504
  have htrace : WordTrace (prefixWord ++ tailWord_4917504) baseStart_4917504 baseEnd_4917504 := by
    simpa [prefixWord, tailWord_4917504, baseEnd_4917504] using wordTrace_append hprefix tailTrace_4917504
  have hstable : (prefixWord ++ tailWord_4917504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917504).length < 2 ^ (prefixWord ++ tailWord_4917504).sum := by decide
  have hdescent : baseEnd_4917504 < baseStart_4917504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917514 : List Nat := [3, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2]
def baseStart_4917514 : Nat := 118140960795 + 4917514 * 2 ^ 59
def prefixEnd_4917514 : Nat := 4983230072969 + 3 ^ 40 * 4917514 * 2
def baseEnd_4917514 : Nat := 2525048307213778437559771

theorem tailTrace_4917514 : CollatzResearch.WordTrace tailWord_4917514 prefixEnd_4917514 2525048307213778437559771 := by
  unfold tailWord_4917514
  simp only [CollatzResearch.WordTrace]
  refine ⟨44839117576673524343217899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119570980204462731581914397 44839117576673524343217899)
  ·
    refine ⟨67258676365010286514826849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44839117576673524343217899 67258676365010286514826849)
    ·
      refine ⟨50444007273757714886120137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67258676365010286514826849 50444007273757714886120137)
      ·
        refine ⟨37833005455318286164590103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50444007273757714886120137 37833005455318286164590103)
        ·
          refine ⟨56749508182977429246885155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37833005455318286164590103 56749508182977429246885155)
          ·
            refine ⟨85124262274466143870327733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56749508182977429246885155 85124262274466143870327733)
            ·
              refine ⟨7980399588231200987843225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85124262274466143870327733 7980399588231200987843225)
              ·
                refine ⟨5985299691173400740882419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7980399588231200987843225 5985299691173400740882419)
                ·
                  refine ⟨8977949536760101111323629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5985299691173400740882419 8977949536760101111323629)
                  ·
                    refine ⟨3366731076285037916746361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8977949536760101111323629 3366731076285037916746361)
                    ·
                      refine ⟨2525048307213778437559771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3366731076285037916746361 2525048307213778437559771)
                      ·
                        rfl

theorem cell23_4917514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_4917514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917514 prefixEnd_4917514 := by exact prefixLift 4917514
  have htrace : WordTrace (prefixWord ++ tailWord_4917514) baseStart_4917514 baseEnd_4917514 := by
    simpa [prefixWord, tailWord_4917514, baseEnd_4917514] using wordTrace_append hprefix tailTrace_4917514
  have hstable : (prefixWord ++ tailWord_4917514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917514).length < 2 ^ (prefixWord ++ tailWord_4917514).sum := by decide
  have hdescent : baseEnd_4917514 < baseStart_4917514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917527 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 3, 4, 2]
def baseStart_4917527 : Nat := 118140960795 + 4917527 * 2 ^ 59
def prefixEnd_4917527 : Nat := 4983230072969 + 3 ^ 40 * 4917527 * 2
def baseEnd_4917527 : Nat := 2525054982462286886697211

theorem tailTrace_4917527 : CollatzResearch.WordTrace tailWord_4917527 prefixEnd_4917527 2525054982462286886697211 := by
  unfold tailWord_4917527
  simp only [CollatzResearch.WordTrace]
  refine ⟨179356944455647000593094835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119571296303764667062063223 179356944455647000593094835)
  ·
    refine ⟨269035416683470500889642253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179356944455647000593094835 269035416683470500889642253)
    ·
      refine ⟨100888281256301437833615845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269035416683470500889642253 100888281256301437833615845)
      ·
        refine ⟨18916552735556519593802971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100888281256301437833615845 18916552735556519593802971)
        ·
          refine ⟨28374829103334779390704457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18916552735556519593802971 28374829103334779390704457)
          ·
            refine ⟨21281121827501084543028343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28374829103334779390704457 21281121827501084543028343)
            ·
              refine ⟨31921682741251626814542515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21281121827501084543028343 31921682741251626814542515)
              ·
                refine ⟨47882524111877440221813773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31921682741251626814542515 47882524111877440221813773)
                ·
                  refine ⟨17955946541954040083180165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47882524111877440221813773 17955946541954040083180165)
                  ·
                    refine ⟨3366739976616382515596281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17955946541954040083180165 3366739976616382515596281)
                    ·
                      refine ⟨2525054982462286886697211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3366739976616382515596281 2525054982462286886697211)
                      ·
                        rfl

theorem cell23_4917527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_4917527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917527 prefixEnd_4917527 := by exact prefixLift 4917527
  have htrace : WordTrace (prefixWord ++ tailWord_4917527) baseStart_4917527 baseEnd_4917527 := by
    simpa [prefixWord, tailWord_4917527, baseEnd_4917527] using wordTrace_append hprefix tailTrace_4917527
  have hstable : (prefixWord ++ tailWord_4917527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917527).length < 2 ^ (prefixWord ++ tailWord_4917527).sum := by decide
  have hdescent : baseEnd_4917527 < baseStart_4917527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917560 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 1, 5, 3]
def baseStart_4917560 : Nat := 118140960795 + 4917560 * 2 ^ 59
def prefixEnd_4917560 : Nat := 4983230072969 + 3 ^ 40 * 4917560 * 2
def baseEnd_4917560 : Nat := 2525071927323885257584559

theorem tailTrace_4917560 : CollatzResearch.WordTrace tailWord_4917560 prefixEnd_4917560 2525071927323885257584559 := by
  unfold tailWord_4917560
  simp only [CollatzResearch.WordTrace]
  refine ⟨89679074032263723614523067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119572098709684964819364089 89679074032263723614523067)
  ·
    refine ⟨134518611048395585421784601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89679074032263723614523067 134518611048395585421784601)
    ·
      refine ⟨100888958286296689066338451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134518611048395585421784601 100888958286296689066338451)
      ·
        refine ⟨151333437429445033599507677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100888958286296689066338451 151333437429445033599507677)
        ·
          refine ⟨56750039036041887599815379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151333437429445033599507677 56750039036041887599815379)
          ·
            refine ⟨85125058554062831399723069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56750039036041887599815379 85125058554062831399723069)
            ·
              refine ⟨31921896957773561774896151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85125058554062831399723069 31921896957773561774896151)
              ·
                refine ⟨47882845436660342662344227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31921896957773561774896151 47882845436660342662344227)
                ·
                  refine ⟨71824268154990513993516341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47882845436660342662344227 71824268154990513993516341)
                  ·
                    refine ⟨6733525139530360686892157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71824268154990513993516341 6733525139530360686892157)
                    ·
                      refine ⟨2525071927323885257584559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6733525139530360686892157 2525071927323885257584559)
                      ·
                        rfl

theorem cell23_4917560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 1, 5, 3].length) (baseStart_4917560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917560 prefixEnd_4917560 := by exact prefixLift 4917560
  have htrace : WordTrace (prefixWord ++ tailWord_4917560) baseStart_4917560 baseEnd_4917560 := by
    simpa [prefixWord, tailWord_4917560, baseEnd_4917560] using wordTrace_append hprefix tailTrace_4917560
  have hstable : (prefixWord ++ tailWord_4917560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917560).length < 2 ^ (prefixWord ++ tailWord_4917560).sum := by decide
  have hdescent : baseEnd_4917560 < baseStart_4917560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917561 : List Nat := [1, 2, 1, 6, 1, 1, 2, 3, 2, 2, 2]
def baseStart_4917561 : Nat := 118140960795 + 4917561 * 2 ^ 59
def prefixEnd_4917561 : Nat := 4983230072969 + 3 ^ 40 * 4917561 * 2
def baseEnd_4917561 : Nat := 2525072440804539753672055

theorem tailTrace_4917561 : CollatzResearch.WordTrace tailWord_4917561 prefixEnd_4917561 2525072440804539753672055 := by
  unfold tailWord_4917561
  simp only [CollatzResearch.WordTrace]
  refine ⟨179358184537523824399832537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119572123025015882933221691 179358184537523824399832537)
  ·
    refine ⟨134518638403142868299874403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179358184537523824399832537 134518638403142868299874403)
    ·
      refine ⟨201777957604714302449811605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134518638403142868299874403 201777957604714302449811605)
      ·
        refine ⟨9458341762720982927334919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 201777957604714302449811605 9458341762720982927334919)
        ·
          refine ⟨14187512644081474391002379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9458341762720982927334919 14187512644081474391002379)
          ·
            refine ⟨21281268966122211586503569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14187512644081474391002379 21281268966122211586503569)
            ·
              refine ⟨15960951724591658689877677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21281268966122211586503569 15960951724591658689877677)
              ·
                refine ⟨5985356896721872008704129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15960951724591658689877677 5985356896721872008704129)
                ·
                  refine ⟨4489017672541404006528097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5985356896721872008704129 4489017672541404006528097)
                  ·
                    refine ⟨3366763254406053004896073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4489017672541404006528097 3366763254406053004896073)
                    ·
                      refine ⟨2525072440804539753672055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3366763254406053004896073 2525072440804539753672055)
                      ·
                        rfl

theorem cell23_4917561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_4917561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917561 prefixEnd_4917561 := by exact prefixLift 4917561
  have htrace : WordTrace (prefixWord ++ tailWord_4917561) baseStart_4917561 baseEnd_4917561 := by
    simpa [prefixWord, tailWord_4917561, baseEnd_4917561] using wordTrace_append hprefix tailTrace_4917561
  have hstable : (prefixWord ++ tailWord_4917561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917561).length < 2 ^ (prefixWord ++ tailWord_4917561).sum := by decide
  have hdescent : baseEnd_4917561 < baseStart_4917561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917580 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 1, 7]
def baseStart_4917580 : Nat := 118140960795 + 4917580 * 2 ^ 59
def prefixEnd_4917580 : Nat := 4983230072969 + 3 ^ 40 * 4917580 * 2
def baseEnd_4917580 : Nat := 841694065645658393111489

theorem tailTrace_4917580 : CollatzResearch.WordTrace tailWord_4917580 prefixEnd_4917580 841694065645658393111489 := by
  unfold tailWord_4917580
  simp only [CollatzResearch.WordTrace]
  refine ⟨89679438762227495322387097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119572585016303327096516129 89679438762227495322387097)
  ·
    refine ⟨67259579071670621491790323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89679438762227495322387097 67259579071670621491790323)
    ·
      refine ⟨100889368607505932237685485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67259579071670621491790323 100889368607505932237685485)
      ·
        refine ⟨37833513227814724589132057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100889368607505932237685485 37833513227814724589132057)
        ·
          refine ⟨28375134920861043441849043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37833513227814724589132057 28375134920861043441849043)
          ·
            refine ⟨42562702381291565162773565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28375134920861043441849043 42562702381291565162773565)
            ·
              refine ⟨15961013392984336936040087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42562702381291565162773565 15961013392984336936040087)
              ·
                refine ⟨23941520089476505404060131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15961013392984336936040087 23941520089476505404060131)
                ·
                  refine ⟨35912280134214758106090197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23941520089476505404060131 35912280134214758106090197)
                  ·
                    refine ⟨841694065645658393111489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35912280134214758106090197 841694065645658393111489)
                    ·
                      rfl

theorem cell23_4917580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_4917580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917580 prefixEnd_4917580 := by exact prefixLift 4917580
  have htrace : WordTrace (prefixWord ++ tailWord_4917580) baseStart_4917580 baseEnd_4917580 := by
    simpa [prefixWord, tailWord_4917580, baseEnd_4917580] using wordTrace_append hprefix tailTrace_4917580
  have hstable : (prefixWord ++ tailWord_4917580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917580).length < 2 ^ (prefixWord ++ tailWord_4917580).sum := by decide
  have hdescent : baseEnd_4917580 < baseStart_4917580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917627 : List Nat := [1, 1, 1, 1, 1, 7, 2, 2, 3, 4]
def baseStart_4917627 : Nat := 118140960795 + 4917627 * 2 ^ 59
def prefixEnd_4917627 : Nat := 4983230072969 + 3 ^ 40 * 4917627 * 2
def baseEnd_4917627 : Nat := 841702110175912165148917

theorem tailTrace_4917627 : CollatzResearch.WordTrace tailWord_4917627 prefixEnd_4917627 841702110175912165148917 := by
  unfold tailWord_4917627
  simp only [CollatzResearch.WordTrace]
  refine ⟨179360591755284717671735135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119573727836856478447823423 179360591755284717671735135)
  ·
    refine ⟨269040887632927076507602703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179360591755284717671735135 269040887632927076507602703)
    ·
      refine ⟨403561331449390614761404055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269040887632927076507602703 403561331449390614761404055)
      ·
        refine ⟨605341997174085922142106083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403561331449390614761404055 605341997174085922142106083)
        ·
          refine ⟨908012995761128883213159125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605341997174085922142106083 908012995761128883213159125)
          ·
            refine ⟨21281554588151458200308417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 908012995761128883213159125 21281554588151458200308417)
            ·
              refine ⟨15961165941113593650231313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21281554588151458200308417 15961165941113593650231313)
              ·
                refine ⟨11970874455835195237673485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15961165941113593650231313 11970874455835195237673485)
                ·
                  refine ⟨4489077920938198214127557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11970874455835195237673485 4489077920938198214127557)
                  ·
                    refine ⟨841702110175912165148917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4489077920938198214127557 841702110175912165148917)
                    ·
                      rfl

theorem cell23_4917627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 4].length) (baseStart_4917627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917627 prefixEnd_4917627 := by exact prefixLift 4917627
  have htrace : WordTrace (prefixWord ++ tailWord_4917627) baseStart_4917627 baseEnd_4917627 := by
    simpa [prefixWord, tailWord_4917627, baseEnd_4917627] using wordTrace_append hprefix tailTrace_4917627
  have hstable : (prefixWord ++ tailWord_4917627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917627).length < 2 ^ (prefixWord ++ tailWord_4917627).sum := by decide
  have hdescent : baseEnd_4917627 < baseStart_4917627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917637 : List Nat := [1, 3, 1, 1, 3, 1, 1, 5, 2, 2, 3]
def baseStart_4917637 : Nat := 118140960795 + 4917637 * 2 ^ 59
def prefixEnd_4917637 : Nat := 4983230072969 + 3 ^ 40 * 4917637 * 2
def baseEnd_4917637 : Nat := 2525111465334281456321705

theorem tailTrace_4917637 : CollatzResearch.WordTrace tailWord_4917637 prefixEnd_4917637 2525111465334281456321705 := by
  unfold tailWord_4917637
  simp only [CollatzResearch.WordTrace]
  refine ⟨179360956485248489379599165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119573970990165659586399443 179360956485248489379599165)
  ·
    refine ⟨67260358681968183517349687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179360956485248489379599165 67260358681968183517349687)
    ·
      refine ⟨100890538022952275276024531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67260358681968183517349687 100890538022952275276024531)
      ·
        refine ⟨151335807034428412914036797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100890538022952275276024531 151335807034428412914036797)
        ·
          refine ⟨56750927637910654842763799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151335807034428412914036797 56750927637910654842763799)
          ·
            refine ⟨85126391456865982264145699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56750927637910654842763799 85126391456865982264145699)
            ·
              refine ⟨127689587185298973396218549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85126391456865982264145699 127689587185298973396218549)
              ·
                refine ⟨11970898798621778755895489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127689587185298973396218549 11970898798621778755895489)
                ·
                  refine ⟨8978174098966334066921617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11970898798621778755895489 8978174098966334066921617)
                  ·
                    refine ⟨6733630574224750550191213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8978174098966334066921617 6733630574224750550191213)
                    ·
                      refine ⟨2525111465334281456321705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6733630574224750550191213 2525111465334281456321705)
                      ·
                        rfl

theorem cell23_4917637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 2, 3].length) (baseStart_4917637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917637 prefixEnd_4917637 := by exact prefixLift 4917637
  have htrace : WordTrace (prefixWord ++ tailWord_4917637) baseStart_4917637 baseEnd_4917637 := by
    simpa [prefixWord, tailWord_4917637, baseEnd_4917637] using wordTrace_append hprefix tailTrace_4917637
  have hstable : (prefixWord ++ tailWord_4917637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917637).length < 2 ^ (prefixWord ++ tailWord_4917637).sum := by decide
  have hdescent : baseEnd_4917637 < baseStart_4917637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917640 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 10]
def baseStart_4917640 : Nat := 118140960795 + 4917640 * 2 ^ 59
def prefixEnd_4917640 : Nat := 4983230072969 + 3 ^ 40 * 4917640 * 2
def baseEnd_4917640 : Nat := 280568111752916104953799

theorem tailTrace_4917640 : CollatzResearch.WordTrace tailWord_4917640 prefixEnd_4917640 280568111752916104953799 := by
  unfold tailWord_4917640
  simp only [CollatzResearch.WordTrace]
  refine ⟨89680532952118810445979187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119574043936158413927972249 89680532952118810445979187)
  ·
    refine ⟨134520799428178215668968781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89680532952118810445979187 134520799428178215668968781)
    ·
      refine ⟨50445299785566830875863293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134520799428178215668968781 50445299785566830875863293)
      ·
        refine ⟨18916987419587561578448735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50445299785566830875863293 18916987419587561578448735)
        ·
          refine ⟨28375481129381342367673103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18916987419587561578448735 28375481129381342367673103)
          ·
            refine ⟨42563221694072013551509655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28375481129381342367673103 42563221694072013551509655)
            ·
              refine ⟨63844832541108020327264483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42563221694072013551509655 63844832541108020327264483)
              ·
                refine ⟨95767248811662030490896725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63844832541108020327264483 95767248811662030490896725)
                ·
                  refine ⟨280568111752916104953799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 95767248811662030490896725 280568111752916104953799)
                  ·
                    rfl

theorem cell23_4917640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 10].length) (baseStart_4917640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917640 prefixEnd_4917640 := by exact prefixLift 4917640
  have htrace : WordTrace (prefixWord ++ tailWord_4917640) baseStart_4917640 baseEnd_4917640 := by
    simpa [prefixWord, tailWord_4917640, baseEnd_4917640] using wordTrace_append hprefix tailTrace_4917640
  have hstable : (prefixWord ++ tailWord_4917640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917640).length < 2 ^ (prefixWord ++ tailWord_4917640).sum := by decide
  have hdescent : baseEnd_4917640 < baseStart_4917640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917661 : List Nat := [1, 4, 2, 1, 4, 2, 1, 1, 3, 4]
def baseStart_4917661 : Nat := 118140960795 + 4917661 * 2 ^ 59
def prefixEnd_4917661 : Nat := 4983230072969 + 3 ^ 40 * 4917661 * 2
def baseEnd_4917661 : Nat := 841707929623329787473865

theorem tailTrace_4917661 : CollatzResearch.WordTrace tailWord_4917661 prefixEnd_4917661 841707929623329787473865 := by
  unfold tailWord_4917661
  simp only [CollatzResearch.WordTrace]
  refine ⟨179361831837161541478472837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119574554558107694318981891 179361831837161541478472837)
  ·
    refine ⟨33630343469467789027213657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179361831837161541478472837 33630343469467789027213657)
    ·
      refine ⟨25222757602100841770410243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33630343469467789027213657 25222757602100841770410243)
      ·
        refine ⟨37834136403151262655615365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25222757602100841770410243 37834136403151262655615365)
        ·
          refine ⟨7093900575590861747927881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37834136403151262655615365 7093900575590861747927881)
          ·
            refine ⟨5320425431693146310945911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7093900575590861747927881 5320425431693146310945911)
            ·
              refine ⟨7980638147539719466418867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5320425431693146310945911 7980638147539719466418867)
              ·
                refine ⟨11970957221309579199628301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7980638147539719466418867 11970957221309579199628301)
                ·
                  refine ⟨4489108957991092199860613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11970957221309579199628301 4489108957991092199860613)
                  ·
                    refine ⟨841707929623329787473865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4489108957991092199860613 841707929623329787473865)
                    ·
                      rfl

theorem cell23_4917661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_4917661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917661 prefixEnd_4917661 := by exact prefixLift 4917661
  have htrace : WordTrace (prefixWord ++ tailWord_4917661) baseStart_4917661 baseEnd_4917661 := by
    simpa [prefixWord, tailWord_4917661, baseEnd_4917661] using wordTrace_append hprefix tailTrace_4917661
  have hstable : (prefixWord ++ tailWord_4917661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917661).length < 2 ^ (prefixWord ++ tailWord_4917661).sum := by decide
  have hdescent : baseEnd_4917661 < baseStart_4917661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917687 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 3, 5]
def baseStart_4917687 : Nat := 118140960795 + 4917687 * 2 ^ 59
def prefixEnd_4917687 : Nat := 4983230072969 + 3 ^ 40 * 4917687 * 2
def baseEnd_4917687 : Nat := 841712379789002086898825

theorem tailTrace_4917687 : CollatzResearch.WordTrace tailWord_4917687 prefixEnd_4917687 841712379789002086898825 := by
  unfold tailWord_4917687
  simp only [CollatzResearch.WordTrace]
  refine ⟨179362780135067347918919315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119575186756711565279279543 179362780135067347918919315)
  ·
    refine ⟨269044170202601021878378973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179362780135067347918919315 269044170202601021878378973)
    ·
      refine ⟨100891563825975383204392115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269044170202601021878378973 100891563825975383204392115)
      ·
        refine ⟨151337345738963074806588173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100891563825975383204392115 151337345738963074806588173)
        ·
          refine ⟨56751504652111153052470565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151337345738963074806588173 56751504652111153052470565)
          ·
            refine ⟨10640907122270841197338231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56751504652111153052470565 10640907122270841197338231)
            ·
              refine ⟨15961360683406261796007347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10640907122270841197338231 15961360683406261796007347)
              ·
                refine ⟨23942041025109392694011021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15961360683406261796007347 23942041025109392694011021)
                ·
                  refine ⟨8978265384416022260254133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23942041025109392694011021 8978265384416022260254133)
                  ·
                    refine ⟨841712379789002086898825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8978265384416022260254133 841712379789002086898825)
                    ·
                      rfl

theorem cell23_4917687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_4917687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917687 prefixEnd_4917687 := by exact prefixLift 4917687
  have htrace : WordTrace (prefixWord ++ tailWord_4917687) baseStart_4917687 baseEnd_4917687 := by
    simpa [prefixWord, tailWord_4917687, baseEnd_4917687] using wordTrace_append hprefix tailTrace_4917687
  have hstable : (prefixWord ++ tailWord_4917687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917687).length < 2 ^ (prefixWord ++ tailWord_4917687).sum := by decide
  have hdescent : baseEnd_4917687 < baseStart_4917687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917694 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2]
def baseStart_4917694 : Nat := 118140960795 + 4917694 * 2 ^ 59
def prefixEnd_4917694 : Nat := 4983230072969 + 3 ^ 40 * 4917694 * 2
def baseEnd_4917694 : Nat := 2525140733731587733308943

theorem tailTrace_4917694 : CollatzResearch.WordTrace tailWord_4917694 prefixEnd_4917694 2525140733731587733308943 := by
  unfold tailWord_4917694
  simp only [CollatzResearch.WordTrace]
  refine ⟨22420379430755248514303017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119575356964027992076282757 22420379430755248514303017)
  ·
    refine ⟨16815284573066436385727263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22420379430755248514303017 16815284573066436385727263)
    ·
      refine ⟨25222926859599654578590895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16815284573066436385727263 25222926859599654578590895)
      ·
        refine ⟨37834390289399481867886343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25222926859599654578590895 37834390289399481867886343)
        ·
          refine ⟨56751585434099222801829515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37834390289399481867886343 56751585434099222801829515)
          ·
            refine ⟨85127378151148834202744273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56751585434099222801829515 85127378151148834202744273)
            ·
              refine ⟨63845533613361625652058205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85127378151148834202744273 63845533613361625652058205)
              ·
                refine ⟨23942075105010609619521827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63845533613361625652058205 23942075105010609619521827)
                ·
                  refine ⟨35913112657515914429282741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23942075105010609619521827 35913112657515914429282741)
                  ·
                    refine ⟨3366854311642116977745257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35913112657515914429282741 3366854311642116977745257)
                    ·
                      refine ⟨2525140733731587733308943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3366854311642116977745257 2525140733731587733308943)
                      ·
                        rfl

theorem cell23_4917694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_4917694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917694 prefixEnd_4917694 := by exact prefixLift 4917694
  have htrace : WordTrace (prefixWord ++ tailWord_4917694) baseStart_4917694 baseEnd_4917694 := by
    simpa [prefixWord, tailWord_4917694, baseEnd_4917694] using wordTrace_append hprefix tailTrace_4917694
  have hstable : (prefixWord ++ tailWord_4917694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917694).length < 2 ^ (prefixWord ++ tailWord_4917694).sum := by decide
  have hdescent : baseEnd_4917694 < baseStart_4917694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917744 : List Nat := [2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 3]
def baseStart_4917744 : Nat := 118140960795 + 4917744 * 2 ^ 59
def prefixEnd_4917744 : Nat := 4983230072969 + 3 ^ 40 * 4917744 * 2
def baseEnd_4917744 : Nat := 2525166407764312537683713

theorem tailTrace_4917744 : CollatzResearch.WordTrace tailWord_4917744 prefixEnd_4917744 2525166407764312537683713 := by
  unfold tailWord_4917744
  simp only [CollatzResearch.WordTrace]
  refine ⟨89682429547930423326872143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119576572730573897769162857 89682429547930423326872143)
  ·
    refine ⟨134523644321895634990308215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89682429547930423326872143 134523644321895634990308215)
    ·
      refine ⟨201785466482843452485462323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134523644321895634990308215 201785466482843452485462323)
      ·
        refine ⟨302678199724265178728193485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201785466482843452485462323 302678199724265178728193485)
        ·
          refine ⟨113504324896599442023072557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 302678199724265178728193485 113504324896599442023072557)
          ·
            refine ⟨42564121836224790758652209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113504324896599442023072557 42564121836224790758652209)
            ·
              refine ⟨31923091377168593068989157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42564121836224790758652209 31923091377168593068989157)
              ·
                refine ⟨5985579633219111200435467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31923091377168593068989157 5985579633219111200435467)
                ·
                  refine ⟨8978369449828666800653201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5985579633219111200435467 8978369449828666800653201)
                  ·
                    refine ⟨6733777087371500100489901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8978369449828666800653201 6733777087371500100489901)
                    ·
                      refine ⟨2525166407764312537683713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6733777087371500100489901 2525166407764312537683713)
                      ·
                        rfl

theorem cell23_4917744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 3].length) (baseStart_4917744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917744 prefixEnd_4917744 := by exact prefixLift 4917744
  have htrace : WordTrace (prefixWord ++ tailWord_4917744) baseStart_4917744 baseEnd_4917744 := by
    simpa [prefixWord, tailWord_4917744, baseEnd_4917744] using wordTrace_append hprefix tailTrace_4917744
  have hstable : (prefixWord ++ tailWord_4917744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917744).length < 2 ^ (prefixWord ++ tailWord_4917744).sum := by decide
  have hdescent : baseEnd_4917744 < baseStart_4917744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917747 : List Nat := [1, 1, 1, 2, 2, 2, 7, 7]
def baseStart_4917747 : Nat := 118140960795 + 4917747 * 2 ^ 59
def prefixEnd_4917747 : Nat := 4983230072969 + 3 ^ 40 * 4917747 * 2
def baseEnd_4917747 : Nat := 93524738822454667627637

theorem tailTrace_4917747 : CollatzResearch.WordTrace tailWord_4917747 prefixEnd_4917747 93524738822454667627637 := by
  unfold tailWord_4917747
  simp only [CollatzResearch.WordTrace]
  refine ⟨179364968514849978166103495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119576645676566652110735663 179364968514849978166103495)
  ·
    refine ⟨269047452772274967249155243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179364968514849978166103495 269047452772274967249155243)
    ·
      refine ⟨403571179158412450873732865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269047452772274967249155243 403571179158412450873732865)
      ·
        refine ⟨302678384368809338155299649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 403571179158412450873732865 302678384368809338155299649)
        ·
          refine ⟨227008788276607003616474737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302678384368809338155299649 227008788276607003616474737)
          ·
            refine ⟨170256591207455252712356053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227008788276607003616474737 170256591207455252712356053)
            ·
              refine ⟨3990388856424732485445845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 170256591207455252712356053 3990388856424732485445845)
              ·
                refine ⟨93524738822454667627637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3990388856424732485445845 93524738822454667627637)
                ·
                  rfl

theorem cell23_4917747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 7].length) (baseStart_4917747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917747 prefixEnd_4917747 := by exact prefixLift 4917747
  have htrace : WordTrace (prefixWord ++ tailWord_4917747) baseStart_4917747 baseEnd_4917747 := by
    simpa [prefixWord, tailWord_4917747, baseEnd_4917747] using wordTrace_append hprefix tailTrace_4917747
  have hstable : (prefixWord ++ tailWord_4917747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917747).length < 2 ^ (prefixWord ++ tailWord_4917747).sum := by decide
  have hdescent : baseEnd_4917747 < baseStart_4917747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917761 : List Nat := [1, 2, 4, 1, 3, 2, 1, 3, 1, 2, 3]
def baseStart_4917761 : Nat := 118140960795 + 4917761 * 2 ^ 59
def prefixEnd_4917761 : Nat := 4983230072969 + 3 ^ 40 * 4917761 * 2
def baseEnd_4917761 : Nat := 2525175136935438971171135

theorem tailTrace_4917761 : CollatzResearch.WordTrace tailWord_4917761 prefixEnd_4917761 2525175136935438971171135 := by
  unfold tailWord_4917761
  simp only [CollatzResearch.WordTrace]
  refine ⟨179365479136799258557113137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119576986091199505704742091 179365479136799258557113137)
  ·
    refine ⟨134524109352599443917834853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179365479136799258557113137 134524109352599443917834853)
    ·
      refine ⟨25223270503612395734594035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134524109352599443917834853 25223270503612395734594035)
      ·
        refine ⟨37834905755418593601891053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25223270503612395734594035 37834905755418593601891053)
        ·
          refine ⟨14188089658281972600709145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37834905755418593601891053 14188089658281972600709145)
          ·
            refine ⟨10641067243711479450531859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14188089658281972600709145 10641067243711479450531859)
            ·
              refine ⟨15961600865567219175797789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10641067243711479450531859 15961600865567219175797789)
              ·
                refine ⟨5985600324587707190924171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15961600865567219175797789 5985600324587707190924171)
                ·
                  refine ⟨8978400486881560786386257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5985600324587707190924171 8978400486881560786386257)
                  ·
                    refine ⟨6733800365161170589789693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8978400486881560786386257 6733800365161170589789693)
                    ·
                      refine ⟨2525175136935438971171135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6733800365161170589789693 2525175136935438971171135)
                      ·
                        rfl

theorem cell23_4917761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_4917761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917761 prefixEnd_4917761 := by exact prefixLift 4917761
  have htrace : WordTrace (prefixWord ++ tailWord_4917761) baseStart_4917761 baseEnd_4917761 := by
    simpa [prefixWord, tailWord_4917761, baseEnd_4917761] using wordTrace_append hprefix tailTrace_4917761
  have hstable : (prefixWord ++ tailWord_4917761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917761).length < 2 ^ (prefixWord ++ tailWord_4917761).sum := by decide
  have hdescent : baseEnd_4917761 < baseStart_4917761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917797 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 2, 3, 4]
def baseStart_4917797 : Nat := 118140960795 + 4917797 * 2 ^ 59
def prefixEnd_4917797 : Nat := 4983230072969 + 3 ^ 40 * 4917797 * 2
def baseEnd_4917797 : Nat := 2525193622239000830320969

theorem tailTrace_4917797 : CollatzResearch.WordTrace tailWord_4917797 prefixEnd_4917797 2525193622239000830320969 := by
  unfold tailWord_4917797
  simp only [CollatzResearch.WordTrace]
  refine ⟨179366792164668836705423645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119577861443112557803615763 179366792164668836705423645)
  ·
    refine ⟨67262547061750813764533867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179366792164668836705423645 67262547061750813764533867)
    ·
      refine ⟨100893820592626220646800801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67262547061750813764533867 100893820592626220646800801)
      ·
        refine ⟨75670365444469665485100601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100893820592626220646800801 75670365444469665485100601)
        ·
          refine ⟨56752774083352249113825451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75670365444469665485100601 56752774083352249113825451)
          ·
            refine ⟨85129161125028373670738177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56752774083352249113825451 85129161125028373670738177)
            ·
              refine ⟨63846870843771280253053633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85129161125028373670738177 63846870843771280253053633)
              ·
                refine ⟨47885153132828460189790225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63846870843771280253053633 47885153132828460189790225)
                ·
                  refine ⟨35913864849621345142342669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47885153132828460189790225 35913864849621345142342669)
                  ·
                    refine ⟨13467699318608004428378501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35913864849621345142342669 13467699318608004428378501)
                    ·
                      refine ⟨2525193622239000830320969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13467699318608004428378501 2525193622239000830320969)
                      ·
                        rfl

theorem cell23_4917797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_4917797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917797 prefixEnd_4917797 := by exact prefixLift 4917797
  have htrace : WordTrace (prefixWord ++ tailWord_4917797) baseStart_4917797 baseEnd_4917797 := by
    simpa [prefixWord, tailWord_4917797, baseEnd_4917797] using wordTrace_append hprefix tailTrace_4917797
  have hstable : (prefixWord ++ tailWord_4917797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917797).length < 2 ^ (prefixWord ++ tailWord_4917797).sum := by decide
  have hdescent : baseEnd_4917797 < baseStart_4917797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917827 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 4]
def baseStart_4917827 : Nat := 118140960795 + 4917827 * 2 ^ 59
def prefixEnd_4917827 : Nat := 4983230072969 + 3 ^ 40 * 4917827 * 2
def baseEnd_4917827 : Nat := 2525209026658635712945831

theorem tailTrace_4917827 : CollatzResearch.WordTrace tailWord_4917827 prefixEnd_4917827 2525209026658635712945831 := by
  unfold tailWord_4917827
  simp only [CollatzResearch.WordTrace]
  refine ⟨179367886354560151829015735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119578590903040101219343823 179367886354560151829015735)
  ·
    refine ⟨269051829531840227743523603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179367886354560151829015735 269051829531840227743523603)
    ·
      refine ⟨403577744297760341615285405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269051829531840227743523603 403577744297760341615285405)
      ·
        refine ⟨151341654111660128105732027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 403577744297760341615285405 151341654111660128105732027)
        ·
          refine ⟨227012481167490192158598041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151341654111660128105732027 227012481167490192158598041)
          ·
            refine ⟨170259360875617644118948531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227012481167490192158598041 170259360875617644118948531)
            ·
              refine ⟨255389041313426466178422797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170259360875617644118948531 255389041313426466178422797)
              ·
                refine ⟨95770890492534924816908549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 255389041313426466178422797 95770890492534924816908549)
                ·
                  refine ⟨17957041967350298403170353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95770890492534924816908549 17957041967350298403170353)
                  ·
                    refine ⟨13467781475512723802377765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17957041967350298403170353 13467781475512723802377765)
                    ·
                      refine ⟨2525209026658635712945831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13467781475512723802377765 2525209026658635712945831)
                      ·
                        rfl

theorem cell23_4917827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_4917827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917827 prefixEnd_4917827 := by exact prefixLift 4917827
  have htrace : WordTrace (prefixWord ++ tailWord_4917827) baseStart_4917827 baseEnd_4917827 := by
    simpa [prefixWord, tailWord_4917827, baseEnd_4917827] using wordTrace_append hprefix tailTrace_4917827
  have hstable : (prefixWord ++ tailWord_4917827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917827).length < 2 ^ (prefixWord ++ tailWord_4917827).sum := by decide
  have hdescent : baseEnd_4917827 < baseStart_4917827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917852 : List Nat := [2, 2, 4, 1, 4, 1, 1, 2, 1, 3, 2]
def baseStart_4917852 : Nat := 118140960795 + 4917852 * 2 ^ 59
def prefixEnd_4917852 : Nat := 4983230072969 + 3 ^ 40 * 4917852 * 2
def baseEnd_4917852 : Nat := 2525221863674998115133217

theorem tailTrace_4917852 : CollatzResearch.WordTrace tailWord_4917852 prefixEnd_4917852 2525221863674998115133217 := by
  unfold tailWord_4917852
  simp only [CollatzResearch.WordTrace]
  refine ⟨89684399089734790549337905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119579198786313054065783873 89684399089734790549337905)
  ·
    refine ⟨67263299317301092912003429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89684399089734790549337905 67263299317301092912003429)
    ·
      refine ⟨12611868621993954921000643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67263299317301092912003429 12611868621993954921000643)
      ·
        refine ⟨18917802932990932381500965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12611868621993954921000643 18917802932990932381500965)
        ·
          refine ⟨3547088049935799821531431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18917802932990932381500965 3547088049935799821531431)
          ·
            refine ⟨5320632074903699732297147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3547088049935799821531431 5320632074903699732297147)
            ·
              refine ⟨7980948112355549598445721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5320632074903699732297147 7980948112355549598445721)
              ·
                refine ⟨5985711084266662198834291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7980948112355549598445721 5985711084266662198834291)
                ·
                  refine ⟨8978566626399993298251437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5985711084266662198834291 8978566626399993298251437)
                  ·
                    refine ⟨3366962484899997486844289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8978566626399993298251437 3366962484899997486844289)
                    ·
                      refine ⟨2525221863674998115133217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3366962484899997486844289 2525221863674998115133217)
                      ·
                        rfl

theorem cell23_4917852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_4917852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917852 prefixEnd_4917852 := by exact prefixLift 4917852
  have htrace : WordTrace (prefixWord ++ tailWord_4917852) baseStart_4917852 baseEnd_4917852 := by
    simpa [prefixWord, tailWord_4917852, baseEnd_4917852] using wordTrace_append hprefix tailTrace_4917852
  have hstable : (prefixWord ++ tailWord_4917852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917852).length < 2 ^ (prefixWord ++ tailWord_4917852).sum := by decide
  have hdescent : baseEnd_4917852 < baseStart_4917852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917884 : List Nat := [2, 2, 2, 1, 1, 2, 4, 2, 2, 5]
def baseStart_4917884 : Nat := 118140960795 + 4917884 * 2 ^ 59
def prefixEnd_4917884 : Nat := 4983230072969 + 3 ^ 40 * 4917884 * 2
def baseEnd_4917884 : Nat := 841746098351980663311023

theorem tailTrace_4917884 : CollatzResearch.WordTrace tailWord_4917884 prefixEnd_4917884 841746098351980663311023 := by
  unfold tailWord_4917884
  simp only [CollatzResearch.WordTrace]
  refine ⟨89684982657676825281920353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119579976876902433709227137 89684982657676825281920353)
  ·
    refine ⟨67263736993257618961440265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89684982657676825281920353 67263736993257618961440265)
    ·
      refine ⟨50447802744943214221080199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67263736993257618961440265 50447802744943214221080199)
      ·
        refine ⟨75671704117414821331620299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50447802744943214221080199 75671704117414821331620299)
        ·
          refine ⟨113507556176122231997430449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75671704117414821331620299 113507556176122231997430449)
          ·
            refine ⟨85130667132091673998072837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113507556176122231997430449 85130667132091673998072837)
            ·
              refine ⟨15962000087267188874638657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85130667132091673998072837 15962000087267188874638657)
              ·
                refine ⟨11971500065450391655978993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15962000087267188874638657 11971500065450391655978993)
                ·
                  refine ⟨8978625049087793741984245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11971500065450391655978993 8978625049087793741984245)
                  ·
                    refine ⟨841746098351980663311023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8978625049087793741984245 841746098351980663311023)
                    ·
                      rfl

theorem cell23_4917884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_4917884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917884 prefixEnd_4917884 := by exact prefixLift 4917884
  have htrace : WordTrace (prefixWord ++ tailWord_4917884) baseStart_4917884 baseEnd_4917884 := by
    simpa [prefixWord, tailWord_4917884, baseEnd_4917884] using wordTrace_append hprefix tailTrace_4917884
  have hstable : (prefixWord ++ tailWord_4917884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917884).length < 2 ^ (prefixWord ++ tailWord_4917884).sum := by decide
  have hdescent : baseEnd_4917884 < baseStart_4917884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917888 : List Nat := [2, 1, 1, 2, 1, 7, 2, 2, 5]
def baseStart_4917888 : Nat := 118140960795 + 4917888 * 2 ^ 59
def prefixEnd_4917888 : Nat := 4983230072969 + 3 ^ 40 * 4917888 * 2
def baseEnd_4917888 : Nat := 280582260997617774920339

theorem tailTrace_4917888 : CollatzResearch.WordTrace tailWord_4917888 prefixEnd_4917888 280582260997617774920339 := by
  unfold tailWord_4917888
  simp only [CollatzResearch.WordTrace]
  refine ⟨89685055603669579623493159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119580074138226106164657545 89685055603669579623493159)
  ·
    refine ⟨134527583405504369435239739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89685055603669579623493159 134527583405504369435239739)
    ·
      refine ⟨201791375108256554152859609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134527583405504369435239739 201791375108256554152859609)
      ·
        refine ⟨151343531331192415614644707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201791375108256554152859609 151343531331192415614644707)
        ·
          refine ⟨227015296996788623421967061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151343531331192415614644707 227015296996788623421967061)
          ·
            refine ⟨5320671023362233361452353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 227015296996788623421967061 5320671023362233361452353)
            ·
              refine ⟨3990503267521675021089265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5320671023362233361452353 3990503267521675021089265)
              ·
                refine ⟨2992877450641256265816949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3990503267521675021089265 2992877450641256265816949)
                ·
                  refine ⟨280582260997617774920339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2992877450641256265816949 280582260997617774920339)
                  ·
                    rfl

theorem cell23_4917888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 5].length) (baseStart_4917888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917888 prefixEnd_4917888 := by exact prefixLift 4917888
  have htrace : WordTrace (prefixWord ++ tailWord_4917888) baseStart_4917888 baseEnd_4917888 := by
    simpa [prefixWord, tailWord_4917888, baseEnd_4917888] using wordTrace_append hprefix tailTrace_4917888
  have hstable : (prefixWord ++ tailWord_4917888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917888).length < 2 ^ (prefixWord ++ tailWord_4917888).sum := by decide
  have hdescent : baseEnd_4917888 < baseStart_4917888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917897 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 2, 8]
def baseStart_4917897 : Nat := 118140960795 + 4917897 * 2 ^ 59
def prefixEnd_4917897 : Nat := 4983230072969 + 3 ^ 40 * 4917897 * 2
def baseEnd_4917897 : Nat := 841748323434816813023503

theorem tailTrace_4917897 : CollatzResearch.WordTrace tailWord_4917897 prefixEnd_4917897 841748323434816813023503 := by
  unfold tailWord_4917897
  simp only [CollatzResearch.WordTrace]
  refine ⟨179370439464306553784063945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119580292976204369189375963 179370439464306553784063945)
  ·
    refine ⟨134527829598229915338047959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179370439464306553784063945 134527829598229915338047959)
    ·
      refine ⟨201791744397344873007071939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134527829598229915338047959 201791744397344873007071939)
      ·
        refine ⟨302687616596017309510607909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201791744397344873007071939 302687616596017309510607909)
        ·
          refine ⟨56753928111753245533238983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 302687616596017309510607909 56753928111753245533238983)
          ·
            refine ⟨85130892167629868299858475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56753928111753245533238983 85130892167629868299858475)
            ·
              refine ⟨127696338251444802449787713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85130892167629868299858475 127696338251444802449787713)
              ·
                refine ⟨95772253688583601837340785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127696338251444802449787713 95772253688583601837340785)
                ·
                  refine ⟨71829190266437701378005589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95772253688583601837340785 71829190266437701378005589)
                  ·
                    refine ⟨841748323434816813023503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71829190266437701378005589 841748323434816813023503)
                    ·
                      rfl

theorem cell23_4917897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 8].length) (baseStart_4917897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917897 prefixEnd_4917897 := by exact prefixLift 4917897
  have htrace : WordTrace (prefixWord ++ tailWord_4917897) baseStart_4917897 baseEnd_4917897 := by
    simpa [prefixWord, tailWord_4917897, baseEnd_4917897] using wordTrace_append hprefix tailTrace_4917897
  have hstable : (prefixWord ++ tailWord_4917897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917897).length < 2 ^ (prefixWord ++ tailWord_4917897).sum := by decide
  have hdescent : baseEnd_4917897 < baseStart_4917897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917907 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 5]
def baseStart_4917907 : Nat := 118140960795 + 4917907 * 2 ^ 59
def prefixEnd_4917907 : Nat := 4983230072969 + 3 ^ 40 * 4917907 * 2
def baseEnd_4917907 : Nat := 2525250105110995399945463

theorem tailTrace_4917907 : CollatzResearch.WordTrace tailWord_4917907 prefixEnd_4917907 2525250105110995399945463 := by
  unfold tailWord_4917907
  simp only [CollatzResearch.WordTrace]
  refine ⟨179370804194270325491927975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119580536129513550327951983 179370804194270325491927975)
  ·
    refine ⟨269056206291405488237891963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179370804194270325491927975 269056206291405488237891963)
    ·
      refine ⟨403584309437108232356837945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269056206291405488237891963 403584309437108232356837945)
      ·
        refine ⟨302688232077831174267628459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 403584309437108232356837945 302688232077831174267628459)
        ·
          refine ⟨454032348116746761401442689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302688232077831174267628459 454032348116746761401442689)
          ·
            refine ⟨340524261087560071051082017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 454032348116746761401442689 340524261087560071051082017)
            ·
              refine ⟨255393195815670053288311513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340524261087560071051082017 255393195815670053288311513)
              ·
                refine ⟨191544896861752539966233635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255393195815670053288311513 191544896861752539966233635)
                ·
                  refine ⟨287317345292628809949350453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191544896861752539966233635 287317345292628809949350453)
                  ·
                    refine ⟨26936001121183950932751605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 287317345292628809949350453 26936001121183950932751605)
                    ·
                      refine ⟨2525250105110995399945463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26936001121183950932751605 2525250105110995399945463)
                      ·
                        rfl

theorem cell23_4917907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_4917907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917907 prefixEnd_4917907 := by exact prefixLift 4917907
  have htrace : WordTrace (prefixWord ++ tailWord_4917907) baseStart_4917907 baseEnd_4917907 := by
    simpa [prefixWord, tailWord_4917907, baseEnd_4917907] using wordTrace_append hprefix tailTrace_4917907
  have hstable : (prefixWord ++ tailWord_4917907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917907).length < 2 ^ (prefixWord ++ tailWord_4917907).sum := by decide
  have hdescent : baseEnd_4917907 < baseStart_4917907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917921 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 1, 3, 4]
def baseStart_4917921 : Nat := 118140960795 + 4917921 * 2 ^ 59
def prefixEnd_4917921 : Nat := 4983230072969 + 3 ^ 40 * 4917921 * 2
def baseEnd_4917921 : Nat := 2525257293840158345170399

theorem tailTrace_4917921 : CollatzResearch.WordTrace tailWord_4917921 prefixEnd_4917921 2525257293840158345170399 := by
  unfold tailWord_4917921
  simp only [CollatzResearch.WordTrace]
  refine ⟨179371314816219605882937617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119580876544146403921958411 179371314816219605882937617)
  ·
    refine ⟨134528486112164704412203213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179371314816219605882937617 134528486112164704412203213)
    ·
      refine ⟨50448182292061764154576205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134528486112164704412203213 50448182292061764154576205)
      ·
        refine ⟨18918068359523161557966077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50448182292061764154576205 18918068359523161557966077)
        ·
          refine ⟨7094275634821185584237279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18918068359523161557966077 7094275634821185584237279)
          ·
            refine ⟨10641413452231778376355919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7094275634821185584237279 10641413452231778376355919)
            ·
              refine ⟨15962120178347667564533879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10641413452231778376355919 15962120178347667564533879)
              ·
                refine ⟨23943180267521501346800819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15962120178347667564533879 23943180267521501346800819)
                ·
                  refine ⟨35914770401282252020201229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23943180267521501346800819 35914770401282252020201229)
                  ·
                    refine ⟨13468038900480844507575461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35914770401282252020201229 13468038900480844507575461)
                    ·
                      refine ⟨2525257293840158345170399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13468038900480844507575461 2525257293840158345170399)
                      ·
                        rfl

theorem cell23_4917921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_4917921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917921 prefixEnd_4917921 := by exact prefixLift 4917921
  have htrace : WordTrace (prefixWord ++ tailWord_4917921) baseStart_4917921 baseEnd_4917921 := by
    simpa [prefixWord, tailWord_4917921, baseEnd_4917921] using wordTrace_append hprefix tailTrace_4917921
  have hstable : (prefixWord ++ tailWord_4917921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917921).length < 2 ^ (prefixWord ++ tailWord_4917921).sum := by decide
  have hdescent : baseEnd_4917921 < baseStart_4917921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917948 : List Nat := [2, 2, 2, 3, 1, 1, 1, 6, 1, 4]
def baseStart_4917948 : Nat := 118140960795 + 4917948 * 2 ^ 59
def prefixEnd_4917948 : Nat := 4983230072969 + 3 ^ 40 * 4917948 * 2
def baseEnd_4917948 : Nat := 841757052605943246510925

theorem tailTrace_4917948 : CollatzResearch.WordTrace tailWord_4917948 prefixEnd_4917948 841757052605943246510925 := by
  unfold tailWord_4917948
  simp only [CollatzResearch.WordTrace]
  refine ⟨89686149793560894747085249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119581533058081192996113665 89686149793560894747085249)
  ·
    refine ⟨67264612345170671060313937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89686149793560894747085249 67264612345170671060313937)
    ·
      refine ⟨50448459258878003295235453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67264612345170671060313937 50448459258878003295235453)
      ·
        refine ⟨18918172222079251235713295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50448459258878003295235453 18918172222079251235713295)
        ·
          refine ⟨28377258333118876853569943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18918172222079251235713295 28377258333118876853569943)
          ·
            refine ⟨42565887499678315280354915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28377258333118876853569943 42565887499678315280354915)
            ·
              refine ⟨63848831249517472920532373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42565887499678315280354915 63848831249517472920532373)
              ·
                refine ⟨2992913964821131543149955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63848831249517472920532373 2992913964821131543149955)
                ·
                  refine ⟨4489370947231697314724933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2992913964821131543149955 4489370947231697314724933)
                  ·
                    refine ⟨841757052605943246510925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4489370947231697314724933 841757052605943246510925)
                    ·
                      rfl

theorem cell23_4917948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_4917948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917948 prefixEnd_4917948 := by exact prefixLift 4917948
  have htrace : WordTrace (prefixWord ++ tailWord_4917948) baseStart_4917948 baseEnd_4917948 := by
    simpa [prefixWord, tailWord_4917948, baseEnd_4917948] using wordTrace_append hprefix tailTrace_4917948
  have hstable : (prefixWord ++ tailWord_4917948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917948).length < 2 ^ (prefixWord ++ tailWord_4917948).sum := by decide
  have hdescent : baseEnd_4917948 < baseStart_4917948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4917998 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 4, 3, 2]
def baseStart_4917998 : Nat := 118140960795 + 4917998 * 2 ^ 59
def prefixEnd_4917998 : Nat := 4983230072969 + 3 ^ 40 * 4917998 * 2
def baseEnd_4917998 : Nat := 2525296831850554543907545

theorem tailTrace_4917998 : CollatzResearch.WordTrace tailWord_4917998 prefixEnd_4917998 2525296831850554543907545 := by
  unfold tailWord_4917998
  simp only [CollatzResearch.WordTrace]
  refine ⟨22421765404617581004186331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119582748824627098688993765 22421765404617581004186331)
  ·
    refine ⟨33632648106926371506279497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22421765404617581004186331 33632648106926371506279497)
    ·
      refine ⟨25224486080194778629709623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33632648106926371506279497 25224486080194778629709623)
      ·
        refine ⟨37836729120292167944564435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25224486080194778629709623 37836729120292167944564435)
        ·
          refine ⟨56755093680438251916846653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37836729120292167944564435 56755093680438251916846653)
          ·
            refine ⟨21283160130164344468817495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56755093680438251916846653 21283160130164344468817495)
            ·
              refine ⟨31924740195246516703226243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21283160130164344468817495 31924740195246516703226243)
              ·
                refine ⟨47887110292869775054839365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31924740195246516703226243 47887110292869775054839365)
                ·
                  refine ⟨8978833179913082822782381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47887110292869775054839365 8978833179913082822782381)
                  ·
                    refine ⟨3367062442467406058543393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8978833179913082822782381 3367062442467406058543393)
                    ·
                      refine ⟨2525296831850554543907545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3367062442467406058543393 2525296831850554543907545)
                      ·
                        rfl

theorem cell23_4917998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_4917998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4917998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4917998 prefixEnd_4917998 := by exact prefixLift 4917998
  have htrace : WordTrace (prefixWord ++ tailWord_4917998) baseStart_4917998 baseEnd_4917998 := by
    simpa [prefixWord, tailWord_4917998, baseEnd_4917998] using wordTrace_append hprefix tailTrace_4917998
  have hstable : (prefixWord ++ tailWord_4917998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4917998).length < 2 ^ (prefixWord ++ tailWord_4917998).sum := by decide
  have hdescent : baseEnd_4917998 < baseStart_4917998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4917998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918028 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 5, 2, 2]
def baseStart_4918028 : Nat := 118140960795 + 4918028 * 2 ^ 59
def prefixEnd_4918028 : Nat := 4983230072969 + 3 ^ 40 * 4918028 * 2
def baseEnd_4918028 : Nat := 2525312236270189426532407

theorem tailTrace_4918028 : CollatzResearch.WordTrace tailWord_4918028 prefixEnd_4918028 2525312236270189426532407 := by
  unfold tailWord_4918028
  simp only [CollatzResearch.WordTrace]
  refine ⟨89687608713415981578541369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119583478284554642104721825 89687608713415981578541369)
  ·
    refine ⟨67265706535061986183906027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89687608713415981578541369 67265706535061986183906027)
    ·
      refine ⟨100898559802592979275859041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67265706535061986183906027 100898559802592979275859041)
      ·
        refine ⟨75673919851944734456894281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100898559802592979275859041 75673919851944734456894281)
        ·
          refine ⟨56755439888958550842670711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75673919851944734456894281 56755439888958550842670711)
          ·
            refine ⟨85133159833437826264006067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56755439888958550842670711 85133159833437826264006067)
            ·
              refine ⟨127699739750156739396009101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85133159833437826264006067 127699739750156739396009101)
              ·
                refine ⟨47887402406308777273503413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127699739750156739396009101 47887402406308777273503413)
                ·
                  refine ⟨4489443975591447869390945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47887402406308777273503413 4489443975591447869390945)
                  ·
                    refine ⟨3367082981693585902043209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4489443975591447869390945 3367082981693585902043209)
                    ·
                      refine ⟨2525312236270189426532407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3367082981693585902043209 2525312236270189426532407)
                      ·
                        rfl

theorem cell23_4918028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_4918028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918028 prefixEnd_4918028 := by exact prefixLift 4918028
  have htrace : WordTrace (prefixWord ++ tailWord_4918028) baseStart_4918028 baseEnd_4918028 := by
    simpa [prefixWord, tailWord_4918028, baseEnd_4918028] using wordTrace_append hprefix tailTrace_4918028
  have hstable : (prefixWord ++ tailWord_4918028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918028).length < 2 ^ (prefixWord ++ tailWord_4918028).sum := by decide
  have hdescent : baseEnd_4918028 < baseStart_4918028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918031 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 3]
def baseStart_4918031 : Nat := 118140960795 + 4918031 * 2 ^ 59
def prefixEnd_4918031 : Nat := 4983230072969 + 3 ^ 40 * 4918031 * 2
def baseEnd_4918031 : Nat := 2525313776712152914794893

theorem tailTrace_4918031 : CollatzResearch.WordTrace tailWord_4918031 prefixEnd_4918031 2525313776712152914794893 := by
  unfold tailWord_4918031
  simp only [CollatzResearch.WordTrace]
  refine ⟨179375326845821094669441947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119583551230547396446294631 179375326845821094669441947)
  ·
    refine ⟨269062990268731642004162921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179375326845821094669441947 269062990268731642004162921)
    ·
      refine ⟨201797242701548731503122191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269062990268731642004162921 201797242701548731503122191)
      ·
        refine ⟨302695864052323097254683287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201797242701548731503122191 302695864052323097254683287)
        ·
          refine ⟨454043796078484645882024931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302695864052323097254683287 454043796078484645882024931)
          ·
            refine ⟨681065694117726968823037397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454043796078484645882024931 681065694117726968823037397)
            ·
              refine ⟨15962477205884225831789939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 681065694117726968823037397 15962477205884225831789939)
              ·
                refine ⟨23943715808826338747684909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15962477205884225831789939 23943715808826338747684909)
                ·
                  refine ⟨8978893428309877030381841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23943715808826338747684909 8978893428309877030381841)
                  ·
                    refine ⟨6734170071232407772786381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8978893428309877030381841 6734170071232407772786381)
                    ·
                      refine ⟨2525313776712152914794893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6734170071232407772786381 2525313776712152914794893)
                      ·
                        rfl

theorem cell23_4918031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 3].length) (baseStart_4918031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918031 prefixEnd_4918031 := by exact prefixLift 4918031
  have htrace : WordTrace (prefixWord ++ tailWord_4918031) baseStart_4918031 baseEnd_4918031 := by
    simpa [prefixWord, tailWord_4918031, baseEnd_4918031] using wordTrace_append hprefix tailTrace_4918031
  have hstable : (prefixWord ++ tailWord_4918031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918031).length < 2 ^ (prefixWord ++ tailWord_4918031).sum := by decide
  have hdescent : baseEnd_4918031 < baseStart_4918031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918048 : List Nat := [2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 5]
def baseStart_4918048 : Nat := 118140960795 + 4918048 * 2 ^ 59
def prefixEnd_4918048 : Nat := 4983230072969 + 3 ^ 40 * 4918048 * 2
def baseEnd_4918048 : Nat := 2525322505883279348282315

theorem tailTrace_4918048 : CollatzResearch.WordTrace tailWord_4918048 prefixEnd_4918048 2525322505883279348282315 := by
  unfold tailWord_4918048
  simp only [CollatzResearch.WordTrace]
  refine ⟨89687973443379753286405399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119583964591173004381873865 89687973443379753286405399)
  ·
    refine ⟨134531960165069629929608099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89687973443379753286405399 134531960165069629929608099)
    ·
      refine ⟨201797940247604444894412149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134531960165069629929608099 201797940247604444894412149)
      ·
        refine ⟨18918556898212916708851139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 201797940247604444894412149 18918556898212916708851139)
        ·
          refine ⟨28377835347319375063276709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18918556898212916708851139 28377835347319375063276709)
          ·
            refine ⟨5320844127622382824364383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28377835347319375063276709 5320844127622382824364383)
            ·
              refine ⟨7981266191433574236546575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5320844127622382824364383 7981266191433574236546575)
              ·
                refine ⟨11971899287150361354819863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7981266191433574236546575 11971899287150361354819863)
                ·
                  refine ⟨17957848930725542032229795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11971899287150361354819863 17957848930725542032229795)
                  ·
                    refine ⟨26936773396088313048344693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17957848930725542032229795 26936773396088313048344693)
                    ·
                      refine ⟨2525322505883279348282315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26936773396088313048344693 2525322505883279348282315)
                      ·
                        rfl

theorem cell23_4918048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_4918048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918048 prefixEnd_4918048 := by exact prefixLift 4918048
  have htrace : WordTrace (prefixWord ++ tailWord_4918048) baseStart_4918048 baseEnd_4918048 := by
    simpa [prefixWord, tailWord_4918048, baseEnd_4918048] using wordTrace_append hprefix tailTrace_4918048
  have hstable : (prefixWord ++ tailWord_4918048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918048).length < 2 ^ (prefixWord ++ tailWord_4918048).sum := by decide
  have hdescent : baseEnd_4918048 < baseStart_4918048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918088 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 3, 3, 2]
def baseStart_4918088 : Nat := 118140960795 + 4918088 * 2 ^ 59
def prefixEnd_4918088 : Nat := 4983230072969 + 3 ^ 40 * 4918088 * 2
def baseEnd_4918088 : Nat := 2525343045109459191782131

theorem tailTrace_4918088 : CollatzResearch.WordTrace tailWord_4918088 prefixEnd_4918088 2525343045109459191782131 := by
  unfold tailWord_4918088
  simp only [CollatzResearch.WordTrace]
  refine ⟨89688702903307296702133459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119584937204409728936177945 89688702903307296702133459)
  ·
    refine ⟨134533054354960945053200189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89688702903307296702133459 134533054354960945053200189)
    ·
      refine ⟨50449895383110354394950071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134533054354960945053200189 50449895383110354394950071)
      ·
        refine ⟨75674843074665531592425107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50449895383110354394950071 75674843074665531592425107)
        ·
          refine ⟨113512264611998297388637661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75674843074665531592425107 113512264611998297388637661)
          ·
            refine ⟨42567099229499361520739123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113512264611998297388637661 42567099229499361520739123)
            ·
              refine ⟨63850648844249042281108685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42567099229499361520739123 63850648844249042281108685)
              ·
                refine ⟨23943993316593390855415757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63850648844249042281108685 23943993316593390855415757)
                ·
                  refine ⟨8978997493722521570780909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23943993316593390855415757 8978997493722521570780909)
                  ·
                    refine ⟨3367124060145945589042841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8978997493722521570780909 3367124060145945589042841)
                    ·
                      refine ⟨2525343045109459191782131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3367124060145945589042841 2525343045109459191782131)
                      ·
                        rfl

theorem cell23_4918088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 3, 3, 2].length) (baseStart_4918088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918088 prefixEnd_4918088 := by exact prefixLift 4918088
  have htrace : WordTrace (prefixWord ++ tailWord_4918088) baseStart_4918088 baseEnd_4918088 := by
    simpa [prefixWord, tailWord_4918088, baseEnd_4918088] using wordTrace_append hprefix tailTrace_4918088
  have hstable : (prefixWord ++ tailWord_4918088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918088).length < 2 ^ (prefixWord ++ tailWord_4918088).sum := by decide
  have hdescent : baseEnd_4918088 < baseStart_4918088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918105 : List Nat := [1, 2, 1, 2, 2, 5, 1, 3, 1, 3, 2]
def baseStart_4918105 : Nat := 118140960795 + 4918105 * 2 ^ 59
def prefixEnd_4918105 : Nat := 4983230072969 + 3 ^ 40 * 4918105 * 2
def baseEnd_4918105 : Nat := 2525351774280585625269553

theorem tailTrace_4918105 : CollatzResearch.WordTrace tailWord_4918105 prefixEnd_4918105 2525351774280585625269553 := by
  unfold tailWord_4918105
  simp only [CollatzResearch.WordTrace]
  refine ⟨179378025847553005307635769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119585350565035336871757179 179378025847553005307635769)
  ·
    refine ⟨134533519385664753980726827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179378025847553005307635769 134533519385664753980726827)
    ·
      refine ⟨201800279078497130971090241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134533519385664753980726827 201800279078497130971090241)
      ·
        refine ⟨151350209308872848228317681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201800279078497130971090241 151350209308872848228317681)
        ·
          refine ⟨113512656981654636171238261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151350209308872848228317681 113512656981654636171238261)
          ·
            refine ⟨10641811592030122141053587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113512656981654636171238261 10641811592030122141053587)
            ·
              refine ⟨15962717388045183211580381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10641811592030122141053587 15962717388045183211580381)
              ·
                refine ⟨5986019020516943704342643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15962717388045183211580381 5986019020516943704342643)
                ·
                  refine ⟨8979028530775415556513965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5986019020516943704342643 8979028530775415556513965)
                  ·
                    refine ⟨3367135699040780833692737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8979028530775415556513965 3367135699040780833692737)
                    ·
                      refine ⟨2525351774280585625269553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3367135699040780833692737 2525351774280585625269553)
                      ·
                        rfl

theorem cell23_4918105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 3, 2].length) (baseStart_4918105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918105 prefixEnd_4918105 := by exact prefixLift 4918105
  have htrace : WordTrace (prefixWord ++ tailWord_4918105) baseStart_4918105 baseEnd_4918105 := by
    simpa [prefixWord, tailWord_4918105, baseEnd_4918105] using wordTrace_append hprefix tailTrace_4918105
  have hstable : (prefixWord ++ tailWord_4918105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918105).length < 2 ^ (prefixWord ++ tailWord_4918105).sum := by decide
  have hdescent : baseEnd_4918105 < baseStart_4918105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918131 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 4]
def baseStart_4918131 : Nat := 118140960795 + 4918131 * 2 ^ 59
def prefixEnd_4918131 : Nat := 4983230072969 + 3 ^ 40 * 4918131 * 2
def baseEnd_4918131 : Nat := 2525365124777602523544433

theorem tailTrace_4918131 : CollatzResearch.WordTrace tailWord_4918131 prefixEnd_4918131 2525365124777602523544433 := by
  unfold tailWord_4918131
  simp only [CollatzResearch.WordTrace]
  refine ⟨179378974145458811748082247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119585982763639207832054831 179378974145458811748082247)
  ·
    refine ⟨269068461218188217622123371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179378974145458811748082247 269068461218188217622123371)
    ·
      refine ⟨403602691827282326433185057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269068461218188217622123371 403602691827282326433185057)
      ·
        refine ⟨302702018870461744824888793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 403602691827282326433185057 302702018870461744824888793)
        ·
          refine ⟨227026514152846308618666595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302702018870461744824888793 227026514152846308618666595)
          ·
            refine ⟨340539771229269462927999893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227026514152846308618666595 340539771229269462927999893)
            ·
              refine ⟨15962801776372006074749995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 340539771229269462927999893 15962801776372006074749995)
              ·
                refine ⟨23944202664558009112124993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15962801776372006074749995 23944202664558009112124993)
                ·
                  refine ⟨17958151998418506834093745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23944202664558009112124993 17958151998418506834093745)
                  ·
                    refine ⟨13468613998813880125570309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17958151998418506834093745 13468613998813880125570309)
                    ·
                      refine ⟨2525365124777602523544433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13468613998813880125570309 2525365124777602523544433)
                      ·
                        rfl

theorem cell23_4918131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 4].length) (baseStart_4918131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918131 prefixEnd_4918131 := by exact prefixLift 4918131
  have htrace : WordTrace (prefixWord ++ tailWord_4918131) baseStart_4918131 baseEnd_4918131 := by
    simpa [prefixWord, tailWord_4918131, baseEnd_4918131] using wordTrace_append hprefix tailTrace_4918131
  have hstable : (prefixWord ++ tailWord_4918131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918131).length < 2 ^ (prefixWord ++ tailWord_4918131).sum := by decide
  have hdescent : baseEnd_4918131 < baseStart_4918131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918135 : List Nat := [1, 1, 3, 1, 1, 2, 1, 7, 2, 2, 2]
def baseStart_4918135 : Nat := 118140960795 + 4918135 * 2 ^ 59
def prefixEnd_4918135 : Nat := 4983230072969 + 3 ^ 40 * 4918135 * 2
def baseEnd_4918135 : Nat := 2525367178700220507894415

theorem tailTrace_4918135 : CollatzResearch.WordTrace tailWord_4918135 prefixEnd_4918135 2525367178700220507894415 := by
  unfold tailWord_4918135
  simp only [CollatzResearch.WordTrace]
  refine ⟨179379120037444320431227859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119586080024962880287485239 179379120037444320431227859)
  ·
    refine ⟨269068680056166480646841789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179379120037444320431227859 269068680056166480646841789)
    ·
      refine ⟨100900755021062430242565671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269068680056166480646841789 100900755021062430242565671)
      ·
        refine ⟨151351132531593645363848507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100900755021062430242565671 151351132531593645363848507)
        ·
          refine ⟨227026698797390468045772761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151351132531593645363848507 227026698797390468045772761)
          ·
            refine ⟨170270024098042851034329571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227026698797390468045772761 170270024098042851034329571)
            ·
              refine ⟨255405036147064276551494357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170270024098042851034329571 255405036147064276551494357)
              ·
                refine ⟨5986055534696818981675649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 255405036147064276551494357 5986055534696818981675649)
                ·
                  refine ⟨4489541651022614236256737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5986055534696818981675649 4489541651022614236256737)
                  ·
                    refine ⟨3367156238266960677192553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4489541651022614236256737 3367156238266960677192553)
                    ·
                      refine ⟨2525367178700220507894415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3367156238266960677192553 2525367178700220507894415)
                      ·
                        rfl

theorem cell23_4918135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 2, 2].length) (baseStart_4918135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918135 prefixEnd_4918135 := by exact prefixLift 4918135
  have htrace : WordTrace (prefixWord ++ tailWord_4918135) baseStart_4918135 baseEnd_4918135 := by
    simpa [prefixWord, tailWord_4918135, baseEnd_4918135] using wordTrace_append hprefix tailTrace_4918135
  have hstable : (prefixWord ++ tailWord_4918135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918135).length < 2 ^ (prefixWord ++ tailWord_4918135).sum := by decide
  have hdescent : baseEnd_4918135 < baseStart_4918135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918141 : List Nat := [1, 4, 1, 1, 2, 1, 4, 2, 7]
def baseStart_4918141 : Nat := 118140960795 + 4918141 * 2 ^ 59
def prefixEnd_4918141 : Nat := 4983230072969 + 3 ^ 40 * 4918141 * 2
def baseEnd_4918141 : Nat := 280596695509349720491043

theorem tailTrace_4918141 : CollatzResearch.WordTrace tailWord_4918141 prefixEnd_4918141 280596695509349720491043 := by
  unfold tailWord_4918141
  simp only [CollatzResearch.WordTrace]
  refine ⟨179379338875422583455946277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119586225916948388970630851 179379338875422583455946277)
  ·
    refine ⟨33633626039141734397989927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179379338875422583455946277 33633626039141734397989927)
    ·
      refine ⟨50450439058712601596984891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33633626039141734397989927 50450439058712601596984891)
      ·
        refine ⟨75675658588068902395477337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50450439058712601596984891 75675658588068902395477337)
        ·
          refine ⟨56756743941051676796608003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75675658588068902395477337 56756743941051676796608003)
          ·
            refine ⟨85135115911577515194912005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56756743941051676796608003 85135115911577515194912005)
            ·
              refine ⟨15962834233420784099046001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85135115911577515194912005 15962834233420784099046001)
              ·
                refine ⟨11972125675065588074284501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15962834233420784099046001 11972125675065588074284501)
                ·
                  refine ⟨280596695509349720491043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11972125675065588074284501 280596695509349720491043)
                  ·
                    rfl

theorem cell23_4918141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_4918141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918141 prefixEnd_4918141 := by exact prefixLift 4918141
  have htrace : WordTrace (prefixWord ++ tailWord_4918141) baseStart_4918141 baseEnd_4918141 := by
    simpa [prefixWord, tailWord_4918141, baseEnd_4918141] using wordTrace_append hprefix tailTrace_4918141
  have hstable : (prefixWord ++ tailWord_4918141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918141).length < 2 ^ (prefixWord ++ tailWord_4918141).sum := by decide
  have hdescent : baseEnd_4918141 < baseStart_4918141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918191 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 4]
def baseStart_4918191 : Nat := 118140960795 + 4918191 * 2 ^ 59
def prefixEnd_4918191 : Nat := 4983230072969 + 3 ^ 40 * 4918191 * 2
def baseEnd_4918191 : Nat := 2525395933616872288794157

theorem tailTrace_4918191 : CollatzResearch.WordTrace tailWord_4918191 prefixEnd_4918191 2525395933616872288794157 := by
  unfold tailWord_4918191
  simp only [CollatzResearch.WordTrace]
  refine ⟨179381162525241441995266427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119587441683494294663510951 179381162525241441995266427)
  ·
    refine ⟨269071743787862162992899641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179381162525241441995266427 269071743787862162992899641)
    ·
      refine ⟨201803807840896622244674731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269071743787862162992899641 201803807840896622244674731)
      ·
        refine ⟨302705711761344933367012097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201803807840896622244674731 302705711761344933367012097)
        ·
          refine ⟨227029283821008700025259073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302705711761344933367012097 227029283821008700025259073)
          ·
            refine ⟨170271962865756525018944305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227029283821008700025259073 170271962865756525018944305)
            ·
              refine ⟨127703972149317393764208229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170271962865756525018944305 127703972149317393764208229)
              ·
                refine ⟨23944494777997011330789043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127703972149317393764208229 23944494777997011330789043)
                ·
                  refine ⟨35916742166995516996183565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23944494777997011330789043 35916742166995516996183565)
                  ·
                    refine ⟨13468778312623318873568837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35916742166995516996183565 13468778312623318873568837)
                    ·
                      refine ⟨2525395933616872288794157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13468778312623318873568837 2525395933616872288794157)
                      ·
                        rfl

theorem cell23_4918191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 4].length) (baseStart_4918191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918191 prefixEnd_4918191 := by exact prefixLift 4918191
  have htrace : WordTrace (prefixWord ++ tailWord_4918191) baseStart_4918191 baseEnd_4918191 := by
    simpa [prefixWord, tailWord_4918191, baseEnd_4918191] using wordTrace_append hprefix tailTrace_4918191
  have hstable : (prefixWord ++ tailWord_4918191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918191).length < 2 ^ (prefixWord ++ tailWord_4918191).sum := by decide
  have hdescent : baseEnd_4918191 < baseStart_4918191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918205 : List Nat := [1, 4, 1, 2, 4, 1, 2, 1, 2, 5]
def baseStart_4918205 : Nat := 118140960795 + 4918205 * 2 ^ 59
def prefixEnd_4918205 : Nat := 4983230072969 + 3 ^ 40 * 4918205 * 2
def baseEnd_4918205 : Nat := 841801040782011744673031

theorem tailTrace_4918205 : CollatzResearch.WordTrace tailWord_4918205 prefixEnd_4918205 841801040782011744673031 := by
  unfold tailWord_4918205
  simp only [CollatzResearch.WordTrace]
  refine ⟨179381673147190722386276069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119587782098127148257517379 179381673147190722386276069)
  ·
    refine ⟨33634063715098260447426763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179381673147190722386276069 33634063715098260447426763)
    ·
      refine ⟨50451095572647390671140145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33634063715098260447426763 50451095572647390671140145)
      ·
        refine ⟨37838321679485543003355109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50451095572647390671140145 37838321679485543003355109)
        ·
          refine ⟨7094685314903539313129083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37838321679485543003355109 7094685314903539313129083)
          ·
            refine ⟨10642027972355308969693625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7094685314903539313129083 10642027972355308969693625)
            ·
              refine ⟨7981520979266481727270219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10642027972355308969693625 7981520979266481727270219)
              ·
                refine ⟨11972281468899722590905329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7981520979266481727270219 11972281468899722590905329)
                ·
                  refine ⟨8979211101674791943178997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11972281468899722590905329 8979211101674791943178997)
                  ·
                    refine ⟨841801040782011744673031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8979211101674791943178997 841801040782011744673031)
                    ·
                      rfl

theorem cell23_4918205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_4918205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918205 prefixEnd_4918205 := by exact prefixLift 4918205
  have htrace : WordTrace (prefixWord ++ tailWord_4918205) baseStart_4918205 baseEnd_4918205 := by
    simpa [prefixWord, tailWord_4918205, baseEnd_4918205] using wordTrace_append hprefix tailTrace_4918205
  have hstable : (prefixWord ++ tailWord_4918205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918205).length < 2 ^ (prefixWord ++ tailWord_4918205).sum := by decide
  have hdescent : baseEnd_4918205 < baseStart_4918205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918208 : List Nat := [2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 4]
def baseStart_4918208 : Nat := 118140960795 + 4918208 * 2 ^ 59
def prefixEnd_4918208 : Nat := 4983230072969 + 3 ^ 40 * 4918208 * 2
def baseEnd_4918208 : Nat := 2525404662787998722281579

theorem tailTrace_4918208 : CollatzResearch.WordTrace tailWord_4918208 prefixEnd_4918208 2525404662787998722281579 := by
  unfold tailWord_4918208
  simp only [CollatzResearch.WordTrace]
  refine ⟨89690891283089926949317639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119587855044119902599090185 89690891283089926949317639)
  ·
    refine ⟨134536336924634890423976459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89690891283089926949317639 134536336924634890423976459)
    ·
      refine ⟨201804505386952335635964689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134536336924634890423976459 201804505386952335635964689)
      ·
        refine ⟨151353379040214251726973517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201804505386952335635964689 151353379040214251726973517)
        ·
          refine ⟨56757517140080344397615069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151353379040214251726973517 56757517140080344397615069)
          ·
            refine ⟨21284068927530129149105651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56757517140080344397615069 21284068927530129149105651)
            ·
              refine ⟨31926103391295193723658477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21284068927530129149105651 31926103391295193723658477)
              ·
                refine ⟨11972288771735697646371929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31926103391295193723658477 11972288771735697646371929)
                ·
                  refine ⟨8979216578801773234778947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11972288771735697646371929 8979216578801773234778947)
                  ·
                    refine ⟨13468824868202659852168421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8979216578801773234778947 13468824868202659852168421)
                    ·
                      refine ⟨2525404662787998722281579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13468824868202659852168421 2525404662787998722281579)
                      ·
                        rfl

theorem cell23_4918208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_4918208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918208 prefixEnd_4918208 := by exact prefixLift 4918208
  have htrace : WordTrace (prefixWord ++ tailWord_4918208) baseStart_4918208 baseEnd_4918208 := by
    simpa [prefixWord, tailWord_4918208, baseEnd_4918208] using wordTrace_append hprefix tailTrace_4918208
  have hstable : (prefixWord ++ tailWord_4918208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918208).length < 2 ^ (prefixWord ++ tailWord_4918208).sum := by decide
  have hdescent : baseEnd_4918208 < baseStart_4918208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918242 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_4918242 : Nat := 118140960795 + 4918242 * 2 ^ 59
def prefixEnd_4918242 : Nat := 4983230072969 + 3 ^ 40 * 4918242 * 2
def baseEnd_4918242 : Nat := 2525422121130251589256423

theorem tailTrace_4918242 : CollatzResearch.WordTrace tailWord_4918242 prefixEnd_4918242 2525422121130251589256423 := by
  unfold tailWord_4918242
  simp only [CollatzResearch.WordTrace]
  refine ⟨44845755662014169426343245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119588681765371118470248653 44845755662014169426343245)
  ·
    refine ⟨16817158373255313534878717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44845755662014169426343245 16817158373255313534878717)
    ·
      refine ⟨6306434389970742575579519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16817158373255313534878717 6306434389970742575579519)
      ·
        refine ⟨9459651584956113863369279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6306434389970742575579519 9459651584956113863369279)
        ·
          refine ⟨14189477377434170795053919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9459651584956113863369279 14189477377434170795053919)
          ·
            refine ⟨21284216066151256192580879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14189477377434170795053919 21284216066151256192580879)
            ·
              refine ⟨31926324099226884288871319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21284216066151256192580879 31926324099226884288871319)
              ·
                refine ⟨47889486148840326433306979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31926324099226884288871319 47889486148840326433306979)
                ·
                  refine ⟨71834229223260489649960469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47889486148840326433306979 71834229223260489649960469)
                  ·
                    refine ⟨3367229494840335452341897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71834229223260489649960469 3367229494840335452341897)
                    ·
                      refine ⟨2525422121130251589256423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3367229494840335452341897 2525422121130251589256423)
                      ·
                        rfl

theorem cell23_4918242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_4918242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918242 prefixEnd_4918242 := by exact prefixLift 4918242
  have htrace : WordTrace (prefixWord ++ tailWord_4918242) baseStart_4918242 baseEnd_4918242 := by
    simpa [prefixWord, tailWord_4918242, baseEnd_4918242] using wordTrace_append hprefix tailTrace_4918242
  have hstable : (prefixWord ++ tailWord_4918242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918242).length < 2 ^ (prefixWord ++ tailWord_4918242).sum := by decide
  have hdescent : baseEnd_4918242 < baseStart_4918242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918248 : List Nat := [2, 1, 4, 1, 1, 1, 4, 3, 6]
def baseStart_4918248 : Nat := 118140960795 + 4918248 * 2 ^ 59
def prefixEnd_4918248 : Nat := 4983230072969 + 3 ^ 40 * 4918248 * 2
def baseEnd_4918248 : Nat := 280602800223797618420155

theorem tailTrace_4918248 : CollatzResearch.WordTrace tailWord_4918248 prefixEnd_4918248 280602800223797618420155 := by
  unfold tailWord_4918248
  simp only [CollatzResearch.WordTrace]
  refine ⟨89691620743017470365045699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119588827657356627153394265 89691620743017470365045699)
  ·
    refine ⟨134537431114526205547568549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89691620743017470365045699 134537431114526205547568549)
    ·
      refine ⟨25225768333973663540169103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134537431114526205547568549 25225768333973663540169103)
      ·
        refine ⟨37838652500960495310253655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25225768333973663540169103 37838652500960495310253655)
        ·
          refine ⟨56757978751440742965380483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37838652500960495310253655 56757978751440742965380483)
          ·
            refine ⟨85136968127161114448070725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56757978751440742965380483 85136968127161114448070725)
            ·
              refine ⟨15963181523842708959013261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85136968127161114448070725 15963181523842708959013261)
              ·
                refine ⟨5986193071441015859629973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15963181523842708959013261 5986193071441015859629973)
                ·
                  refine ⟨280602800223797618420155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5986193071441015859629973 280602800223797618420155)
                  ·
                    rfl

theorem cell23_4918248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 6].length) (baseStart_4918248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918248 prefixEnd_4918248 := by exact prefixLift 4918248
  have htrace : WordTrace (prefixWord ++ tailWord_4918248) baseStart_4918248 baseEnd_4918248 := by
    simpa [prefixWord, tailWord_4918248, baseEnd_4918248] using wordTrace_append hprefix tailTrace_4918248
  have hstable : (prefixWord ++ tailWord_4918248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918248).length < 2 ^ (prefixWord ++ tailWord_4918248).sum := by decide
  have hdescent : baseEnd_4918248 < baseStart_4918248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918262 : List Nat := [5, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3]
def baseStart_4918262 : Nat := 118140960795 + 4918262 * 2 ^ 59
def prefixEnd_4918262 : Nat := 4983230072969 + 3 ^ 40 * 4918262 * 2
def baseEnd_4918262 : Nat := 2525432390743341511006331

theorem tailTrace_4918262 : CollatzResearch.WordTrace tailWord_4918262 prefixEnd_4918262 2525432390743341511006331 := by
  unfold tailWord_4918262
  simp only [CollatzResearch.WordTrace]
  refine ⟨11211484506749013820068815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119589168071989480747400693 11211484506749013820068815)
  ·
    refine ⟨16817226760123520730103223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11211484506749013820068815 16817226760123520730103223)
    ·
      refine ⟨25225840140185281095154835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16817226760123520730103223 25225840140185281095154835)
      ·
        refine ⟨37838760210277921642732253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25225840140185281095154835 37838760210277921642732253)
        ·
          refine ⟨14189535078854220616024595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37838760210277921642732253 14189535078854220616024595)
          ·
            refine ⟨21284302618281330924036893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14189535078854220616024595 21284302618281330924036893)
            ·
              refine ⟨7981613481855499096513835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21284302618281330924036893 7981613481855499096513835)
              ·
                refine ⟨11972420222783248644770753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7981613481855499096513835 11972420222783248644770753)
                ·
                  refine ⟨8979315167087436483578065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11972420222783248644770753 8979315167087436483578065)
                  ·
                    refine ⟨6734486375315577362683549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8979315167087436483578065 6734486375315577362683549)
                    ·
                      refine ⟨2525432390743341511006331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6734486375315577362683549 2525432390743341511006331)
                      ·
                        rfl

theorem cell23_4918262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_4918262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918262 prefixEnd_4918262 := by exact prefixLift 4918262
  have htrace : WordTrace (prefixWord ++ tailWord_4918262) baseStart_4918262 baseEnd_4918262 := by
    simpa [prefixWord, tailWord_4918262, baseEnd_4918262] using wordTrace_append hprefix tailTrace_4918262
  have hstable : (prefixWord ++ tailWord_4918262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918262).length < 2 ^ (prefixWord ++ tailWord_4918262).sum := by decide
  have hdescent : baseEnd_4918262 < baseStart_4918262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918271 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 5]
def baseStart_4918271 : Nat := 118140960795 + 4918271 * 2 ^ 59
def prefixEnd_4918271 : Nat := 4983230072969 + 3 ^ 40 * 4918271 * 2
def baseEnd_4918271 : Nat := 2525437012069231975793789

theorem tailTrace_4918271 : CollatzResearch.WordTrace tailWord_4918271 prefixEnd_4918271 2525437012069231975793789 := by
  unfold tailWord_4918271
  simp only [CollatzResearch.WordTrace]
  refine ⟨179384080364951615658178667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119589386909967743772119111 179384080364951615658178667)
  ·
    refine ⟨269076120547427423487268001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179384080364951615658178667 269076120547427423487268001)
    ·
      refine ⟨201807090410570567615451001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269076120547427423487268001 201807090410570567615451001)
      ·
        refine ⟨151355317807927925711588251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201807090410570567615451001 151355317807927925711588251)
        ·
          refine ⟨227032976711891888567382377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151355317807927925711588251 227032976711891888567382377)
          ·
            refine ⟨170274732533918916425536783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227032976711891888567382377 170274732533918916425536783)
            ·
              refine ⟨255412098800878374638305175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170274732533918916425536783 255412098800878374638305175)
              ·
                refine ⟨383118148201317561957457763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255412098800878374638305175 383118148201317561957457763)
                ·
                  refine ⟨574677222301976342936186645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 383118148201317561957457763 574677222301976342936186645)
                  ·
                    refine ⟨26937994795405141075133749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 574677222301976342936186645 26937994795405141075133749)
                    ·
                      refine ⟨2525437012069231975793789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26937994795405141075133749 2525437012069231975793789)
                      ·
                        rfl

theorem cell23_4918271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_4918271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918271 prefixEnd_4918271 := by exact prefixLift 4918271
  have htrace : WordTrace (prefixWord ++ tailWord_4918271) baseStart_4918271 baseEnd_4918271 := by
    simpa [prefixWord, tailWord_4918271, baseEnd_4918271] using wordTrace_append hprefix tailTrace_4918271
  have hstable : (prefixWord ++ tailWord_4918271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918271).length < 2 ^ (prefixWord ++ tailWord_4918271).sum := by decide
  have hdescent : baseEnd_4918271 < baseStart_4918271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918315 : List Nat := [1, 1, 1, 1, 2, 1, 8, 2, 1, 1, 4]
def baseStart_4918315 : Nat := 118140960795 + 4918315 * 2 ^ 59
def prefixEnd_4918315 : Nat := 4983230072969 + 3 ^ 40 * 4918315 * 2
def baseEnd_4918315 : Nat := 2525459605218029803643587

theorem tailTrace_4918315 : CollatzResearch.WordTrace tailWord_4918315 prefixEnd_4918315 2525459605218029803643587 := by
  unfold tailWord_4918315
  simp only [CollatzResearch.WordTrace]
  refine ⟨179385685176792211172780399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119590456784528140781853599 179385685176792211172780399)
  ·
    refine ⟨269078527765188316759170599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179385685176792211172780399 269078527765188316759170599)
    ·
      refine ⟨403617791647782475138755899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269078527765188316759170599 403617791647782475138755899)
      ·
        refine ⟨605426687471673712708133849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403617791647782475138755899 605426687471673712708133849)
        ·
          refine ⟨454070015603755284531100387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 605426687471673712708133849 454070015603755284531100387)
          ·
            refine ⟨681105023405632926796650581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454070015603755284531100387 681105023405632926796650581)
            ·
              refine ⟨7981699493034760860898249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 681105023405632926796650581 7981699493034760860898249)
              ·
                refine ⟨5986274619776070645673687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7981699493034760860898249 5986274619776070645673687)
                ·
                  refine ⟨8979411929664105968510531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5986274619776070645673687 8979411929664105968510531)
                  ·
                    refine ⟨13469117894496158952765797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8979411929664105968510531 13469117894496158952765797)
                    ·
                      refine ⟨2525459605218029803643587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13469117894496158952765797 2525459605218029803643587)
                      ·
                        rfl

theorem cell23_4918315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 1, 4].length) (baseStart_4918315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918315 prefixEnd_4918315 := by exact prefixLift 4918315
  have htrace : WordTrace (prefixWord ++ tailWord_4918315) baseStart_4918315 baseEnd_4918315 := by
    simpa [prefixWord, tailWord_4918315, baseEnd_4918315] using wordTrace_append hprefix tailTrace_4918315
  have hstable : (prefixWord ++ tailWord_4918315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918315).length < 2 ^ (prefixWord ++ tailWord_4918315).sum := by decide
  have hdescent : baseEnd_4918315 < baseStart_4918315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918326 : List Nat := [5, 1, 2, 1, 1, 2, 3, 3, 1, 1, 3]
def baseStart_4918326 : Nat := 118140960795 + 4918326 * 2 ^ 59
def prefixEnd_4918326 : Nat := 4983230072969 + 3 ^ 40 * 4918326 * 2
def baseEnd_4918326 : Nat := 2525465253505229260606037

theorem tailTrace_4918326 : CollatzResearch.WordTrace tailWord_4918326 prefixEnd_4918326 2525465253505229260606037 := by
  unfold tailWord_4918326
  simp only [CollatzResearch.WordTrace]
  refine ⟨11211630398734522503214427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119590724253168240034287221 11211630398734522503214427)
  ·
    refine ⟨16817445598101783754821641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11211630398734522503214427 16817445598101783754821641)
    ·
      refine ⟨12613084198576337816116231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16817445598101783754821641 12613084198576337816116231)
      ·
        refine ⟨18919626297864506724174347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12613084198576337816116231 18919626297864506724174347)
        ·
          refine ⟨28379439446796760086261521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18919626297864506724174347 28379439446796760086261521)
          ·
            refine ⟨21284579585097570064696141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28379439446796760086261521 21284579585097570064696141)
            ·
              refine ⟨7981717344411588774261053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21284579585097570064696141 7981717344411588774261053)
              ·
                refine ⟨2993144004154345790347895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7981717344411588774261053 2993144004154345790347895)
                ·
                  refine ⟨4489716006231518685521843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2993144004154345790347895 4489716006231518685521843)
                  ·
                    refine ⟨6734574009347278028282765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4489716006231518685521843 6734574009347278028282765)
                    ·
                      refine ⟨2525465253505229260606037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6734574009347278028282765 2525465253505229260606037)
                      ·
                        rfl

theorem cell23_4918326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_4918326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918326 prefixEnd_4918326 := by exact prefixLift 4918326
  have htrace : WordTrace (prefixWord ++ tailWord_4918326) baseStart_4918326 baseEnd_4918326 := by
    simpa [prefixWord, tailWord_4918326, baseEnd_4918326] using wordTrace_append hprefix tailTrace_4918326
  have hstable : (prefixWord ++ tailWord_4918326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918326).length < 2 ^ (prefixWord ++ tailWord_4918326).sum := by decide
  have hdescent : baseEnd_4918326 < baseStart_4918326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918366 : List Nat := [4, 4, 1, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_4918366 : Nat := 118140960795 + 4918366 * 2 ^ 59
def prefixEnd_4918366 : Nat := 4983230072969 + 3 ^ 40 * 4918366 * 2
def baseEnd_4918366 : Nat := 2525485792731409104105853

theorem tailTrace_4918366 : CollatzResearch.WordTrace tailWord_4918366 prefixEnd_4918366 2525485792731409104105853 := by
  unfold tailWord_4918366
  simp only [CollatzResearch.WordTrace]
  refine ⟨22423443162450930860360869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119591696866404964588591301 22423443162450930860360869)
  ·
    refine ⟨4204395592959549536317663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22423443162450930860360869 4204395592959549536317663)
    ·
      refine ⟨6306593389439324304476495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4204395592959549536317663 6306593389439324304476495)
      ·
        refine ⟨9459890084158986456714743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6306593389439324304476495 9459890084158986456714743)
        ·
          refine ⟨14189835126238479685072115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9459890084158986456714743 14189835126238479685072115)
          ·
            refine ⟨21284752689357719527608173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14189835126238479685072115 21284752689357719527608173)
            ·
              refine ⟨7981782258509144822853065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21284752689357719527608173 7981782258509144822853065)
              ·
                refine ⟨5986336693881858617139799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7981782258509144822853065 5986336693881858617139799)
                ·
                  refine ⟨8979505040822787925709699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5986336693881858617139799 8979505040822787925709699)
                  ·
                    refine ⟨13469257561234181888564549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8979505040822787925709699 13469257561234181888564549)
                    ·
                      refine ⟨2525485792731409104105853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13469257561234181888564549 2525485792731409104105853)
                      ·
                        rfl

theorem cell23_4918366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_4918366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918366 prefixEnd_4918366 := by exact prefixLift 4918366
  have htrace : WordTrace (prefixWord ++ tailWord_4918366) baseStart_4918366 baseEnd_4918366 := by
    simpa [prefixWord, tailWord_4918366, baseEnd_4918366] using wordTrace_append hprefix tailTrace_4918366
  have hstable : (prefixWord ++ tailWord_4918366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918366).length < 2 ^ (prefixWord ++ tailWord_4918366).sum := by decide
  have hdescent : baseEnd_4918366 < baseStart_4918366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918382 : List Nat := [4, 1, 2, 2, 1, 3, 1, 2, 1, 3, 3]
def baseStart_4918382 : Nat := 118140960795 + 4918382 * 2 ^ 59
def prefixEnd_4918382 : Nat := 4983230072969 + 3 ^ 40 * 4918382 * 2
def baseEnd_4918382 : Nat := 2525494008421881041505779

theorem tailTrace_4918382 : CollatzResearch.WordTrace tailWord_4918382 prefixEnd_4918382 2525494008421881041505779 := by
  unfold tailWord_4918382
  simp only [CollatzResearch.WordTrace]
  refine ⟨22423516108443685201933675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119592085911699654410312933 22423516108443685201933675)
  ·
    refine ⟨33635274162665527802900513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22423516108443685201933675 33635274162665527802900513)
    ·
      refine ⟨25226455621999145852175385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33635274162665527802900513 25226455621999145852175385)
      ·
        refine ⟨18919841716499359389131539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25226455621999145852175385 18919841716499359389131539)
        ·
          refine ⟨28379762574749039083697309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18919841716499359389131539 28379762574749039083697309)
          ·
            refine ⟨10642410965530889656386491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28379762574749039083697309 10642410965530889656386491)
            ·
              refine ⟨15963616448296334484579737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10642410965530889656386491 15963616448296334484579737)
              ·
                refine ⟨11972712336222250863434803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15963616448296334484579737 11972712336222250863434803)
                ·
                  refine ⟨17959068504333376295152205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11972712336222250863434803 17959068504333376295152205)
                  ·
                    refine ⟨6734650689125016110682077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17959068504333376295152205 6734650689125016110682077)
                    ·
                      refine ⟨2525494008421881041505779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6734650689125016110682077 2525494008421881041505779)
                      ·
                        rfl

theorem cell23_4918382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_4918382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918382 prefixEnd_4918382 := by exact prefixLift 4918382
  have htrace : WordTrace (prefixWord ++ tailWord_4918382) baseStart_4918382 baseEnd_4918382 := by
    simpa [prefixWord, tailWord_4918382, baseEnd_4918382] using wordTrace_append hprefix tailTrace_4918382
  have hstable : (prefixWord ++ tailWord_4918382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918382).length < 2 ^ (prefixWord ++ tailWord_4918382).sum := by decide
  have hdescent : baseEnd_4918382 < baseStart_4918382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918392 : List Nat := [2, 1, 2, 1, 1, 1, 4, 5, 1, 3, 2]
def baseStart_4918392 : Nat := 118140960795 + 4918392 * 2 ^ 59
def prefixEnd_4918392 : Nat := 4983230072969 + 3 ^ 40 * 4918392 * 2
def baseEnd_4918392 : Nat := 2525499143228426002380733

theorem tailTrace_4918392 : CollatzResearch.WordTrace tailWord_4918392 prefixEnd_4918392 2525499143228426002380733 := by
  unfold tailWord_4918392
  simp only [CollatzResearch.WordTrace]
  refine ⟨89694246798756626661666715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119592329065008835548888953 89694246798756626661666715)
  ·
    refine ⟨134541370198134939992500073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89694246798756626661666715 134541370198134939992500073)
    ·
      refine ⟨100906027648601204994375055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134541370198134939992500073 100906027648601204994375055)
      ·
        refine ⟨151359041472901807491562583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100906027648601204994375055 151359041472901807491562583)
        ·
          refine ⟨227038562209352711237343875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151359041472901807491562583 227038562209352711237343875)
          ·
            refine ⟨340557843314029066856015813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227038562209352711237343875 340557843314029066856015813)
            ·
              refine ⟨63854595621380450035502965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 340557843314029066856015813 63854595621380450035502965)
              ·
                refine ⟨5986368339504417190828403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63854595621380450035502965 5986368339504417190828403)
                ·
                  refine ⟨8979552509256625786242605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5986368339504417190828403 8979552509256625786242605)
                  ·
                    refine ⟨3367332190971234669840977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8979552509256625786242605 3367332190971234669840977)
                    ·
                      refine ⟨2525499143228426002380733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3367332190971234669840977 2525499143228426002380733)
                      ·
                        rfl

theorem cell23_4918392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 1, 3, 2].length) (baseStart_4918392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918392 prefixEnd_4918392 := by exact prefixLift 4918392
  have htrace : WordTrace (prefixWord ++ tailWord_4918392) baseStart_4918392 baseEnd_4918392 := by
    simpa [prefixWord, tailWord_4918392, baseEnd_4918392] using wordTrace_append hprefix tailTrace_4918392
  have hstable : (prefixWord ++ tailWord_4918392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918392).length < 2 ^ (prefixWord ++ tailWord_4918392).sum := by decide
  have hdescent : baseEnd_4918392 < baseStart_4918392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918439 : List Nat := [1, 1, 6, 2, 1, 1, 2, 2, 1, 4, 2]
def baseStart_4918439 : Nat := 118140960795 + 4918439 * 2 ^ 59
def prefixEnd_4918439 : Nat := 4983230072969 + 3 ^ 40 * 4918439 * 2
def baseEnd_4918439 : Nat := 2525523276819187318493017

theorem tailTrace_4918439 : CollatzResearch.WordTrace tailWord_4918439 prefixEnd_4918439 2525523276819187318493017 := by
  unfold tailWord_4918439
  simp only [CollatzResearch.WordTrace]
  refine ⟨179390207828342980350294371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119593471885561986900196247 179390207828342980350294371)
  ·
    refine ⟨269085311742514470525441557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179390207828342980350294371 269085311742514470525441557)
    ·
      refine ⟨12613373987930365805880073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 269085311742514470525441557 12613373987930365805880073)
      ·
        refine ⟨9460030490947774354410055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12613373987930365805880073 9460030490947774354410055)
        ·
          refine ⟨14190045736421661531615083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9460030490947774354410055 14190045736421661531615083)
          ·
            refine ⟨21285068604632492297422625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14190045736421661531615083 21285068604632492297422625)
            ·
              refine ⟨15963801453474369223066969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21285068604632492297422625 15963801453474369223066969)
              ·
                refine ⟨11972851090105776917300227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15963801453474369223066969 11972851090105776917300227)
                ·
                  refine ⟨17959276635158665375950341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11972851090105776917300227 17959276635158665375950341)
                  ·
                    refine ⟨3367364369092249757990689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17959276635158665375950341 3367364369092249757990689)
                    ·
                      refine ⟨2525523276819187318493017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3367364369092249757990689 2525523276819187318493017)
                      ·
                        rfl

theorem cell23_4918439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_4918439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918439 prefixEnd_4918439 := by exact prefixLift 4918439
  have htrace : WordTrace (prefixWord ++ tailWord_4918439) baseStart_4918439 baseEnd_4918439 := by
    simpa [prefixWord, tailWord_4918439, baseEnd_4918439] using wordTrace_append hprefix tailTrace_4918439
  have hstable : (prefixWord ++ tailWord_4918439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918439).length < 2 ^ (prefixWord ++ tailWord_4918439).sum := by decide
  have hdescent : baseEnd_4918439 < baseStart_4918439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918455 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 3]
def baseStart_4918455 : Nat := 118140960795 + 4918455 * 2 ^ 59
def prefixEnd_4918455 : Nat := 4983230072969 + 3 ^ 40 * 4918455 * 2
def baseEnd_4918455 : Nat := 2525531492509659255892943

theorem tailTrace_4918455 : CollatzResearch.WordTrace tailWord_4918455 prefixEnd_4918455 2525531492509659255892943 := by
  unfold tailWord_4918455
  simp only [CollatzResearch.WordTrace]
  refine ⟨179390791396285015082876819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119593860930856676721917879 179390791396285015082876819)
  ·
    refine ⟨269086187094427522624315229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179390791396285015082876819 269086187094427522624315229)
    ·
      refine ⟨100907320160410320984118211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269086187094427522624315229 100907320160410320984118211)
      ·
        refine ⟨151360980240615481476177317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100907320160410320984118211 151360980240615481476177317)
        ·
          refine ⟨28380183795115402776783247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151360980240615481476177317 28380183795115402776783247)
          ·
            refine ⟨42570275692673104165174871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28380183795115402776783247 42570275692673104165174871)
            ·
              refine ⟨63855413539009656247762307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42570275692673104165174871 63855413539009656247762307)
              ·
                refine ⟨95783120308514484371643461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63855413539009656247762307 95783120308514484371643461)
                ·
                  refine ⟨17959335057846465819683149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95783120308514484371643461 17959335057846465819683149)
                  ·
                    refine ⟨6734750646692424682381181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17959335057846465819683149 6734750646692424682381181)
                    ·
                      refine ⟨2525531492509659255892943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6734750646692424682381181 2525531492509659255892943)
                      ·
                        rfl

theorem cell23_4918455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 3].length) (baseStart_4918455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918455 prefixEnd_4918455 := by exact prefixLift 4918455
  have htrace : WordTrace (prefixWord ++ tailWord_4918455) baseStart_4918455 baseEnd_4918455 := by
    simpa [prefixWord, tailWord_4918455, baseEnd_4918455] using wordTrace_append hprefix tailTrace_4918455
  have hstable : (prefixWord ++ tailWord_4918455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918455).length < 2 ^ (prefixWord ++ tailWord_4918455).sum := by decide
  have hdescent : baseEnd_4918455 < baseStart_4918455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918462 : List Nat := [4, 2, 1, 1, 3, 2, 2, 1, 7]
def baseStart_4918462 : Nat := 118140960795 + 4918462 * 2 ^ 59
def prefixEnd_4918462 : Nat := 4983230072969 + 3 ^ 40 * 4918462 * 2
def baseEnd_4918462 : Nat := 280615009652693414278379

theorem tailTrace_4918462 : CollatzResearch.WordTrace tailWord_4918462 prefixEnd_4918462 280615009652693414278379 := by
  unfold tailWord_4918462
  simp only [CollatzResearch.WordTrace]
  refine ⟨22423880838407456909797705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119594031138173103518921093 22423880838407456909797705)
  ·
    refine ⟨16817910628805592682348279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22423880838407456909797705 16817910628805592682348279)
    ·
      refine ⟨25226865943208389023522419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16817910628805592682348279 25226865943208389023522419)
      ·
        refine ⟨37840298914812583535283629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25226865943208389023522419 37840298914812583535283629)
        ·
          refine ⟨14190112093054718825731361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37840298914812583535283629 14190112093054718825731361)
          ·
            refine ⟨10642584069791039119298521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14190112093054718825731361 10642584069791039119298521)
            ·
              refine ⟨7981938052343279339473891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10642584069791039119298521 7981938052343279339473891)
              ·
                refine ⟨11972907078514919009210837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7981938052343279339473891 11972907078514919009210837)
                ·
                  refine ⟨280615009652693414278379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11972907078514919009210837 280615009652693414278379)
                  ·
                    rfl

theorem cell23_4918462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_4918462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918462 prefixEnd_4918462 := by exact prefixLift 4918462
  have htrace : WordTrace (prefixWord ++ tailWord_4918462) baseStart_4918462 baseEnd_4918462 := by
    simpa [prefixWord, tailWord_4918462, baseEnd_4918462] using wordTrace_append hprefix tailTrace_4918462
  have hstable : (prefixWord ++ tailWord_4918462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918462).length < 2 ^ (prefixWord ++ tailWord_4918462).sum := by decide
  have hdescent : baseEnd_4918462 < baseStart_4918462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918495 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 4]
def baseStart_4918495 : Nat := 118140960795 + 4918495 * 2 ^ 59
def prefixEnd_4918495 : Nat := 4983230072969 + 3 ^ 40 * 4918495 * 2
def baseEnd_4918495 : Nat := 2525552031735839099392759

theorem tailTrace_4918495 : CollatzResearch.WordTrace tailWord_4918495 prefixEnd_4918495 2525552031735839099392759 := by
  unfold tailWord_4918495
  simp only [CollatzResearch.WordTrace]
  refine ⟨179392250316140101914332939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119594833544093401276221959 179392250316140101914332939)
  ·
    refine ⟨269088375474210152871499409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179392250316140101914332939 269088375474210152871499409)
    ·
      refine ⟨201816281605657614653624557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269088375474210152871499409 201816281605657614653624557)
      ·
        refine ⟨75681105602121605495109209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201816281605657614653624557 75681105602121605495109209)
        ·
          refine ⟨56760829201591204121331907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75681105602121605495109209 56760829201591204121331907)
          ·
            refine ⟨85141243802386806181997861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56760829201591204121331907 85141243802386806181997861)
            ·
              refine ⟨15963983212947526159124599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85141243802386806181997861 15963983212947526159124599)
              ·
                refine ⟨23945974819421289238686899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15963983212947526159124599 23945974819421289238686899)
                ·
                  refine ⟨35918962229131933858030349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23945974819421289238686899 35918962229131933858030349)
                  ·
                    refine ⟨13469610835924475196761381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35918962229131933858030349 13469610835924475196761381)
                    ·
                      refine ⟨2525552031735839099392759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13469610835924475196761381 2525552031735839099392759)
                      ·
                        rfl

theorem cell23_4918495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_4918495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918495 prefixEnd_4918495 := by exact prefixLift 4918495
  have htrace : WordTrace (prefixWord ++ tailWord_4918495) baseStart_4918495 baseEnd_4918495 := by
    simpa [prefixWord, tailWord_4918495, baseEnd_4918495] using wordTrace_append hprefix tailTrace_4918495
  have hstable : (prefixWord ++ tailWord_4918495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918495).length < 2 ^ (prefixWord ++ tailWord_4918495).sum := by decide
  have hdescent : baseEnd_4918495 < baseStart_4918495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918572 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 3, 5, 2]
def baseStart_4918572 : Nat := 118140960795 + 4918572 * 2 ^ 59
def prefixEnd_4918572 : Nat := 4983230072969 + 3 ^ 40 * 4918572 * 2
def baseEnd_4918572 : Nat := 2525591569746235298129905

theorem tailTrace_4918572 : CollatzResearch.WordTrace tailWord_4918572 prefixEnd_4918572 2525591569746235298129905 := by
  unfold tailWord_4918572
  simp only [CollatzResearch.WordTrace]
  refine ⟨89697529368430572032442985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119596705824574096043257313 89697529368430572032442985)
  ·
    refine ⟨67273147026322929024332239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89697529368430572032442985 67273147026322929024332239)
    ·
      refine ⟨100909720539484393536498359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67273147026322929024332239 100909720539484393536498359)
      ·
        refine ⟨151364580809226590304747539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100909720539484393536498359 151364580809226590304747539)
        ·
          refine ⟨227046871213839885457121309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151364580809226590304747539 227046871213839885457121309)
          ·
            refine ⟨85142576705189957046420491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227046871213839885457121309 85142576705189957046420491)
            ·
              refine ⟨127713865057784935569630737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85142576705189957046420491 127713865057784935569630737)
              ·
                refine ⟨95785398793338701677223053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127713865057784935569630737 95785398793338701677223053)
                ·
                  refine ⟨35919524547502013128958645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95785398793338701677223053 35919524547502013128958645)
                  ·
                    refine ⟨3367455426328313730839873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35919524547502013128958645 3367455426328313730839873)
                    ·
                      refine ⟨2525591569746235298129905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3367455426328313730839873 2525591569746235298129905)
                      ·
                        rfl

theorem cell23_4918572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 5, 2].length) (baseStart_4918572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918572 prefixEnd_4918572 := by exact prefixLift 4918572
  have htrace : WordTrace (prefixWord ++ tailWord_4918572) baseStart_4918572 baseEnd_4918572 := by
    simpa [prefixWord, tailWord_4918572, baseEnd_4918572] using wordTrace_append hprefix tailTrace_4918572
  have hstable : (prefixWord ++ tailWord_4918572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918572).length < 2 ^ (prefixWord ++ tailWord_4918572).sum := by decide
  have hdescent : baseEnd_4918572 < baseStart_4918572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918573 : List Nat := [1, 5, 3, 1, 1, 2, 1, 4, 1, 4]
def baseStart_4918573 : Nat := 118140960795 + 4918573 * 2 ^ 59
def prefixEnd_4918573 : Nat := 4983230072969 + 3 ^ 40 * 4918573 * 2
def baseEnd_4918573 : Nat := 841864027742296598072467

theorem tailTrace_4918573 : CollatzResearch.WordTrace tailWord_4918573 prefixEnd_4918573 841864027742296598072467 := by
  unfold tailWord_4918573
  simp only [CollatzResearch.WordTrace]
  refine ⟨179395095209857521235672373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119596730139905014157114915 179395095209857521235672373)
  ·
    refine ⟨16818290175924142615844285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 179395095209857521235672373 16818290175924142615844285)
    ·
      refine ⟨6306858815971553480941607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16818290175924142615844285 6306858815971553480941607)
      ·
        refine ⟨9460288223957330221412411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6306858815971553480941607 9460288223957330221412411)
        ·
          refine ⟨14190432335935995332118617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9460288223957330221412411 14190432335935995332118617)
          ·
            refine ⟨10642824251951996499088963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14190432335935995332118617 10642824251951996499088963)
            ·
              refine ⟨15964236377927994748633445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10642824251951996499088963 15964236377927994748633445)
              ·
                refine ⟨2993294320861499015368771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15964236377927994748633445 2993294320861499015368771)
                ·
                  refine ⟨4489941481292248523053157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2993294320861499015368771 4489941481292248523053157)
                  ·
                    refine ⟨841864027742296598072467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4489941481292248523053157 841864027742296598072467)
                    ·
                      rfl

theorem cell23_4918573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_4918573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918573 prefixEnd_4918573 := by exact prefixLift 4918573
  have htrace : WordTrace (prefixWord ++ tailWord_4918573) baseStart_4918573 baseEnd_4918573 := by
    simpa [prefixWord, tailWord_4918573, baseEnd_4918573] using wordTrace_append hprefix tailTrace_4918573
  have hstable : (prefixWord ++ tailWord_4918573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918573).length < 2 ^ (prefixWord ++ tailWord_4918573).sum := by decide
  have hdescent : baseEnd_4918573 < baseStart_4918573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918596 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_4918596 : Nat := 118140960795 + 4918596 * 2 ^ 59
def prefixEnd_4918596 : Nat := 4983230072969 + 3 ^ 40 * 4918596 * 2
def baseEnd_4918596 : Nat := 2525603893281943204229795

theorem tailTrace_4918596 : CollatzResearch.WordTrace tailWord_4918596 prefixEnd_4918596 2525603893281943204229795 := by
  unfold tailWord_4918596
  simp only [CollatzResearch.WordTrace]
  refine ⟨89697967044387098081879821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119597289392516130775839761 89697967044387098081879821)
  ·
    refine ⟨33636737641645161780704933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89697967044387098081879821 33636737641645161780704933)
    ·
      refine ⟨6306888307808467833882175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33636737641645161780704933 6306888307808467833882175)
      ·
        refine ⟨9460332461712701750823263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6306888307808467833882175 9460332461712701750823263)
        ·
          refine ⟨14190498692569052626234895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9460332461712701750823263 14190498692569052626234895)
          ·
            refine ⟨21285748038853578939352343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14190498692569052626234895 21285748038853578939352343)
            ·
              refine ⟨31928622058280368409028515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21285748038853578939352343 31928622058280368409028515)
              ·
                refine ⟨47892933087420552613542773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31928622058280368409028515 47892933087420552613542773)
                ·
                  refine ⟨4489962476945676807519635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47892933087420552613542773 4489962476945676807519635)
                  ·
                    refine ⟨6734943715418515211279453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4489962476945676807519635 6734943715418515211279453)
                    ·
                      refine ⟨2525603893281943204229795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6734943715418515211279453 2525603893281943204229795)
                      ·
                        rfl

theorem cell23_4918596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_4918596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918596 prefixEnd_4918596 := by exact prefixLift 4918596
  have htrace : WordTrace (prefixWord ++ tailWord_4918596) baseStart_4918596 baseEnd_4918596 := by
    simpa [prefixWord, tailWord_4918596, baseEnd_4918596] using wordTrace_append hprefix tailTrace_4918596
  have hstable : (prefixWord ++ tailWord_4918596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918596).length < 2 ^ (prefixWord ++ tailWord_4918596).sum := by decide
  have hdescent : baseEnd_4918596 < baseStart_4918596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918612 : List Nat := [2, 4, 1, 1, 2, 1, 1, 4, 1, 6]
def baseStart_4918612 : Nat := 118140960795 + 4918612 * 2 ^ 59
def prefixEnd_4918612 : Nat := 4983230072969 + 3 ^ 40 * 4918612 * 2
def baseEnd_4918612 : Nat := 841870702990805047209907

theorem tailTrace_4918612 : CollatzResearch.WordTrace tailWord_4918612 prefixEnd_4918612 841870702990805047209907 := by
  unfold tailWord_4918612
  simp only [CollatzResearch.WordTrace]
  refine ⟨89698258828358115448171045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119597678437810820597561393 89698258828358115448171045)
  ·
    refine ⟨16818423530317146646532071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89698258828358115448171045 16818423530317146646532071)
    ·
      refine ⟨25227635295475719969798107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16818423530317146646532071 25227635295475719969798107)
      ·
        refine ⟨37841452943213579954697161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25227635295475719969798107 37841452943213579954697161)
        ·
          refine ⟨28381089707410184966022871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37841452943213579954697161 28381089707410184966022871)
          ·
            refine ⟨42571634561115277449034307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28381089707410184966022871 42571634561115277449034307)
            ·
              refine ⟨63857451841672916173551461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42571634561115277449034307 63857451841672916173551461)
              ·
                refine ⟨11973272220313671782540899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63857451841672916173551461 11973272220313671782540899)
                ·
                  refine ⟨17959908330470507673811349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11973272220313671782540899 17959908330470507673811349)
                  ·
                    refine ⟨841870702990805047209907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17959908330470507673811349 841870702990805047209907)
                    ·
                      rfl

theorem cell23_4918612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_4918612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918612 prefixEnd_4918612 := by exact prefixLift 4918612
  have htrace : WordTrace (prefixWord ++ tailWord_4918612) baseStart_4918612 baseEnd_4918612 := by
    simpa [prefixWord, tailWord_4918612, baseEnd_4918612] using wordTrace_append hprefix tailTrace_4918612
  have hstable : (prefixWord ++ tailWord_4918612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918612).length < 2 ^ (prefixWord ++ tailWord_4918612).sum := by decide
  have hdescent : baseEnd_4918612 < baseStart_4918612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918613 : List Nat := [1, 3, 2, 2, 3, 2, 2, 3, 1, 1, 3]
def baseStart_4918613 : Nat := 118140960795 + 4918613 * 2 ^ 59
def prefixEnd_4918613 : Nat := 4983230072969 + 3 ^ 40 * 4918613 * 2
def baseEnd_4918613 : Nat := 2525612622453069637717217

theorem tailTrace_4918613 : CollatzResearch.WordTrace tailWord_4918613 prefixEnd_4918613 2525612622453069637717217 := by
  unfold tailWord_4918613
  simp only [CollatzResearch.WordTrace]
  refine ⟨179396554129712608067128493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119597702753141738711418995 179396554129712608067128493)
  ·
    refine ⟨67273707798642228025173185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179396554129712608067128493 67273707798642228025173185)
    ·
      refine ⟨50455280848981671018879889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67273707798642228025173185 50455280848981671018879889)
      ·
        refine ⟨37841460636736253264159917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50455280848981671018879889 37841460636736253264159917)
        ·
          refine ⟨14190547738776094974059969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37841460636736253264159917 14190547738776094974059969)
          ·
            refine ⟨10642910804082071230544977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14190547738776094974059969 10642910804082071230544977)
            ·
              refine ⟨7982183103061553422908733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10642910804082071230544977 7982183103061553422908733)
              ·
                refine ⟨2993318663648082533590775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7982183103061553422908733 2993318663648082533590775)
                ·
                  refine ⟨4489977995472123800386163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2993318663648082533590775 4489977995472123800386163)
                  ·
                    refine ⟨6734966993208185700579245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4489977995472123800386163 6734966993208185700579245)
                    ·
                      refine ⟨2525612622453069637717217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6734966993208185700579245 2525612622453069637717217)
                      ·
                        rfl

theorem cell23_4918613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_4918613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918613 prefixEnd_4918613 := by exact prefixLift 4918613
  have htrace : WordTrace (prefixWord ++ tailWord_4918613) baseStart_4918613 baseEnd_4918613 := by
    simpa [prefixWord, tailWord_4918613, baseEnd_4918613] using wordTrace_append hprefix tailTrace_4918613
  have hstable : (prefixWord ++ tailWord_4918613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918613).length < 2 ^ (prefixWord ++ tailWord_4918613).sum := by decide
  have hdescent : baseEnd_4918613 < baseStart_4918613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918636 : List Nat := [2, 2, 1, 1, 5, 1, 1, 3, 3, 2, 2]
def baseStart_4918636 : Nat := 118140960795 + 4918636 * 2 ^ 59
def prefixEnd_4918636 : Nat := 4983230072969 + 3 ^ 40 * 4918636 * 2
def baseEnd_4918636 : Nat := 2525624432508123047729611

theorem tailTrace_4918636 : CollatzResearch.WordTrace tailWord_4918636 prefixEnd_4918636 2525624432508123047729611 := by
  unfold tailWord_4918636
  simp only [CollatzResearch.WordTrace]
  refine ⟨89698696504314641497607881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119598262005752855330143841 89698696504314641497607881)
  ·
    refine ⟨67274022378235981123205911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89698696504314641497607881 67274022378235981123205911)
    ·
      refine ⟨100911033567353971684808867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67274022378235981123205911 100911033567353971684808867)
      ·
        refine ⟨151366550351030957527213301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100911033567353971684808867 151366550351030957527213301)
        ·
          refine ⟨14190614095409152268176247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 151366550351030957527213301 14190614095409152268176247)
          ·
            refine ⟨21285921143113728402264371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14190614095409152268176247 21285921143113728402264371)
            ·
              refine ⟨31928881714670592603396557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21285921143113728402264371 31928881714670592603396557)
              ·
                refine ⟨11973330643001472226273709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31928881714670592603396557 11973330643001472226273709)
                ·
                  refine ⟨4489998991125552084852641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11973330643001472226273709 4489998991125552084852641)
                  ·
                    refine ⟨3367499243344164063639481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4489998991125552084852641 3367499243344164063639481)
                    ·
                      refine ⟨2525624432508123047729611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3367499243344164063639481 2525624432508123047729611)
                      ·
                        rfl

theorem cell23_4918636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 2, 2].length) (baseStart_4918636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918636 prefixEnd_4918636 := by exact prefixLift 4918636
  have htrace : WordTrace (prefixWord ++ tailWord_4918636) baseStart_4918636 baseEnd_4918636 := by
    simpa [prefixWord, tailWord_4918636, baseEnd_4918636] using wordTrace_append hprefix tailTrace_4918636
  have hstable : (prefixWord ++ tailWord_4918636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918636).length < 2 ^ (prefixWord ++ tailWord_4918636).sum := by decide
  have hdescent : baseEnd_4918636 < baseStart_4918636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918659 : List Nat := [1, 1, 1, 3, 5, 3, 2, 7]
def baseStart_4918659 : Nat := 118140960795 + 4918659 * 2 ^ 59
def prefixEnd_4918659 : Nat := 4983230072969 + 3 ^ 40 * 4918659 * 2
def baseEnd_4918659 : Nat := 93542083057895424360815

theorem tailTrace_4918659 : CollatzResearch.WordTrace tailWord_4918659 prefixEnd_4918659 93542083057895424360815 := by
  unfold tailWord_4918659
  simp only [CollatzResearch.WordTrace]
  refine ⟨179398231887545957923303031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119598821258363971948868687 179398231887545957923303031)
  ·
    refine ⟨269097347831318936884954547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179398231887545957923303031 269097347831318936884954547)
    ·
      refine ⟨403646021746978405327431821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269097347831318936884954547 403646021746978405327431821)
      ·
        refine ⟨151367258155116901997786933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 403646021746978405327431821 151367258155116901997786933)
        ·
          refine ⟨14190680452042209562292525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 151367258155116901997786933 14190680452042209562292525)
          ·
            refine ⟨5321505169515828585859697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14190680452042209562292525 5321505169515828585859697)
            ·
              refine ⟨3991128877136871439394773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5321505169515828585859697 3991128877136871439394773)
              ·
                refine ⟨93542083057895424360815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3991128877136871439394773 93542083057895424360815)
                ·
                  rfl

theorem cell23_4918659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 7].length) (baseStart_4918659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918659 prefixEnd_4918659 := by exact prefixLift 4918659
  have htrace : WordTrace (prefixWord ++ tailWord_4918659) baseStart_4918659 baseEnd_4918659 := by
    simpa [prefixWord, tailWord_4918659, baseEnd_4918659] using wordTrace_append hprefix tailTrace_4918659
  have hstable : (prefixWord ++ tailWord_4918659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918659).length < 2 ^ (prefixWord ++ tailWord_4918659).sum := by decide
  have hdescent : baseEnd_4918659 < baseStart_4918659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918675 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 8]
def baseStart_4918675 : Nat := 118140960795 + 4918675 * 2 ^ 59
def prefixEnd_4918675 : Nat := 4983230072969 + 3 ^ 40 * 4918675 * 2
def baseEnd_4918675 : Nat := 2525644458253648395141931

theorem tailTrace_4918675 : CollatzResearch.WordTrace tailWord_4918675 prefixEnd_4918675 2525644458253648395141931 := by
  unfold tailWord_4918675
  simp only [CollatzResearch.WordTrace]
  refine ⟨179398815455487992655885479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119599210303658661770590319 179398815455487992655885479)
  ·
    refine ⟨269098223183231988983828219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179398815455487992655885479 269098223183231988983828219)
    ·
      refine ⟨403647334774847983475742329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269098223183231988983828219 403647334774847983475742329)
      ·
        refine ⟨302735501081135987606806747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 403647334774847983475742329 302735501081135987606806747)
        ·
          refine ⟨454103251621703981410210121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302735501081135987606806747 454103251621703981410210121)
          ·
            refine ⟨340577438716277986057657591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 454103251621703981410210121 340577438716277986057657591)
            ·
              refine ⟨510866158074416979086486387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340577438716277986057657591 510866158074416979086486387)
              ·
                refine ⟨766299237111625468629729581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510866158074416979086486387 766299237111625468629729581)
                ·
                  refine ⟨287362213916859550736148593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 766299237111625468629729581 287362213916859550736148593)
                  ·
                    refine ⟨215521660437644663052111445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 287362213916859550736148593 215521660437644663052111445)
                    ·
                      refine ⟨2525644458253648395141931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 215521660437644663052111445 2525644458253648395141931)
                      ·
                        rfl

theorem cell23_4918675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_4918675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918675 prefixEnd_4918675 := by exact prefixLift 4918675
  have htrace : WordTrace (prefixWord ++ tailWord_4918675) baseStart_4918675 baseEnd_4918675 := by
    simpa [prefixWord, tailWord_4918675, baseEnd_4918675] using wordTrace_append hprefix tailTrace_4918675
  have hstable : (prefixWord ++ tailWord_4918675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918675).length < 2 ^ (prefixWord ++ tailWord_4918675).sum := by decide
  have hdescent : baseEnd_4918675 < baseStart_4918675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918679 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 5, 3, 2]
def baseStart_4918679 : Nat := 118140960795 + 4918679 * 2 ^ 59
def prefixEnd_4918679 : Nat := 4983230072969 + 3 ^ 40 * 4918679 * 2
def baseEnd_4918679 : Nat := 2525646512176266379491913

theorem tailTrace_4918679 : CollatzResearch.WordTrace tailWord_4918679 prefixEnd_4918679 2525646512176266379491913 := by
  unfold tailWord_4918679
  simp only [CollatzResearch.WordTrace]
  refine ⟨179398961347473501339031091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119599307564982334226020727 179398961347473501339031091)
  ·
    refine ⟨269098442021210252008546637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179398961347473501339031091 269098442021210252008546637)
    ·
      refine ⟨100911915757953844503204989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269098442021210252008546637 100911915757953844503204989)
      ·
        refine ⟨37841968409232691688701871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100911915757953844503204989 37841968409232691688701871)
        ·
          refine ⟨56762952613849037533052807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37841968409232691688701871 56762952613849037533052807)
          ·
            refine ⟨85144428920773556299579211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56762952613849037533052807 85144428920773556299579211)
            ·
              refine ⟨127716643381160334449368817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85144428920773556299579211 127716643381160334449368817)
              ·
                refine ⟨95787482535870250837026613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127716643381160334449368817 95787482535870250837026613)
                ·
                  refine ⟨8980076487737836015971245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95787482535870250837026613 8980076487737836015971245)
                  ·
                    refine ⟨3367528682901688505989217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8980076487737836015971245 3367528682901688505989217)
                    ·
                      refine ⟨2525646512176266379491913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3367528682901688505989217 2525646512176266379491913)
                      ·
                        rfl

theorem cell23_4918679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_4918679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918679 prefixEnd_4918679 := by exact prefixLift 4918679
  have htrace : WordTrace (prefixWord ++ tailWord_4918679) baseStart_4918679 baseEnd_4918679 := by
    simpa [prefixWord, tailWord_4918679, baseEnd_4918679] using wordTrace_append hprefix tailTrace_4918679
  have hstable : (prefixWord ++ tailWord_4918679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918679).length < 2 ^ (prefixWord ++ tailWord_4918679).sum := by decide
  have hdescent : baseEnd_4918679 < baseStart_4918679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918682 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5]
def baseStart_4918682 : Nat := 118140960795 + 4918682 * 2 ^ 59
def prefixEnd_4918682 : Nat := 4983230072969 + 3 ^ 40 * 4918682 * 2
def baseEnd_4918682 : Nat := 2525648052618229867754399

theorem tailTrace_4918682 : CollatzResearch.WordTrace tailWord_4918682 prefixEnd_4918682 2525648052618229867754399 := by
  unfold tailWord_4918682
  simp only [CollatzResearch.WordTrace]
  refine ⟨44849767691615658212847575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119599380510975088567593533 44849767691615658212847575)
  ·
    refine ⟨67274651537423487319271363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44849767691615658212847575 67274651537423487319271363)
    ·
      refine ⟨100911977306135230978907045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67274651537423487319271363 100911977306135230978907045)
      ·
        refine ⟨18920995744900355808545071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100911977306135230978907045 18920995744900355808545071)
        ·
          refine ⟨28381493617350533712817607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18920995744900355808545071 28381493617350533712817607)
          ·
            refine ⟨42572240426025800569226411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28381493617350533712817607 42572240426025800569226411)
            ·
              refine ⟨63858360639038700853839617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42572240426025800569226411 63858360639038700853839617)
              ·
                refine ⟨47893770479279025640379713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63858360639038700853839617 47893770479279025640379713)
                ·
                  refine ⟨35920327859459269230284785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47893770479279025640379713 35920327859459269230284785)
                  ·
                    refine ⟨26940245894594451922713589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35920327859459269230284785 26940245894594451922713589)
                    ·
                      refine ⟨2525648052618229867754399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26940245894594451922713589 2525648052618229867754399)
                      ·
                        rfl

theorem cell23_4918682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_4918682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918682 prefixEnd_4918682 := by exact prefixLift 4918682
  have htrace : WordTrace (prefixWord ++ tailWord_4918682) baseStart_4918682 baseEnd_4918682 := by
    simpa [prefixWord, tailWord_4918682, baseEnd_4918682] using wordTrace_append hprefix tailTrace_4918682
  have hstable : (prefixWord ++ tailWord_4918682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918682).length < 2 ^ (prefixWord ++ tailWord_4918682).sum := by decide
  have hdescent : baseEnd_4918682 < baseStart_4918682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918692 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 2, 3, 4]
def baseStart_4918692 : Nat := 118140960795 + 4918692 * 2 ^ 59
def prefixEnd_4918692 : Nat := 4983230072969 + 3 ^ 40 * 4918692 * 2
def baseEnd_4918692 : Nat := 2525653187424774828629353

theorem tailTrace_4918692 : CollatzResearch.WordTrace tailWord_4918692 prefixEnd_4918692 2525653187424774828629353 := by
  unfold tailWord_4918692
  simp only [CollatzResearch.WordTrace]
  refine ⟨89699717748213202279627165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119599623664284269706169553 89699717748213202279627165)
  ·
    refine ⟨33637394155579950854860187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89699717748213202279627165 33637394155579950854860187)
    ·
      refine ⟨50456091233369926282290281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33637394155579950854860187 50456091233369926282290281)
      ·
        refine ⟨37842068425027444711717711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50456091233369926282290281 37842068425027444711717711)
        ·
          refine ⟨56763102637541167067576567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37842068425027444711717711 56763102637541167067576567)
          ·
            refine ⟨85144653956311750601364851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56763102637541167067576567 85144653956311750601364851)
            ·
              refine ⟨127716980934467625902047277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85144653956311750601364851 127716980934467625902047277)
              ·
                refine ⟨47893867850425359713267729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127716980934467625902047277 47893867850425359713267729)
                ·
                  refine ⟨35920400887819019784950797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47893867850425359713267729 35920400887819019784950797)
                  ·
                    refine ⟨13470150332932132419356549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35920400887819019784950797 13470150332932132419356549)
                    ·
                      refine ⟨2525653187424774828629353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13470150332932132419356549 2525653187424774828629353)
                      ·
                        rfl

theorem cell23_4918692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_4918692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918692 prefixEnd_4918692 := by exact prefixLift 4918692
  have htrace : WordTrace (prefixWord ++ tailWord_4918692) baseStart_4918692 baseEnd_4918692 := by
    simpa [prefixWord, tailWord_4918692, baseEnd_4918692] using wordTrace_append hprefix tailTrace_4918692
  have hstable : (prefixWord ++ tailWord_4918692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918692).length < 2 ^ (prefixWord ++ tailWord_4918692).sum := by decide
  have hdescent : baseEnd_4918692 < baseStart_4918692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918712 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 2, 1, 5]
def baseStart_4918712 : Nat := 118140960795 + 4918712 * 2 ^ 59
def prefixEnd_4918712 : Nat := 4983230072969 + 3 ^ 40 * 4918712 * 2
def baseEnd_4918712 : Nat := 2525663457037864750379261

theorem tailTrace_4918712 : CollatzResearch.WordTrace tailWord_4918712 prefixEnd_4918712 2525663457037864750379261 := by
  unfold tailWord_4918712
  simp only [CollatzResearch.WordTrace]
  refine ⟨89700082478176973987491195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119600109970902631983321593 89700082478176973987491195)
  ·
    refine ⟨134550123717265460981236793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89700082478176973987491195 134550123717265460981236793)
    ·
      refine ⟨100912592787949095735927595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134550123717265460981236793 100912592787949095735927595)
      ·
        refine ⟨151368889181923643603891393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100912592787949095735927595 151368889181923643603891393)
        ·
          refine ⟨113526666886442732702918545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151368889181923643603891393 113526666886442732702918545)
          ·
            refine ⟨85145000164832049527188909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113526666886442732702918545 85145000164832049527188909)
            ·
              refine ⟨31929375061812018572695841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85145000164832049527188909 31929375061812018572695841)
              ·
                refine ⟨23947031296359013929521881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31929375061812018572695841 23947031296359013929521881)
                ·
                  refine ⟨17960273472269260447141411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23947031296359013929521881 17960273472269260447141411)
                  ·
                    refine ⟨26940410208403890670712117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17960273472269260447141411 26940410208403890670712117)
                    ·
                      refine ⟨2525663457037864750379261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26940410208403890670712117 2525663457037864750379261)
                      ·
                        rfl

theorem cell23_4918712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_4918712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918712 prefixEnd_4918712 := by exact prefixLift 4918712
  have htrace : WordTrace (prefixWord ++ tailWord_4918712) baseStart_4918712 baseEnd_4918712 := by
    simpa [prefixWord, tailWord_4918712, baseEnd_4918712] using wordTrace_append hprefix tailTrace_4918712
  have hstable : (prefixWord ++ tailWord_4918712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918712).length < 2 ^ (prefixWord ++ tailWord_4918712).sum := by decide
  have hdescent : baseEnd_4918712 < baseStart_4918712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918759 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 3]
def baseStart_4918759 : Nat := 118140960795 + 4918759 * 2 ^ 59
def prefixEnd_4918759 : Nat := 4983230072969 + 3 ^ 40 * 4918759 * 2
def baseEnd_4918759 : Nat := 2525687590628626066491545

theorem tailTrace_4918759 : CollatzResearch.WordTrace tailWord_4918759 prefixEnd_4918759 2525687590628626066491545 := by
  unfold tailWord_4918759
  simp only [CollatzResearch.WordTrace]
  refine ⟨179401879187183675001943331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119601252791455783334628887 179401879187183675001943331)
  ·
    refine ⟨269102818780775512502914997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179401879187183675001943331 269102818780775512502914997)
    ·
      refine ⟨25228389260697704297148281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 269102818780775512502914997 25228389260697704297148281)
      ·
        refine ⟨18921291945523278222861211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25228389260697704297148281 18921291945523278222861211)
        ·
          refine ⟨28381937918284917334291817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18921291945523278222861211 28381937918284917334291817)
          ·
            refine ⟨21286453438713688000718863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28381937918284917334291817 21286453438713688000718863)
            ·
              refine ⟨31929680158070532001078295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21286453438713688000718863 31929680158070532001078295)
              ·
                refine ⟨47894520237105798001617443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31929680158070532001078295 47894520237105798001617443)
                ·
                  refine ⟨71841780355658697002426165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47894520237105798001617443 71841780355658697002426165)
                  ·
                    refine ⟨6735166908343002843977453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71841780355658697002426165 6735166908343002843977453)
                    ·
                      refine ⟨2525687590628626066491545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6735166908343002843977453 2525687590628626066491545)
                      ·
                        rfl

theorem cell23_4918759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_4918759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918759 prefixEnd_4918759 := by exact prefixLift 4918759
  have htrace : WordTrace (prefixWord ++ tailWord_4918759) baseStart_4918759 baseEnd_4918759 := by
    simpa [prefixWord, tailWord_4918759, baseEnd_4918759] using wordTrace_append hprefix tailTrace_4918759
  have hstable : (prefixWord ++ tailWord_4918759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918759).length < 2 ^ (prefixWord ++ tailWord_4918759).sum := by decide
  have hdescent : baseEnd_4918759 < baseStart_4918759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918826 : List Nat := [3, 1, 4, 1, 1, 1, 1, 4, 3, 4]
def baseStart_4918826 : Nat := 118140960795 + 4918826 * 2 ^ 59
def prefixEnd_4918826 : Nat := 4983230072969 + 3 ^ 40 * 4918826 * 2
def baseEnd_4918826 : Nat := 841907331277492434784579

theorem tailTrace_4918826 : CollatzResearch.WordTrace tailWord_4918826 prefixEnd_4918826 841907331277492434784579 := by
  unfold tailWord_4918826
  simp only [CollatzResearch.WordTrace]
  refine ⟨44851080719485236361158083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119602881918627296963088221 44851080719485236361158083)
  ·
    refine ⟨67276621079227854541737125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44851080719485236361158083 67276621079227854541737125)
    ·
      refine ⟨12614366452355222726575711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67276621079227854541737125 12614366452355222726575711)
      ·
        refine ⟨18921549678532834089863567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12614366452355222726575711 18921549678532834089863567)
        ·
          refine ⟨28382324517799251134795351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18921549678532834089863567 28382324517799251134795351)
          ·
            refine ⟨42573486776698876702193027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28382324517799251134795351 42573486776698876702193027)
            ·
              refine ⟨63860230165048315053289541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42573486776698876702193027 63860230165048315053289541)
              ·
                refine ⟨11973793155946559072491789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63860230165048315053289541 11973793155946559072491789)
                ·
                  refine ⟨4490172433479959652184421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11973793155946559072491789 4490172433479959652184421)
                  ·
                    refine ⟨841907331277492434784579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4490172433479959652184421 841907331277492434784579)
                    ·
                      rfl

theorem cell23_4918826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_4918826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918826 prefixEnd_4918826 := by exact prefixLift 4918826
  have htrace : WordTrace (prefixWord ++ tailWord_4918826) baseStart_4918826 baseEnd_4918826 := by
    simpa [prefixWord, tailWord_4918826, baseEnd_4918826] using wordTrace_append hprefix tailTrace_4918826
  have hstable : (prefixWord ++ tailWord_4918826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918826).length < 2 ^ (prefixWord ++ tailWord_4918826).sum := by decide
  have hdescent : baseEnd_4918826 < baseStart_4918826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918860 : List Nat := [2, 2, 1, 3, 1, 4, 3, 2, 1, 4]
def baseStart_4918860 : Nat := 118140960795 + 4918860 * 2 ^ 59
def prefixEnd_4918860 : Nat := 4983230072969 + 3 ^ 40 * 4918860 * 2
def baseEnd_4918860 : Nat := 841913150724910057109527

theorem tailTrace_4918860 : CollatzResearch.WordTrace tailWord_4918860 prefixEnd_4918860 841913150724910057109527 := by
  unfold tailWord_4918860
  simp only [CollatzResearch.WordTrace]
  refine ⟨89702781479908884625685017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119603708639878512834246689 89702781479908884625685017)
  ·
    refine ⟨67277086109931663469263763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89702781479908884625685017 67277086109931663469263763)
    ·
      refine ⟨100915629164897495203895645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67277086109931663469263763 100915629164897495203895645)
      ·
        refine ⟨37843360936836560701460867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100915629164897495203895645 37843360936836560701460867)
        ·
          refine ⟨56765041405254841052191301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37843360936836560701460867 56765041405254841052191301)
          ·
            refine ⟨10643445263485282697285869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56765041405254841052191301 10643445263485282697285869)
            ·
              refine ⟨3991291973806981011482201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10643445263485282697285869 3991291973806981011482201)
              ·
                refine ⟨2993468980355235758611651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3991291973806981011482201 2993468980355235758611651)
                ·
                  refine ⟨4490203470532853637917477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2993468980355235758611651 4490203470532853637917477)
                  ·
                    refine ⟨841913150724910057109527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4490203470532853637917477 841913150724910057109527)
                    ·
                      rfl

theorem cell23_4918860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 1, 4].length) (baseStart_4918860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918860 prefixEnd_4918860 := by exact prefixLift 4918860
  have htrace : WordTrace (prefixWord ++ tailWord_4918860) baseStart_4918860 baseEnd_4918860 := by
    simpa [prefixWord, tailWord_4918860, baseEnd_4918860] using wordTrace_append hprefix tailTrace_4918860
  have hstable : (prefixWord ++ tailWord_4918860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918860).length < 2 ^ (prefixWord ++ tailWord_4918860).sum := by decide
  have hdescent : baseEnd_4918860 < baseStart_4918860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918869 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 3, 5]
def baseStart_4918869 : Nat := 118140960795 + 4918869 * 2 ^ 59
def prefixEnd_4918869 : Nat := 4983230072969 + 3 ^ 40 * 4918869 * 2
def baseEnd_4918869 : Nat := 841914691166873545372013

theorem tailTrace_4918869 : CollatzResearch.WordTrace tailWord_4918869 prefixEnd_4918869 841914691166873545372013 := by
  unfold tailWord_4918869
  simp only [CollatzResearch.WordTrace]
  refine ⟨179405891216785163788447661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119603927477856775858965107 179405891216785163788447661)
  ·
    refine ⟨67277209206294436420667873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179405891216785163788447661 67277209206294436420667873)
    ·
      refine ⟨50457906904720827315500905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67277209206294436420667873 50457906904720827315500905)
      ·
        refine ⟨37843430178540620486625679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50457906904720827315500905 37843430178540620486625679)
        ·
          refine ⟨56765145267810930729938519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37843430178540620486625679 56765145267810930729938519)
          ·
            refine ⟨85147717901716396094907779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56765145267810930729938519 85147717901716396094907779)
            ·
              refine ⟨127721576852574594142361669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85147717901716396094907779 127721576852574594142361669)
              ·
                refine ⟨23947795659857736401692813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127721576852574594142361669 23947795659857736401692813)
                ·
                  refine ⟨8980423372446651150634805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23947795659857736401692813 8980423372446651150634805)
                  ·
                    refine ⟨841914691166873545372013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8980423372446651150634805 841914691166873545372013)
                    ·
                      rfl

theorem cell23_4918869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_4918869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918869 prefixEnd_4918869 := by exact prefixLift 4918869
  have htrace : WordTrace (prefixWord ++ tailWord_4918869) baseStart_4918869 baseEnd_4918869 := by
    simpa [prefixWord, tailWord_4918869, baseEnd_4918869] using wordTrace_append hprefix tailTrace_4918869
  have hstable : (prefixWord ++ tailWord_4918869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918869).length < 2 ^ (prefixWord ++ tailWord_4918869).sum := by decide
  have hdescent : baseEnd_4918869 < baseStart_4918869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918923 : List Nat := [1, 1, 1, 1, 4, 1, 4, 3, 3, 2, 2]
def baseStart_4918923 : Nat := 118140960795 + 4918923 * 2 ^ 59
def prefixEnd_4918923 : Nat := 4983230072969 + 3 ^ 40 * 4918923 * 2
def baseEnd_4918923 : Nat := 2525771801455963424840791

theorem tailTrace_4918923 : CollatzResearch.WordTrace tailWord_4918923 prefixEnd_4918923 2525771801455963424840791 := by
  unfold tailWord_4918923
  simp only [CollatzResearch.WordTrace]
  refine ⟨179407860758589531010913423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119605240505726354007275615 179407860758589531010913423)
  ·
    refine ⟨269111791137884296516370135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179407860758589531010913423 269111791137884296516370135)
    ·
      refine ⟨403667686706826444774555203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269111791137884296516370135 403667686706826444774555203)
      ·
        refine ⟨605501530060239667161832805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403667686706826444774555203 605501530060239667161832805)
        ·
          refine ⟨113531536886294937592843651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 605501530060239667161832805 113531536886294937592843651)
          ·
            refine ⟨170297305329442406389265477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113531536886294937592843651 170297305329442406389265477)
            ·
              refine ⟨31930744749270451197987277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170297305329442406389265477 31930744749270451197987277)
              ·
                refine ⟨11974029280976419199245229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31930744749270451197987277 11974029280976419199245229)
                ·
                  refine ⟨4490260980366157199716961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11974029280976419199245229 4490260980366157199716961)
                  ·
                    refine ⟨3367695735274617899787721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4490260980366157199716961 3367695735274617899787721)
                    ·
                      refine ⟨2525771801455963424840791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3367695735274617899787721 2525771801455963424840791)
                      ·
                        rfl

theorem cell23_4918923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 2, 2].length) (baseStart_4918923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918923 prefixEnd_4918923 := by exact prefixLift 4918923
  have htrace : WordTrace (prefixWord ++ tailWord_4918923) baseStart_4918923 baseEnd_4918923 := by
    simpa [prefixWord, tailWord_4918923, baseEnd_4918923] using wordTrace_append hprefix tailTrace_4918923
  have hstable : (prefixWord ++ tailWord_4918923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918923).length < 2 ^ (prefixWord ++ tailWord_4918923).sum := by decide
  have hdescent : baseEnd_4918923 < baseStart_4918923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918936 : List Nat := [2, 1, 2, 4, 1, 2, 1, 3, 1, 2, 4]
def baseStart_4918936 : Nat := 118140960795 + 4918936 * 2 ^ 59
def prefixEnd_4918936 : Nat := 4983230072969 + 3 ^ 40 * 4918936 * 2
def baseEnd_4918936 : Nat := 2525778476704471873978231

theorem tailTrace_4918936 : CollatzResearch.WordTrace tailWord_4918936 prefixEnd_4918936 2525778476704471873978231 := by
  unfold tailWord_4918936
  simp only [CollatzResearch.WordTrace]
  refine ⟨89704167453771217115568331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119605556605028289487424441 89704167453771217115568331)
  ·
    refine ⟨134556251180656825673352497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89704167453771217115568331 134556251180656825673352497)
    ·
      refine ⟨100917188385492619255014373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134556251180656825673352497 100917188385492619255014373)
      ·
        refine ⟨18921972822279866110315195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100917188385492619255014373 18921972822279866110315195)
        ·
          refine ⟨28382959233419799165472793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18921972822279866110315195 28382959233419799165472793)
          ·
            refine ⟨21287219425064849374104595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28382959233419799165472793 21287219425064849374104595)
            ·
              refine ⟨31930829137597274061156893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21287219425064849374104595 31930829137597274061156893)
              ·
                refine ⟨11974060926598977772933835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31930829137597274061156893 11974060926598977772933835)
                ·
                  refine ⟨17961091389898466659400753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11974060926598977772933835 17961091389898466659400753)
                  ·
                    refine ⟨13470818542423849994550565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17961091389898466659400753 13470818542423849994550565)
                    ·
                      refine ⟨2525778476704471873978231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13470818542423849994550565 2525778476704471873978231)
                      ·
                        rfl

theorem cell23_4918936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_4918936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918936 prefixEnd_4918936 := by exact prefixLift 4918936
  have htrace : WordTrace (prefixWord ++ tailWord_4918936) baseStart_4918936 baseEnd_4918936 := by
    simpa [prefixWord, tailWord_4918936, baseEnd_4918936] using wordTrace_append hprefix tailTrace_4918936
  have hstable : (prefixWord ++ tailWord_4918936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918936).length < 2 ^ (prefixWord ++ tailWord_4918936).sum := by decide
  have hdescent : baseEnd_4918936 < baseStart_4918936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918939 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 3]
def baseStart_4918939 : Nat := 118140960795 + 4918939 * 2 ^ 59
def prefixEnd_4918939 : Nat := 4983230072969 + 3 ^ 40 * 4918939 * 2
def baseEnd_4918939 : Nat := 2525780017146435362240717

theorem tailTrace_4918939 : CollatzResearch.WordTrace tailWord_4918939 prefixEnd_4918939 2525780017146435362240717 := by
  unfold tailWord_4918939
  simp only [CollatzResearch.WordTrace]
  refine ⟨179408444326531565743495871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119605629551021043828997247 179408444326531565743495871)
  ·
    refine ⟨269112666489797348615243807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179408444326531565743495871 269112666489797348615243807)
    ·
      refine ⟨403668999734696022922865711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269112666489797348615243807 403668999734696022922865711)
      ·
        refine ⟨605503499602044034384298567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403668999734696022922865711 605503499602044034384298567)
        ·
          refine ⟨908255249403066051576447851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605503499602044034384298567 908255249403066051576447851)
          ·
            refine ⟨1362382874104599077364671777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 908255249403066051576447851 1362382874104599077364671777)
            ·
              refine ⟨1021787155578449308023503833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1362382874104599077364671777 1021787155578449308023503833)
              ·
                refine ⟨766340366683836981017627875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1021787155578449308023503833 766340366683836981017627875)
                ·
                  refine ⟨1149510550025755471526441813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 766340366683836981017627875 1149510550025755471526441813)
                  ·
                    refine ⟨6735413379057160965975245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1149510550025755471526441813 6735413379057160965975245)
                    ·
                      refine ⟨2525780017146435362240717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6735413379057160965975245 2525780017146435362240717)
                      ·
                        rfl

theorem cell23_4918939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 3].length) (baseStart_4918939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918939 prefixEnd_4918939 := by exact prefixLift 4918939
  have htrace : WordTrace (prefixWord ++ tailWord_4918939) baseStart_4918939 baseEnd_4918939 := by
    simpa [prefixWord, tailWord_4918939, baseEnd_4918939] using wordTrace_append hprefix tailTrace_4918939
  have hstable : (prefixWord ++ tailWord_4918939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918939).length < 2 ^ (prefixWord ++ tailWord_4918939).sum := by decide
  have hdescent : baseEnd_4918939 < baseStart_4918939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4918973 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 4, 1, 3]
def baseStart_4918973 : Nat := 118140960795 + 4918973 * 2 ^ 59
def prefixEnd_4918973 : Nat := 4983230072969 + 3 ^ 40 * 4918973 * 2
def baseEnd_4918973 : Nat := 2525797475488688229215561

theorem tailTrace_4918973 : CollatzResearch.WordTrace tailWord_4918973 prefixEnd_4918973 2525797475488688229215561 := by
  unfold tailWord_4918973
  simp only [CollatzResearch.WordTrace]
  refine ⟨179409684408408389550233573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119606456272272259700155715 179409684408408389550233573)
  ·
    refine ⟨33639315826576573040668795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179409684408408389550233573 33639315826576573040668795)
    ·
      refine ⟨50458973739864859561003193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33639315826576573040668795 50458973739864859561003193)
      ·
        refine ⟨37844230304898644670752395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50458973739864859561003193 37844230304898644670752395)
        ·
          refine ⟨56766345457347967006128593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37844230304898644670752395 56766345457347967006128593)
          ·
            refine ⟨42574759093010975254596445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56766345457347967006128593 42574759093010975254596445)
            ·
              refine ⟨15965534659879115720473667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42574759093010975254596445 15965534659879115720473667)
              ·
                refine ⟨23948301989818673580710501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15965534659879115720473667 23948301989818673580710501)
                ·
                  refine ⟨4490306623091001296383219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23948301989818673580710501 4490306623091001296383219)
                  ·
                    refine ⟨6735459934636501944574829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4490306623091001296383219 6735459934636501944574829)
                    ·
                      refine ⟨2525797475488688229215561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6735459934636501944574829 2525797475488688229215561)
                      ·
                        rfl

theorem cell23_4918973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_4918973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4918973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4918973 prefixEnd_4918973 := by exact prefixLift 4918973
  have htrace : WordTrace (prefixWord ++ tailWord_4918973) baseStart_4918973 baseEnd_4918973 := by
    simpa [prefixWord, tailWord_4918973, baseEnd_4918973] using wordTrace_append hprefix tailTrace_4918973
  have hstable : (prefixWord ++ tailWord_4918973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4918973).length < 2 ^ (prefixWord ++ tailWord_4918973).sum := by decide
  have hdescent : baseEnd_4918973 < baseStart_4918973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4918973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919000 : List Nat := [2, 1, 2, 2, 3, 1, 4, 2, 1, 3, 2]
def baseStart_4919000 : Nat := 118140960795 + 4919000 * 2 ^ 59
def prefixEnd_4919000 : Nat := 4983230072969 + 3 ^ 40 * 4919000 * 2
def baseEnd_4919000 : Nat := 2525811339466359623577937

theorem tailTrace_4919000 : CollatzResearch.WordTrace tailWord_4919000 prefixEnd_4919000 2525811339466359623577937 := by
  unfold tailWord_4919000
  simp only [CollatzResearch.WordTrace]
  refine ⟨89705334589655286580733227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119607112786207048774310969 89705334589655286580733227)
  ·
    refine ⟨134558001884482929871099841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89705334589655286580733227 134558001884482929871099841)
    ·
      refine ⟨100918501413362197403324881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134558001884482929871099841 100918501413362197403324881)
      ·
        refine ⟨75688876060021648052493661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100918501413362197403324881 75688876060021648052493661)
        ·
          refine ⟨28383328522508118019685123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75688876060021648052493661 28383328522508118019685123)
          ·
            refine ⟨42574992783762177029527685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28383328522508118019685123 42574992783762177029527685)
            ·
              refine ⟨7982811146955408193036441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42574992783762177029527685 7982811146955408193036441)
              ·
                refine ⟨5987108360216556144777331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7982811146955408193036441 5987108360216556144777331)
                ·
                  refine ⟨8980662540324834217165997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5987108360216556144777331 8980662540324834217165997)
                  ·
                    refine ⟨3367748452621812831437249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8980662540324834217165997 3367748452621812831437249)
                    ·
                      refine ⟨2525811339466359623577937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3367748452621812831437249 2525811339466359623577937)
                      ·
                        rfl

theorem cell23_4919000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 1, 3, 2].length) (baseStart_4919000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919000 prefixEnd_4919000 := by exact prefixLift 4919000
  have htrace : WordTrace (prefixWord ++ tailWord_4919000) baseStart_4919000 baseEnd_4919000 := by
    simpa [prefixWord, tailWord_4919000, baseEnd_4919000] using wordTrace_append hprefix tailTrace_4919000
  have hstable : (prefixWord ++ tailWord_4919000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919000).length < 2 ^ (prefixWord ++ tailWord_4919000).sum := by decide
  have hdescent : baseEnd_4919000 < baseStart_4919000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919013 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 3, 4, 2]
def baseStart_4919013 : Nat := 118140960795 + 4919013 * 2 ^ 59
def prefixEnd_4919013 : Nat := 4983230072969 + 3 ^ 40 * 4919013 * 2
def baseEnd_4919013 : Nat := 2525818014714868072715377

theorem tailTrace_4919013 : CollatzResearch.WordTrace tailWord_4919013 prefixEnd_4919013 2525818014714868072715377 := by
  unfold tailWord_4919013
  simp only [CollatzResearch.WordTrace]
  refine ⟨179411143328263476381689693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119607428885508984254459795 179411143328263476381689693)
  ·
    refine ⟨67279178748098803643133635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179411143328263476381689693 67279178748098803643133635)
    ·
      refine ⟨100918768122148205464700453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67279178748098803643133635 100918768122148205464700453)
      ·
        refine ⟨18922269022902788524631335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100918768122148205464700453 18922269022902788524631335)
        ·
          refine ⟨28383403534354182786947003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18922269022902788524631335 28383403534354182786947003)
          ·
            refine ⟨42575105301531274180420505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28383403534354182786947003 42575105301531274180420505)
            ·
              refine ⟨31931328976148455635315379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42575105301531274180420505 31931328976148455635315379)
              ·
                refine ⟨47896993464222683452973069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31931328976148455635315379 47896993464222683452973069)
                ·
                  refine ⟨17961372549083506294864901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47896993464222683452973069 17961372549083506294864901)
                  ·
                    refine ⟨3367757352953157430287169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17961372549083506294864901 3367757352953157430287169)
                    ·
                      refine ⟨2525818014714868072715377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3367757352953157430287169 2525818014714868072715377)
                      ·
                        rfl

theorem cell23_4919013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_4919013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919013 prefixEnd_4919013 := by exact prefixLift 4919013
  have htrace : WordTrace (prefixWord ++ tailWord_4919013) baseStart_4919013 baseEnd_4919013 := by
    simpa [prefixWord, tailWord_4919013, baseEnd_4919013] using wordTrace_append hprefix tailTrace_4919013
  have hstable : (prefixWord ++ tailWord_4919013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919013).length < 2 ^ (prefixWord ++ tailWord_4919013).sum := by decide
  have hdescent : baseEnd_4919013 < baseStart_4919013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919016 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_4919016 : Nat := 118140960795 + 4919016 * 2 ^ 59
def prefixEnd_4919016 : Nat := 4983230072969 + 3 ^ 40 * 4919016 * 2
def baseEnd_4919016 : Nat := 2525819555156831560977863

theorem tailTrace_4919016 : CollatzResearch.WordTrace tailWord_4919016 prefixEnd_4919016 2525819555156831560977863 := by
  unfold tailWord_4919016
  simp only [CollatzResearch.WordTrace]
  refine ⟨89705626373626303947024451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119607501831501738596032601 89705626373626303947024451)
  ·
    refine ⟨134558439560439455920536677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89705626373626303947024451 134558439560439455920536677)
    ·
      refine ⟨25229707417582397985100627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134558439560439455920536677 25229707417582397985100627)
      ·
        refine ⟨37844561126373596977650941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25229707417582397985100627 37844561126373596977650941)
        ·
          refine ⟨14191710422390098866619103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37844561126373596977650941 14191710422390098866619103)
          ·
            refine ⟨21287565633585148299928655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14191710422390098866619103 21287565633585148299928655)
            ·
              refine ⟨31931348450377722449892983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21287565633585148299928655 31931348450377722449892983)
              ·
                refine ⟨47897022675566583674839475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31931348450377722449892983 47897022675566583674839475)
                ·
                  refine ⟨71845534013349875512259213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47897022675566583674839475 71845534013349875512259213)
                  ·
                    refine ⟨26942075255006203317097205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71845534013349875512259213 26942075255006203317097205)
                    ·
                      refine ⟨2525819555156831560977863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26942075255006203317097205 2525819555156831560977863)
                      ·
                        rfl

theorem cell23_4919016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_4919016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919016 prefixEnd_4919016 := by exact prefixLift 4919016
  have htrace : WordTrace (prefixWord ++ tailWord_4919016) baseStart_4919016 baseEnd_4919016 := by
    simpa [prefixWord, tailWord_4919016, baseEnd_4919016] using wordTrace_append hprefix tailTrace_4919016
  have hstable : (prefixWord ++ tailWord_4919016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919016).length < 2 ^ (prefixWord ++ tailWord_4919016).sum := by decide
  have hdescent : baseEnd_4919016 < baseStart_4919016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919019 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 9]
def baseStart_4919019 : Nat := 118140960795 + 4919019 * 2 ^ 59
def prefixEnd_4919019 : Nat := 4983230072969 + 3 ^ 40 * 4919019 * 2
def baseEnd_4919019 : Nat := 280646788399866116582261

theorem tailTrace_4919019 : CollatzResearch.WordTrace tailWord_4919019 prefixEnd_4919019 280646788399866116582261 := by
  unfold tailWord_4919019
  simp only [CollatzResearch.WordTrace]
  refine ⟨179411362166241739406408111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119607574777494492937605407 179411362166241739406408111)
  ·
    refine ⟨269117043249362609109612167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179411362166241739406408111 269117043249362609109612167)
    ·
      refine ⟨403675564874043913664418251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269117043249362609109612167 403675564874043913664418251)
      ·
        refine ⟨605513347311065870496627377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403675564874043913664418251 605513347311065870496627377)
        ·
          refine ⟨454135010483299402872470533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 605513347311065870496627377 454135010483299402872470533)
          ·
            refine ⟨85150314465618638038588225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 454135010483299402872470533 85150314465618638038588225)
            ·
              refine ⟨63862735849213978528941169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85150314465618638038588225 63862735849213978528941169)
              ·
                refine ⟨47897051886910483896705877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63862735849213978528941169 47897051886910483896705877)
                ·
                  refine ⟨280646788399866116582261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47897051886910483896705877 280646788399866116582261)
                  ·
                    rfl

theorem cell23_4919019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 9].length) (baseStart_4919019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919019 prefixEnd_4919019 := by exact prefixLift 4919019
  have htrace : WordTrace (prefixWord ++ tailWord_4919019) baseStart_4919019 baseEnd_4919019 := by
    simpa [prefixWord, tailWord_4919019, baseEnd_4919019] using wordTrace_append hprefix tailTrace_4919019
  have hstable : (prefixWord ++ tailWord_4919019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919019).length < 2 ^ (prefixWord ++ tailWord_4919019).sum := by decide
  have hdescent : baseEnd_4919019 < baseStart_4919019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919113 : List Nat := [1, 2, 1, 1, 2, 4, 3, 2, 3, 4]
def baseStart_4919113 : Nat := 118140960795 + 4919113 * 2 ^ 59
def prefixEnd_4919113 : Nat := 4983230072969 + 3 ^ 40 * 4919113 * 2
def baseEnd_4919113 : Nat := 841956454260105893821639

theorem tailTrace_4919113 : CollatzResearch.WordTrace tailWord_4919113 prefixEnd_4919113 841956454260105893821639 := by
  unfold tailWord_4919113
  simp only [CollatzResearch.WordTrace]
  refine ⟨179414790627901193460329993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119609860418600795640219995 179414790627901193460329993)
  ·
    refine ⟨134561092970925895095247495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179414790627901193460329993 134561092970925895095247495)
    ·
      refine ⟨201841639456388842642871243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134561092970925895095247495 201841639456388842642871243)
      ·
        refine ⟨302762459184583263964306865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201841639456388842642871243 302762459184583263964306865)
        ·
          refine ⟨227071844388437447973230149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302762459184583263964306865 227071844388437447973230149)
          ·
            refine ⟨42575970822832021494980653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 227071844388437447973230149 42575970822832021494980653)
            ·
              refine ⟨15965989058562008060617745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42575970822832021494980653 15965989058562008060617745)
              ·
                refine ⟨11974491793921506045463309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15965989058562008060617745 11974491793921506045463309)
                ·
                  refine ⟨4490434422720564767048741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11974491793921506045463309 4490434422720564767048741)
                  ·
                    refine ⟨841956454260105893821639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4490434422720564767048741 841956454260105893821639)
                    ·
                      rfl

theorem cell23_4919113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 4].length) (baseStart_4919113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919113 prefixEnd_4919113 := by exact prefixLift 4919113
  have htrace : WordTrace (prefixWord ++ tailWord_4919113) baseStart_4919113 baseEnd_4919113 := by
    simpa [prefixWord, tailWord_4919113, baseEnd_4919113] using wordTrace_append hprefix tailTrace_4919113
  have hstable : (prefixWord ++ tailWord_4919113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919113).length < 2 ^ (prefixWord ++ tailWord_4919113).sum := by decide
  have hdescent : baseEnd_4919113 < baseStart_4919113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919117 : List Nat := [1, 6, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_4919117 : Nat := 118140960795 + 4919117 * 2 ^ 59
def prefixEnd_4919117 : Nat := 4983230072969 + 3 ^ 40 * 4919117 * 2
def baseEnd_4919117 : Nat := 841957138900978555271633

theorem tailTrace_4919117 : CollatzResearch.WordTrace tailWord_4919117 prefixEnd_4919117 841957138900978555271633 := by
  unfold tailWord_4919117
  simp only [CollatzResearch.WordTrace]
  refine ⟨179414936519886702143475605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119609957679924468095650403 179414936519886702143475605)
  ·
    refine ⟨8410075149369689162975419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 179414936519886702143475605 8410075149369689162975419)
    ·
      refine ⟨12615112724054533744463129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8410075149369689162975419 12615112724054533744463129)
      ·
        refine ⟨9461334543040900308347347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12615112724054533744463129 9461334543040900308347347)
        ·
          refine ⟨14192001814561350462521021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9461334543040900308347347 14192001814561350462521021)
          ·
            refine ⟨5322000680460506423445383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14192001814561350462521021 5322000680460506423445383)
            ·
              refine ⟨7983001020690759635168075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5322000680460506423445383 7983001020690759635168075)
              ·
                refine ⟨11974501531036139452752113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7983001020690759635168075 11974501531036139452752113)
                ·
                  refine ⟨8980876148277104589564085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11974501531036139452752113 8980876148277104589564085)
                  ·
                    refine ⟨841957138900978555271633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8980876148277104589564085 841957138900978555271633)
                    ·
                      rfl

theorem cell23_4919117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_4919117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919117 prefixEnd_4919117 := by exact prefixLift 4919117
  have htrace : WordTrace (prefixWord ++ tailWord_4919117) baseStart_4919117 baseEnd_4919117 := by
    simpa [prefixWord, tailWord_4919117, baseEnd_4919117] using wordTrace_append hprefix tailTrace_4919117
  have hstable : (prefixWord ++ tailWord_4919117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919117).length < 2 ^ (prefixWord ++ tailWord_4919117).sum := by decide
  have hdescent : baseEnd_4919117 < baseStart_4919117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919180 : List Nat := [2, 2, 1, 2, 1, 2, 1, 5, 2, 3, 2]
def baseStart_4919180 : Nat := 118140960795 + 4919180 * 2 ^ 59
def prefixEnd_4919180 : Nat := 4983230072969 + 3 ^ 40 * 4919180 * 2
def baseEnd_4919180 : Nat := 2525903765984168919327109

theorem tailTrace_4919180 : CollatzResearch.WordTrace tailWord_4919180 prefixEnd_4919180 2525903765984168919327109 := by
  unfold tailWord_4919180
  simp only [CollatzResearch.WordTrace]
  refine ⟨89708617159329231951509497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119611489545772309268679329 89708617159329231951509497)
  ·
    refine ⟨67281462869496923963632123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89708617159329231951509497 67281462869496923963632123)
    ·
      refine ⟨100922194304245385945448185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67281462869496923963632123 100922194304245385945448185)
      ·
        refine ⟨75691645728184039459086139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100922194304245385945448185 75691645728184039459086139)
        ·
          refine ⟨113537468592276059188629209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75691645728184039459086139 113537468592276059188629209)
          ·
            refine ⟨85153101444207044391471907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113537468592276059188629209 85153101444207044391471907)
            ·
              refine ⟨127729652166310566587207861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85153101444207044391471907 127729652166310566587207861)
              ·
                refine ⟨11974654890591615617550737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127729652166310566587207861 11974654890591615617550737)
                ·
                  refine ⟨8980991167943711713163053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11974654890591615617550737 8980991167943711713163053)
                  ·
                    refine ⟨3367871687978891892436145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8980991167943711713163053 3367871687978891892436145)
                    ·
                      refine ⟨2525903765984168919327109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3367871687978891892436145 2525903765984168919327109)
                      ·
                        rfl

theorem cell23_4919180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 2, 3, 2].length) (baseStart_4919180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919180 prefixEnd_4919180 := by exact prefixLift 4919180
  have htrace : WordTrace (prefixWord ++ tailWord_4919180) baseStart_4919180 baseEnd_4919180 := by
    simpa [prefixWord, tailWord_4919180, baseEnd_4919180] using wordTrace_append hprefix tailTrace_4919180
  have hstable : (prefixWord ++ tailWord_4919180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919180).length < 2 ^ (prefixWord ++ tailWord_4919180).sum := by decide
  have hdescent : baseEnd_4919180 < baseStart_4919180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919197 : List Nat := [1, 4, 2, 1, 2, 3, 1, 2, 2, 3, 2]
def baseStart_4919197 : Nat := 118140960795 + 4919197 * 2 ^ 59
def prefixEnd_4919197 : Nat := 4983230072969 + 3 ^ 40 * 4919197 * 2
def baseEnd_4919197 : Nat := 2525912495155295352814531

theorem tailTrace_4919197 : CollatzResearch.WordTrace tailWord_4919197 prefixEnd_4919197 2525912495155295352814531 := by
  unfold tailWord_4919197
  simp only [CollatzResearch.WordTrace]
  refine ⟨179417854359596875806387845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119611902906397917204258563 179417854359596875806387845)
  ·
    refine ⟨33640847692424414213697721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179417854359596875806387845 33640847692424414213697721)
    ·
      refine ⟨25230635769318310660273291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33640847692424414213697721 25230635769318310660273291)
      ·
        refine ⟨37845953653977465990409937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25230635769318310660273291 37845953653977465990409937)
        ·
          refine ⟨28384465240483099492807453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37845953653977465990409937 28384465240483099492807453)
          ·
            refine ⟨10644174465181162309802795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28384465240483099492807453 10644174465181162309802795)
            ·
              refine ⟨15966261697771743464704193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10644174465181162309802795 15966261697771743464704193)
              ·
                refine ⟨11974696273328807598528145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15966261697771743464704193 11974696273328807598528145)
                ·
                  refine ⟨8981022204996605698896109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11974696273328807598528145 8981022204996605698896109)
                  ·
                    refine ⟨3367883326873727137086041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8981022204996605698896109 3367883326873727137086041)
                    ·
                      refine ⟨2525912495155295352814531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3367883326873727137086041 2525912495155295352814531)
                      ·
                        rfl

theorem cell23_4919197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_4919197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919197 prefixEnd_4919197 := by exact prefixLift 4919197
  have htrace : WordTrace (prefixWord ++ tailWord_4919197) baseStart_4919197 baseEnd_4919197 := by
    simpa [prefixWord, tailWord_4919197, baseEnd_4919197] using wordTrace_append hprefix tailTrace_4919197
  have hstable : (prefixWord ++ tailWord_4919197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919197).length < 2 ^ (prefixWord ++ tailWord_4919197).sum := by decide
  have hdescent : baseEnd_4919197 < baseStart_4919197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919198 : List Nat := [4, 3, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_4919198 : Nat := 118140960795 + 4919198 * 2 ^ 59
def prefixEnd_4919198 : Nat := 4983230072969 + 3 ^ 40 * 4919198 * 2
def baseEnd_4919198 : Nat := 841971002878649949634009

theorem tailTrace_4919198 : CollatzResearch.WordTrace tailWord_4919198 prefixEnd_4919198 841971002878649949634009 := by
  unfold tailWord_4919198
  simp only [CollatzResearch.WordTrace]
  refine ⟨22427236354074156622146781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119611927221728835318116165 22427236354074156622146781)
  ·
    refine ⟨8410213632777808733305043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22427236354074156622146781 8410213632777808733305043)
    ·
      refine ⟨12615320449166713099957565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8410213632777808733305043 12615320449166713099957565)
      ·
        refine ⟨4730745168437517412484087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12615320449166713099957565 4730745168437517412484087)
        ·
          refine ⟨7096117752656276118726131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4730745168437517412484087 7096117752656276118726131)
          ·
            refine ⟨10644176628984414178089197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7096117752656276118726131 10644176628984414178089197)
            ·
              refine ⟨3991566235869155316783449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10644176628984414178089197 3991566235869155316783449)
              ·
                refine ⟨2993674676901866487587587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3991566235869155316783449 2993674676901866487587587)
                ·
                  refine ⟨4490512015352799731381381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2993674676901866487587587 4490512015352799731381381)
                  ·
                    refine ⟨841971002878649949634009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4490512015352799731381381 841971002878649949634009)
                    ·
                      rfl

theorem cell23_4919198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_4919198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919198 prefixEnd_4919198 := by exact prefixLift 4919198
  have htrace : WordTrace (prefixWord ++ tailWord_4919198) baseStart_4919198 baseEnd_4919198 := by
    simpa [prefixWord, tailWord_4919198, baseEnd_4919198] using wordTrace_append hprefix tailTrace_4919198
  have hstable : (prefixWord ++ tailWord_4919198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919198).length < 2 ^ (prefixWord ++ tailWord_4919198).sum := by decide
  have hdescent : baseEnd_4919198 < baseStart_4919198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919223 : List Nat := [1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 4]
def baseStart_4919223 : Nat := 118140960795 + 4919223 * 2 ^ 59
def prefixEnd_4919223 : Nat := 4983230072969 + 3 ^ 40 * 4919223 * 2
def baseEnd_4919223 : Nat := 2525925845652312251089411

theorem tailTrace_4919223 : CollatzResearch.WordTrace tailWord_4919223 prefixEnd_4919223 2525925845652312251089411 := by
  unfold tailWord_4919223
  simp only [CollatzResearch.WordTrace]
  refine ⟨179418802657502682246834323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119612535105001788164556215 179418802657502682246834323)
  ·
    refine ⟨269128203986254023370251485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179418802657502682246834323 269128203986254023370251485)
    ·
      refine ⟨100923076494845258763844307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269128203986254023370251485 100923076494845258763844307)
      ·
        refine ⟨151384614742267888145766461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100923076494845258763844307 151384614742267888145766461)
        ·
          refine ⟨56769230528350458054662423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151384614742267888145766461 56769230528350458054662423)
          ·
            refine ⟨85153845792525687081993635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56769230528350458054662423 85153845792525687081993635)
            ·
              refine ⟨127730768688788530622990453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85153845792525687081993635 127730768688788530622990453)
              ·
                refine ⟨11974759564573924745905355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127730768688788530622990453 11974759564573924745905355)
                ·
                  refine ⟨17962139346860887118858033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11974759564573924745905355 17962139346860887118858033)
                  ·
                    refine ⟨13471604510145665339143525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17962139346860887118858033 13471604510145665339143525)
                    ·
                      refine ⟨2525925845652312251089411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13471604510145665339143525 2525925845652312251089411)
                      ·
                        rfl

theorem cell23_4919223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_4919223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919223 prefixEnd_4919223 := by exact prefixLift 4919223
  have htrace : WordTrace (prefixWord ++ tailWord_4919223) baseStart_4919223 baseEnd_4919223 := by
    simpa [prefixWord, tailWord_4919223, baseEnd_4919223] using wordTrace_append hprefix tailTrace_4919223
  have hstable : (prefixWord ++ tailWord_4919223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919223).length < 2 ^ (prefixWord ++ tailWord_4919223).sum := by decide
  have hdescent : baseEnd_4919223 < baseStart_4919223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919240 : List Nat := [2, 1, 3, 1, 4, 2, 1, 2, 1, 2, 4]
def baseStart_4919240 : Nat := 118140960795 + 4919240 * 2 ^ 59
def prefixEnd_4919240 : Nat := 4983230072969 + 3 ^ 40 * 4919240 * 2
def baseEnd_4919240 : Nat := 2525934574823438684576833

theorem tailTrace_4919240 : CollatzResearch.WordTrace tailWord_4919240 prefixEnd_4919240 2525934574823438684576833 := by
  unfold tailWord_4919240
  simp only [CollatzResearch.WordTrace]
  refine ⟨89709711349220547075101587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119612948465627396100135449 89709711349220547075101587)
  ·
    refine ⟨134564567023830820612652381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89709711349220547075101587 134564567023830820612652381)
    ·
      refine ⟨50461712633936557729744643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134564567023830820612652381 50461712633936557729744643)
      ·
        refine ⟨75692568950904836594616965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50461712633936557729744643 75692568950904836594616965)
        ·
          refine ⟨14192356678294656861490681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75692568950904836594616965 14192356678294656861490681)
          ·
            refine ⟨10644267508720992646118011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14192356678294656861490681 10644267508720992646118011)
            ·
              refine ⟨15966401263081488969177017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10644267508720992646118011 15966401263081488969177017)
              ·
                refine ⟨11974800947311116726882763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15966401263081488969177017 11974800947311116726882763)
                ·
                  refine ⟨17962201420966675090324145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11974800947311116726882763 17962201420966675090324145)
                  ·
                    refine ⟨13471651065725006317743109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17962201420966675090324145 13471651065725006317743109)
                    ·
                      refine ⟨2525934574823438684576833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13471651065725006317743109 2525934574823438684576833)
                      ·
                        rfl

theorem cell23_4919240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_4919240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919240 prefixEnd_4919240 := by exact prefixLift 4919240
  have htrace : WordTrace (prefixWord ++ tailWord_4919240) baseStart_4919240 baseEnd_4919240 := by
    simpa [prefixWord, tailWord_4919240, baseEnd_4919240] using wordTrace_append hprefix tailTrace_4919240
  have hstable : (prefixWord ++ tailWord_4919240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919240).length < 2 ^ (prefixWord ++ tailWord_4919240).sum := by decide
  have hdescent : baseEnd_4919240 < baseStart_4919240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919247 : List Nat := [1, 1, 2, 1, 1, 5, 5, 1, 1, 2, 3]
def baseStart_4919247 : Nat := 118140960795 + 4919247 * 2 ^ 59
def prefixEnd_4919247 : Nat := 4983230072969 + 3 ^ 40 * 4919247 * 2
def baseEnd_4919247 : Nat := 2525938169188020157189301

theorem tailTrace_4919247 : CollatzResearch.WordTrace tailWord_4919247 prefixEnd_4919247 2525938169188020157189301 := by
  unfold tailWord_4919247
  simp only [CollatzResearch.WordTrace]
  refine ⟨179419678009415734345707995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119613118672943822897138663 179419678009415734345707995)
  ·
    refine ⟨269129517014123601518561993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179419678009415734345707995 269129517014123601518561993)
    ·
      refine ⟨201847137760592701138921495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269129517014123601518561993 201847137760592701138921495)
      ·
        refine ⟨302770706640889051708382243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201847137760592701138921495 302770706640889051708382243)
        ·
          refine ⟨454156059961333577562573365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302770706640889051708382243 454156059961333577562573365)
          ·
            refine ⟨42577130621375022896491253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 454156059961333577562573365 42577130621375022896491253)
            ·
              refine ⟨3991605995753908396546055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42577130621375022896491253 3991605995753908396546055)
              ·
                refine ⟨5987408993630862594819083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3991605995753908396546055 5987408993630862594819083)
                ·
                  refine ⟨8981113490446293892228625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5987408993630862594819083 8981113490446293892228625)
                  ·
                    refine ⟨6735835117834720419171469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8981113490446293892228625 6735835117834720419171469)
                    ·
                      refine ⟨2525938169188020157189301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6735835117834720419171469 2525938169188020157189301)
                      ·
                        rfl

theorem cell23_4919247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 1, 2, 3].length) (baseStart_4919247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919247 prefixEnd_4919247 := by exact prefixLift 4919247
  have htrace : WordTrace (prefixWord ++ tailWord_4919247) baseStart_4919247 baseEnd_4919247 := by
    simpa [prefixWord, tailWord_4919247, baseEnd_4919247] using wordTrace_append hprefix tailTrace_4919247
  have hstable : (prefixWord ++ tailWord_4919247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919247).length < 2 ^ (prefixWord ++ tailWord_4919247).sum := by decide
  have hdescent : baseEnd_4919247 < baseStart_4919247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919250 : List Nat := [3, 2, 2, 3, 3, 10]
def baseStart_4919250 : Nat := 118140960795 + 4919250 * 2 ^ 59
def prefixEnd_4919250 : Nat := 4983230072969 + 3 ^ 40 * 4919250 * 2
def baseEnd_4919250 : Nat := 10394813619876475907209

theorem tailTrace_4919250 : CollatzResearch.WordTrace tailWord_4919250 prefixEnd_4919250 10394813619876475907209 := by
  unfold tailWord_4919250
  simp only [CollatzResearch.WordTrace]
  refine ⟨44854946857101216464516801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119613191618936577238711469 44854946857101216464516801)
  ·
    refine ⟨33641210142825912348387601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44854946857101216464516801 33641210142825912348387601)
    ·
      refine ⟨25230907607119434261290701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33641210142825912348387601 25230907607119434261290701)
      ·
        refine ⟨9461590352669787847984013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25230907607119434261290701 9461590352669787847984013)
        ·
          refine ⟨3548096382251170442994005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9461590352669787847984013 3548096382251170442994005)
          ·
            refine ⟨10394813619876475907209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3548096382251170442994005 10394813619876475907209)
            ·
              rfl

theorem cell23_4919250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 10].length) (baseStart_4919250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919250 prefixEnd_4919250 := by exact prefixLift 4919250
  have htrace : WordTrace (prefixWord ++ tailWord_4919250) baseStart_4919250 baseEnd_4919250 := by
    simpa [prefixWord, tailWord_4919250, baseEnd_4919250] using wordTrace_append hprefix tailTrace_4919250
  have hstable : (prefixWord ++ tailWord_4919250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919250).length < 2 ^ (prefixWord ++ tailWord_4919250).sum := by decide
  have hdescent : baseEnd_4919250 < baseStart_4919250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919263 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 2, 7]
def baseStart_4919263 : Nat := 118140960795 + 4919263 * 2 ^ 59
def prefixEnd_4919263 : Nat := 4983230072969 + 3 ^ 40 * 4919263 * 2
def baseEnd_4919263 : Nat := 841982128292830698196409

theorem tailTrace_4919263 : CollatzResearch.WordTrace tailWord_4919263 prefixEnd_4919263 841982128292830698196409 := by
  unfold tailWord_4919263
  simp only [CollatzResearch.WordTrace]
  refine ⟨179420261577357769078290443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119613507718238512718860295 179420261577357769078290443)
  ·
    refine ⟨269130392366036653617435665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179420261577357769078290443 269130392366036653617435665)
    ·
      refine ⟨201847794274527490213076749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269130392366036653617435665 201847794274527490213076749)
      ·
        refine ⟨75692922852947808829903781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201847794274527490213076749 75692922852947808829903781)
        ·
          refine ⟨14192423034927714155606959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75692922852947808829903781 14192423034927714155606959)
          ·
            refine ⟨21288634552391571233410439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14192423034927714155606959 21288634552391571233410439)
            ·
              refine ⟨31932951828587356850115659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21288634552391571233410439 31932951828587356850115659)
              ·
                refine ⟨47899427742881035275173489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31932951828587356850115659 47899427742881035275173489)
                ·
                  refine ⟨35924570807160776456380117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47899427742881035275173489 35924570807160776456380117)
                  ·
                    refine ⟨841982128292830698196409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35924570807160776456380117 841982128292830698196409)
                    ·
                      rfl

theorem cell23_4919263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 7].length) (baseStart_4919263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919263 prefixEnd_4919263 := by exact prefixLift 4919263
  have htrace : WordTrace (prefixWord ++ tailWord_4919263) baseStart_4919263 baseEnd_4919263 := by
    simpa [prefixWord, tailWord_4919263, baseEnd_4919263] using wordTrace_append hprefix tailTrace_4919263
  have hstable : (prefixWord ++ tailWord_4919263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919263).length < 2 ^ (prefixWord ++ tailWord_4919263).sum := by decide
  have hdescent : baseEnd_4919263 < baseStart_4919263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919330 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_4919330 : Nat := 118140960795 + 4919330 * 2 ^ 59
def prefixEnd_4919330 : Nat := 4983230072969 + 3 ^ 40 * 4919330 * 2
def baseEnd_4919330 : Nat := 2525980788082343332451419

theorem tailTrace_4919330 : CollatzResearch.WordTrace tailWord_4919330 prefixEnd_4919330 2525980788082343332451419 := by
  unfold tailWord_4919330
  simp only [CollatzResearch.WordTrace]
  refine ⟨44855676317028759880244861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119615136845410026347319629 44855676317028759880244861)
  ·
    refine ⟨16820878618885784955091823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44855676317028759880244861 16820878618885784955091823)
    ·
      refine ⟨25231317928328677432637735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16820878618885784955091823 25231317928328677432637735)
      ·
        refine ⟨37846976892493016148956603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25231317928328677432637735 37846976892493016148956603)
        ·
          refine ⟨56770465338739524223434905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37846976892493016148956603 56770465338739524223434905)
          ·
            refine ⟨42577849004054643167576179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56770465338739524223434905 42577849004054643167576179)
            ·
              refine ⟨63866773506081964751364269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42577849004054643167576179 63866773506081964751364269)
              ·
                refine ⟨23950040064780736781761601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63866773506081964751364269 23950040064780736781761601)
                ·
                  refine ⟨17962530048585552586321201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23950040064780736781761601 17962530048585552586321201)
                  ·
                    refine ⟨13471897536439164439740901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17962530048585552586321201 13471897536439164439740901)
                    ·
                      refine ⟨2525980788082343332451419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13471897536439164439740901 2525980788082343332451419)
                      ·
                        rfl

theorem cell23_4919330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_4919330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919330 prefixEnd_4919330 := by exact prefixLift 4919330
  have htrace : WordTrace (prefixWord ++ tailWord_4919330) baseStart_4919330 baseEnd_4919330 := by
    simpa [prefixWord, tailWord_4919330, baseEnd_4919330] using wordTrace_append hprefix tailTrace_4919330
  have hstable : (prefixWord ++ tailWord_4919330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919330).length < 2 ^ (prefixWord ++ tailWord_4919330).sum := by decide
  have hdescent : baseEnd_4919330 < baseStart_4919330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919374 : List Nat := [4, 1, 1, 1, 1, 5, 3, 2, 5]
def baseStart_4919374 : Nat := 118140960795 + 4919374 * 2 ^ 59
def prefixEnd_4919374 : Nat := 4983230072969 + 3 ^ 40 * 4919374 * 2
def baseEnd_4919374 : Nat := 280667042359015684477913

theorem tailTrace_4919374 : CollatzResearch.WordTrace tailWord_4919374 prefixEnd_4919374 280667042359015684477913 := by
  unfold tailWord_4919374
  simp only [CollatzResearch.WordTrace]
  refine ⟨22428038759994454379447647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119616206719970423357054117 22428038759994454379447647)
  ·
    refine ⟨33642058139991681569171471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22428038759994454379447647 33642058139991681569171471)
    ·
      refine ⟨50463087209987522353757207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33642058139991681569171471 50463087209987522353757207)
      ·
        refine ⟨75694630814981283530635811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50463087209987522353757207 75694630814981283530635811)
        ·
          refine ⟨113541946222471925295953717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75694630814981283530635811 113541946222471925295953717)
          ·
            refine ⟨10644557458356742996495661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113541946222471925295953717 10644557458356742996495661)
            ·
              refine ⟨3991709046883778623685873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10644557458356742996495661 3991709046883778623685873)
              ·
                refine ⟨2993781785162833967764405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3991709046883778623685873 2993781785162833967764405)
                ·
                  refine ⟨280667042359015684477913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2993781785162833967764405 280667042359015684477913)
                  ·
                    rfl

theorem cell23_4919374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_4919374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919374 prefixEnd_4919374 := by exact prefixLift 4919374
  have htrace : WordTrace (prefixWord ++ tailWord_4919374) baseStart_4919374 baseEnd_4919374 := by
    simpa [prefixWord, tailWord_4919374, baseEnd_4919374] using wordTrace_append hprefix tailTrace_4919374
  have hstable : (prefixWord ++ tailWord_4919374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919374).length < 2 ^ (prefixWord ++ tailWord_4919374).sum := by decide
  have hdescent : baseEnd_4919374 < baseStart_4919374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919407 : List Nat := [1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 4]
def baseStart_4919407 : Nat := 118140960795 + 4919407 * 2 ^ 59
def prefixEnd_4919407 : Nat := 4983230072969 + 3 ^ 40 * 4919407 * 2
def baseEnd_4919407 : Nat := 2526020326092739531188565

theorem tailTrace_4919407 : CollatzResearch.WordTrace tailWord_4919407 prefixEnd_4919407 2526020326092739531188565 := by
  unfold tailWord_4919407
  simp only [CollatzResearch.WordTrace]
  refine ⟨179425513688836081671532475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119617009125890721114354983 179425513688836081671532475)
  ·
    refine ⟨269138270533254122507298713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179425513688836081671532475 269138270533254122507298713)
    ·
      refine ⟨201853702899940591880474035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269138270533254122507298713 201853702899940591880474035)
      ·
        refine ⟨302780554349910887820711053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201853702899940591880474035 302780554349910887820711053)
        ·
          refine ⟨113542707881216582932766645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 302780554349910887820711053 113542707881216582932766645)
          ·
            refine ⟨10644628863864054649946873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113542707881216582932766645 10644628863864054649946873)
            ·
              refine ⟨7983471647898040987460155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10644628863864054649946873 7983471647898040987460155)
              ·
                refine ⟨11975207471847061481190233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7983471647898040987460155 11975207471847061481190233)
                ·
                  refine ⟨8981405603885296110892675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11975207471847061481190233 8981405603885296110892675)
                  ·
                    refine ⟨13472108405827944166339013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8981405603885296110892675 13472108405827944166339013)
                    ·
                      refine ⟨2526020326092739531188565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13472108405827944166339013 2526020326092739531188565)
                      ·
                        rfl

theorem cell23_4919407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 4].length) (baseStart_4919407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919407 prefixEnd_4919407 := by exact prefixLift 4919407
  have htrace : WordTrace (prefixWord ++ tailWord_4919407) baseStart_4919407 baseEnd_4919407 := by
    simpa [prefixWord, tailWord_4919407, baseEnd_4919407] using wordTrace_append hprefix tailTrace_4919407
  have hstable : (prefixWord ++ tailWord_4919407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919407).length < 2 ^ (prefixWord ++ tailWord_4919407).sum := by decide
  have hdescent : baseEnd_4919407 < baseStart_4919407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919427 : List Nat := [1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 3]
def baseStart_4919427 : Nat := 118140960795 + 4919427 * 2 ^ 59
def prefixEnd_4919427 : Nat := 4983230072969 + 3 ^ 40 * 4919427 * 2
def baseEnd_4919427 : Nat := 2526030595705829452938473

theorem tailTrace_4919427 : CollatzResearch.WordTrace tailWord_4919427 prefixEnd_4919427 2526030595705829452938473 := by
  unfold tailWord_4919427
  simp only [CollatzResearch.WordTrace]
  refine ⟨179426243148763625087260535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119617495432509083391507023 179426243148763625087260535)
  ·
    refine ⟨269139364723145437630890803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179426243148763625087260535 269139364723145437630890803)
    ·
      refine ⟨403709047084718156446336205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269139364723145437630890803 403709047084718156446336205)
      ·
        refine ⟨151390892656769308667376077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 403709047084718156446336205 151390892656769308667376077)
        ·
          refine ⟨56771584746288490750266029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151390892656769308667376077 56771584746288490750266029)
          ·
            refine ⟨21289344279858184031349761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56771584746288490750266029 21289344279858184031349761)
            ·
              refine ⟨15967008209893638023512321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21289344279858184031349761 15967008209893638023512321)
              ·
                refine ⟨11975256157420228517634241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15967008209893638023512321 11975256157420228517634241)
                ·
                  refine ⟨8981442118065171388225681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11975256157420228517634241 8981442118065171388225681)
                  ·
                    refine ⟨6736081588548878541169261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8981442118065171388225681 6736081588548878541169261)
                    ·
                      refine ⟨2526030595705829452938473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6736081588548878541169261 2526030595705829452938473)
                      ·
                        rfl

theorem cell23_4919427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 3].length) (baseStart_4919427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919427 prefixEnd_4919427 := by exact prefixLift 4919427
  have htrace : WordTrace (prefixWord ++ tailWord_4919427) baseStart_4919427 baseEnd_4919427 := by
    simpa [prefixWord, tailWord_4919427, baseEnd_4919427] using wordTrace_append hprefix tailTrace_4919427
  have hstable : (prefixWord ++ tailWord_4919427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919427).length < 2 ^ (prefixWord ++ tailWord_4919427).sum := by decide
  have hdescent : baseEnd_4919427 < baseStart_4919427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919520 : List Nat := [2, 1, 1, 3, 1, 3, 3, 9]
def baseStart_4919520 : Nat := 118140960795 + 4919520 * 2 ^ 59
def prefixEnd_4919520 : Nat := 4983230072969 + 3 ^ 40 * 4919520 * 2
def baseEnd_4919520 : Nat := 93558457385433244039835

theorem tailTrace_4919520 : CollatzResearch.WordTrace tailWord_4919520 prefixEnd_4919520 93558457385433244039835 := by
  unfold tailWord_4919520
  simp only [CollatzResearch.WordTrace]
  refine ⟨89714817568713350985198007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119619756758284467980264009 89714817568713350985198007)
  ·
    refine ⟨134572226353070026477797011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89714817568713350985198007 134572226353070026477797011)
    ·
      refine ⟨201858339529605039716695517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134572226353070026477797011 201858339529605039716695517)
      ·
        refine ⟨75696877323601889893760819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201858339529605039716695517 75696877323601889893760819)
        ·
          refine ⟨113545315985402834840641229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75696877323601889893760819 113545315985402834840641229)
          ·
            refine ⟨42579493494526063065240461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113545315985402834840641229 42579493494526063065240461)
            ·
              refine ⟨15967310060447273649465173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42579493494526063065240461 15967310060447273649465173)
              ·
                refine ⟨93558457385433244039835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15967310060447273649465173 93558457385433244039835)
                ·
                  rfl

theorem cell23_4919520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 9].length) (baseStart_4919520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919520 prefixEnd_4919520 := by exact prefixLift 4919520
  have htrace : WordTrace (prefixWord ++ tailWord_4919520) baseStart_4919520 baseEnd_4919520 := by
    simpa [prefixWord, tailWord_4919520, baseEnd_4919520] using wordTrace_append hprefix tailTrace_4919520
  have hstable : (prefixWord ++ tailWord_4919520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919520).length < 2 ^ (prefixWord ++ tailWord_4919520).sum := by decide
  have hdescent : baseEnd_4919520 < baseStart_4919520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919548 : List Nat := [2, 2, 2, 1, 4, 3, 1, 1, 3, 2, 2]
def baseStart_4919548 : Nat := 118140960795 + 4919548 * 2 ^ 59
def prefixEnd_4919548 : Nat := 4983230072969 + 3 ^ 40 * 4919548 * 2
def baseEnd_4919548 : Nat := 2526092726865023479525417

theorem tailTrace_4919548 : CollatzResearch.WordTrace tailWord_4919548 prefixEnd_4919548 2526092726865023479525417 := by
  unfold tailWord_4919548
  simp only [CollatzResearch.WordTrace]
  refine ⟨89715328190662631376207649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119620437587550175168276865 89715328190662631376207649)
  ·
    refine ⟨67286496142996973532155737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89715328190662631376207649 67286496142996973532155737)
    ·
      refine ⟨50464872107247730149116803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67286496142996973532155737 50464872107247730149116803)
      ·
        refine ⟨75697308160871595223675205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50464872107247730149116803 75697308160871595223675205)
        ·
          refine ⟨14193245280163424104439101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75697308160871595223675205 14193245280163424104439101)
          ·
            refine ⟨5322466980061284039164663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14193245280163424104439101 5322466980061284039164663)
            ·
              refine ⟨7983700470091926058746995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5322466980061284039164663 7983700470091926058746995)
              ·
                refine ⟨11975550705137889088120493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7983700470091926058746995 11975550705137889088120493)
                ·
                  refine ⟨4490831514426708408045185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11975550705137889088120493 4490831514426708408045185)
                  ·
                    refine ⟨3368123635820031306033889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4490831514426708408045185 3368123635820031306033889)
                    ·
                      refine ⟨2526092726865023479525417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3368123635820031306033889 2526092726865023479525417)
                      ·
                        rfl

theorem cell23_4919548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 3, 2, 2].length) (baseStart_4919548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919548 prefixEnd_4919548 := by exact prefixLift 4919548
  have htrace : WordTrace (prefixWord ++ tailWord_4919548) baseStart_4919548 baseEnd_4919548 := by
    simpa [prefixWord, tailWord_4919548, baseEnd_4919548] using wordTrace_append hprefix tailTrace_4919548
  have hstable : (prefixWord ++ tailWord_4919548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919548).length < 2 ^ (prefixWord ++ tailWord_4919548).sum := by decide
  have hdescent : baseEnd_4919548 < baseStart_4919548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919554 : List Nat := [3, 4, 1, 1, 2, 2, 2, 8]
def baseStart_4919554 : Nat := 118140960795 + 4919554 * 2 ^ 59
def prefixEnd_4919554 : Nat := 4983230072969 + 3 ^ 40 * 4919554 * 2
def baseEnd_4919554 : Nat := 93559103990701868742607

theorem tailTrace_4919554 : CollatzResearch.WordTrace tailWord_4919554 prefixEnd_4919554 93559103990701868742607 := by
  unfold tailWord_4919554
  simp only [CollatzResearch.WordTrace]
  refine ⟨44857718804825881444283429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119620583479535683851422477 44857718804825881444283429)
  ·
    refine ⟨8410822275904852770803143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44857718804825881444283429 8410822275904852770803143)
    ·
      refine ⟨12616233413857279156204715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8410822275904852770803143 12616233413857279156204715)
      ·
        refine ⟨18924350120785918734307073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12616233413857279156204715 18924350120785918734307073)
        ·
          refine ⟨14193262590589439050730305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18924350120785918734307073 14193262590589439050730305)
          ·
            refine ⟨10644946942942079288047729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14193262590589439050730305 10644946942942079288047729)
            ·
              refine ⟨7983710207206559466035797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10644946942942079288047729 7983710207206559466035797)
              ·
                refine ⟨93559103990701868742607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7983710207206559466035797 93559103990701868742607)
                ·
                  rfl

theorem cell23_4919554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 8].length) (baseStart_4919554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919554 prefixEnd_4919554 := by exact prefixLift 4919554
  have htrace : WordTrace (prefixWord ++ tailWord_4919554) baseStart_4919554 baseEnd_4919554 := by
    simpa [prefixWord, tailWord_4919554, baseEnd_4919554] using wordTrace_append hprefix tailTrace_4919554
  have hstable : (prefixWord ++ tailWord_4919554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919554).length < 2 ^ (prefixWord ++ tailWord_4919554).sum := by decide
  have hdescent : baseEnd_4919554 < baseStart_4919554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919581 : List Nat := [1, 4, 2, 3, 2, 1, 1, 2, 1, 3, 3]
def baseStart_4919581 : Nat := 118140960795 + 4919581 * 2 ^ 59
def prefixEnd_4919581 : Nat := 4983230072969 + 3 ^ 40 * 4919581 * 2
def baseEnd_4919581 : Nat := 2526109671726621850412765

theorem tailTrace_4919581 : CollatzResearch.WordTrace tailWord_4919581 prefixEnd_4919581 2526109671726621850412765 := by
  unfold tailWord_4919581
  simp only [CollatzResearch.WordTrace]
  refine ⟨179431859990205709388366597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119621239993470472925577731 179431859990205709388366597)
  ·
    refine ⟨33643473748163570510318737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179431859990205709388366597 33643473748163570510318737)
    ·
      refine ⟨25232605311122677882739053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33643473748163570510318737 25232605311122677882739053)
      ·
        refine ⟨9462226991671004206027145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25232605311122677882739053 9462226991671004206027145)
        ·
          refine ⟨7096670243753253154520359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9462226991671004206027145 7096670243753253154520359)
          ·
            refine ⟨10645005365629879731780539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7096670243753253154520359 10645005365629879731780539)
            ·
              refine ⟨15967508048444819597670809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10645005365629879731780539 15967508048444819597670809)
              ·
                refine ⟨11975631036333614698253107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15967508048444819597670809 11975631036333614698253107)
                ·
                  refine ⟨17963446554500422047379661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11975631036333614698253107 17963446554500422047379661)
                  ·
                    refine ⟨6736292457937658267767373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17963446554500422047379661 6736292457937658267767373)
                    ·
                      refine ⟨2526109671726621850412765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6736292457937658267767373 2526109671726621850412765)
                      ·
                        rfl

theorem cell23_4919581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_4919581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919581 prefixEnd_4919581 := by exact prefixLift 4919581
  have htrace : WordTrace (prefixWord ++ tailWord_4919581) baseStart_4919581 baseEnd_4919581 := by
    simpa [prefixWord, tailWord_4919581, baseEnd_4919581] using wordTrace_append hprefix tailTrace_4919581
  have hstable : (prefixWord ++ tailWord_4919581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919581).length < 2 ^ (prefixWord ++ tailWord_4919581).sum := by decide
  have hdescent : baseEnd_4919581 < baseStart_4919581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919604 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_4919604 : Nat := 118140960795 + 4919604 * 2 ^ 59
def prefixEnd_4919604 : Nat := 4983230072969 + 3 ^ 40 * 4919604 * 2
def baseEnd_4919604 : Nat := 2526121481781675260425159

theorem tailTrace_4919604 : CollatzResearch.WordTrace tailWord_4919604 prefixEnd_4919604 2526121481781675260425159 := by
  unfold tailWord_4919604
  simp only [CollatzResearch.WordTrace]
  refine ⟨89716349434561192158226933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119621799246081589544302577 89716349434561192158226933)
  ·
    refine ⟨8410907759490111764833775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89716349434561192158226933 8410907759490111764833775)
    ·
      refine ⟨12616361639235167647250663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8410907759490111764833775 12616361639235167647250663)
      ·
        refine ⟨18924542458852751470875995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12616361639235167647250663 18924542458852751470875995)
        ·
          refine ⟨28386813688279127206313993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18924542458852751470875995 28386813688279127206313993)
          ·
            refine ⟨21290110266209345404735495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28386813688279127206313993 21290110266209345404735495)
            ·
              refine ⟨31935165399314018107103243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21290110266209345404735495 31935165399314018107103243)
              ·
                refine ⟨47902748098971027160654865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31935165399314018107103243 47902748098971027160654865)
                ·
                  refine ⟨35927061074228270370491149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47902748098971027160654865 35927061074228270370491149)
                  ·
                    refine ⟨13472647902835601388934181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35927061074228270370491149 13472647902835601388934181)
                    ·
                      refine ⟨2526121481781675260425159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13472647902835601388934181 2526121481781675260425159)
                      ·
                        rfl

theorem cell23_4919604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_4919604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919604 prefixEnd_4919604 := by exact prefixLift 4919604
  have htrace : WordTrace (prefixWord ++ tailWord_4919604) baseStart_4919604 baseEnd_4919604 := by
    simpa [prefixWord, tailWord_4919604, baseEnd_4919604] using wordTrace_append hprefix tailTrace_4919604
  have hstable : (prefixWord ++ tailWord_4919604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919604).length < 2 ^ (prefixWord ++ tailWord_4919604).sum := by decide
  have hdescent : baseEnd_4919604 < baseStart_4919604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919614 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 2, 6]
def baseStart_4919614 : Nat := 118140960795 + 4919614 * 2 ^ 59
def prefixEnd_4919614 : Nat := 4983230072969 + 3 ^ 40 * 4919614 * 2
def baseEnd_4919614 : Nat := 842042205529406740433371

theorem tailTrace_4919614 : CollatzResearch.WordTrace tailWord_4919614 prefixEnd_4919614 842042205529406740433371 := by
  unfold tailWord_4919614
  simp only [CollatzResearch.WordTrace]
  refine ⟨22429132949885769503039737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119622042399390770682878597 22429132949885769503039737)
  ·
    refine ⟨16821849712414327127279803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22429132949885769503039737 16821849712414327127279803)
    ·
      refine ⟨25232774568621490690919705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16821849712414327127279803 25232774568621490690919705)
      ·
        refine ⟨18924580926466118018189779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25232774568621490690919705 18924580926466118018189779)
        ·
          refine ⟨28386871389699177027284669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18924580926466118018189779 28386871389699177027284669)
          ·
            refine ⟨10645076771137191385231751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28386871389699177027284669 10645076771137191385231751)
            ·
              refine ⟨15967615156705787077847627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10645076771137191385231751 15967615156705787077847627)
              ·
                refine ⟨23951422735058680616771441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15967615156705787077847627 23951422735058680616771441)
                ·
                  refine ⟨17963567051294010462578581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23951422735058680616771441 17963567051294010462578581)
                  ·
                    refine ⟨842042205529406740433371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17963567051294010462578581 842042205529406740433371)
                    ·
                      rfl

theorem cell23_4919614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_4919614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919614 prefixEnd_4919614 := by exact prefixLift 4919614
  have htrace : WordTrace (prefixWord ++ tailWord_4919614) baseStart_4919614 baseEnd_4919614 := by
    simpa [prefixWord, tailWord_4919614, baseEnd_4919614] using wordTrace_append hprefix tailTrace_4919614
  have hstable : (prefixWord ++ tailWord_4919614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919614).length < 2 ^ (prefixWord ++ tailWord_4919614).sum := by decide
  have hdescent : baseEnd_4919614 < baseStart_4919614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919655 : List Nat := [1, 1, 5, 1, 3, 3, 1, 2, 2, 2, 2]
def baseStart_4919655 : Nat := 118140960795 + 4919655 * 2 ^ 59
def prefixEnd_4919655 : Nat := 4983230072969 + 3 ^ 40 * 4919655 * 2
def baseEnd_4919655 : Nat := 2526147669295054560887425

theorem tailTrace_4919655 : CollatzResearch.WordTrace tailWord_4919655 prefixEnd_4919655 2526147669295054560887425 := by
  unfold tailWord_4919655
  simp only [CollatzResearch.WordTrace]
  refine ⟨179434558991937620026560419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119623039327958413351040279 179434558991937620026560419)
  ·
    refine ⟨269151838487906430039840629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179434558991937620026560419 269151838487906430039840629)
    ·
      refine ⟨25232984858241227816235059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 269151838487906430039840629 25232984858241227816235059)
      ·
        refine ⟨37849477287361841724352589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25232984858241227816235059 37849477287361841724352589)
        ·
          refine ⟨14193553982760690646632221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37849477287361841724352589 14193553982760690646632221)
          ·
            refine ⟨5322582743535258992487083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14193553982760690646632221 5322582743535258992487083)
            ·
              refine ⟨7983874115302888488730625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5322582743535258992487083 7983874115302888488730625)
              ·
                refine ⟨5987905586477166366547969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7983874115302888488730625 5987905586477166366547969)
                ·
                  refine ⟨4490929189857874774910977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5987905586477166366547969 4490929189857874774910977)
                  ·
                    refine ⟨3368196892393406081183233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4490929189857874774910977 3368196892393406081183233)
                    ·
                      refine ⟨2526147669295054560887425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3368196892393406081183233 2526147669295054560887425)
                      ·
                        rfl

theorem cell23_4919655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_4919655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919655 prefixEnd_4919655 := by exact prefixLift 4919655
  have htrace : WordTrace (prefixWord ++ tailWord_4919655) baseStart_4919655 baseEnd_4919655 := by
    simpa [prefixWord, tailWord_4919655, baseEnd_4919655] using wordTrace_append hprefix tailTrace_4919655
  have hstable : (prefixWord ++ tailWord_4919655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919655).length < 2 ^ (prefixWord ++ tailWord_4919655).sum := by decide
  have hdescent : baseEnd_4919655 < baseStart_4919655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919657 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 4, 5]
def baseStart_4919657 : Nat := 118140960795 + 4919657 * 2 ^ 59
def prefixEnd_4919657 : Nat := 4983230072969 + 3 ^ 40 * 4919657 * 2
def baseEnd_4919657 : Nat := 842049565418787851020805

theorem tailTrace_4919657 : CollatzResearch.WordTrace tailWord_4919657 prefixEnd_4919657 842049565418787851020805 := by
  unfold tailWord_4919657
  simp only [CollatzResearch.WordTrace]
  refine ⟨179434631937930374368133225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119623087958620249578755483 179434631937930374368133225)
  ·
    refine ⟨134575973953447780776099919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179434631937930374368133225 134575973953447780776099919)
    ·
      refine ⟨201863960930171671164149879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134575973953447780776099919 201863960930171671164149879)
      ·
        refine ⟨302795941395257506746224819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201863960930171671164149879 302795941395257506746224819)
        ·
          refine ⟨454193912092886260119337229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302795941395257506746224819 454193912092886260119337229)
          ·
            refine ⟨170322717034832347544751461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 454193912092886260119337229 170322717034832347544751461)
            ·
              refine ⟨31935509444031065164640899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170322717034832347544751461 31935509444031065164640899)
              ·
                refine ⟨47903264166046597746961349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31935509444031065164640899 47903264166046597746961349)
                ·
                  refine ⟨8981862031133737077555253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47903264166046597746961349 8981862031133737077555253)
                  ·
                    refine ⟨842049565418787851020805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8981862031133737077555253 842049565418787851020805)
                    ·
                      rfl

theorem cell23_4919657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 5].length) (baseStart_4919657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919657 prefixEnd_4919657 := by exact prefixLift 4919657
  have htrace : WordTrace (prefixWord ++ tailWord_4919657) baseStart_4919657 baseEnd_4919657 := by
    simpa [prefixWord, tailWord_4919657, baseEnd_4919657] using wordTrace_append hprefix tailTrace_4919657
  have hstable : (prefixWord ++ tailWord_4919657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919657).length < 2 ^ (prefixWord ++ tailWord_4919657).sum := by decide
  have hdescent : baseEnd_4919657 < baseStart_4919657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919687 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 2, 8]
def baseStart_4919687 : Nat := 118140960795 + 4919687 * 2 ^ 59
def prefixEnd_4919687 : Nat := 4983230072969 + 3 ^ 40 * 4919687 * 2
def baseEnd_4919687 : Nat := 842054700225332811895759

theorem tailTrace_4919687 : CollatzResearch.WordTrace tailWord_4919687 prefixEnd_4919687 842054700225332811895759 := by
  unfold tailWord_4919687
  simp only [CollatzResearch.WordTrace]
  refine ⟨179435726127821689491725315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119623817418547792994483543 179435726127821689491725315)
  ·
    refine ⟨269153589191732534237587973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179435726127821689491725315 269153589191732534237587973)
    ·
      refine ⟨50466297973449850169547745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 269153589191732534237587973 50466297973449850169547745)
      ·
        refine ⟨37849723480087387627160809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50466297973449850169547745 37849723480087387627160809)
        ·
          refine ⟨28387292610065540720370607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37849723480087387627160809 28387292610065540720370607)
          ·
            refine ⟨42580938915098311080555911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28387292610065540720370607 42580938915098311080555911)
            ·
              refine ⟨63871408372647466620833867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42580938915098311080555911 63871408372647466620833867)
              ·
                refine ⟨95807112558971199931250801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63871408372647466620833867 95807112558971199931250801)
                ·
                  refine ⟨71855334419228399948438101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95807112558971199931250801 71855334419228399948438101)
                  ·
                    refine ⟨842054700225332811895759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71855334419228399948438101 842054700225332811895759)
                    ·
                      rfl

theorem cell23_4919687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_4919687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919687 prefixEnd_4919687 := by exact prefixLift 4919687
  have htrace : WordTrace (prefixWord ++ tailWord_4919687) baseStart_4919687 baseEnd_4919687 := by
    simpa [prefixWord, tailWord_4919687, baseEnd_4919687] using wordTrace_append hprefix tailTrace_4919687
  have hstable : (prefixWord ++ tailWord_4919687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919687).length < 2 ^ (prefixWord ++ tailWord_4919687).sum := by decide
  have hdescent : baseEnd_4919687 < baseStart_4919687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919717 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 8]
def baseStart_4919717 : Nat := 118140960795 + 4919717 * 2 ^ 59
def prefixEnd_4919717 : Nat := 4983230072969 + 3 ^ 40 * 4919717 * 2
def baseEnd_4919717 : Nat := 280686611677292590923571

theorem tailTrace_4919717 : CollatzResearch.WordTrace tailWord_4919717 prefixEnd_4919717 280686611677292590923571 := by
  unfold tailWord_4919717
  simp only [CollatzResearch.WordTrace]
  refine ⟨179436820317713004615317405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119624546878475336410211603 179436820317713004615317405)
  ·
    refine ⟨67288807619142376730744027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179436820317713004615317405 67288807619142376730744027)
    ·
      refine ⟨100933211428713565096116041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67288807619142376730744027 100933211428713565096116041)
      ·
        refine ⟨75699908571535173822087031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100933211428713565096116041 75699908571535173822087031)
        ·
          refine ⟨113549862857302760733130547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75699908571535173822087031 113549862857302760733130547)
          ·
            refine ⟨170324794285954141099695821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113549862857302760733130547 170324794285954141099695821)
            ·
              refine ⟨63871797857232802912385933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170324794285954141099695821 63871797857232802912385933)
              ·
                refine ⟨23951924196462301092144725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63871797857232802912385933 23951924196462301092144725)
                ·
                  refine ⟨280686611677292590923571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23951924196462301092144725 280686611677292590923571)
                  ·
                    rfl

theorem cell23_4919717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 8].length) (baseStart_4919717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919717 prefixEnd_4919717 := by exact prefixLift 4919717
  have htrace : WordTrace (prefixWord ++ tailWord_4919717) baseStart_4919717 baseEnd_4919717 := by
    simpa [prefixWord, tailWord_4919717, baseEnd_4919717] using wordTrace_append hprefix tailTrace_4919717
  have hstable : (prefixWord ++ tailWord_4919717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919717).length < 2 ^ (prefixWord ++ tailWord_4919717).sum := by decide
  have hdescent : baseEnd_4919717 < baseStart_4919717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919721 : List Nat := [1, 2, 1, 1, 1, 1, 3, 8, 1, 4]
def baseStart_4919721 : Nat := 118140960795 + 4919721 * 2 ^ 59
def prefixEnd_4919721 : Nat := 4983230072969 + 3 ^ 40 * 4919721 * 2
def baseEnd_4919721 : Nat := 842060519672750434220707

theorem tailTrace_4919721 : CollatzResearch.WordTrace tailWord_4919721 prefixEnd_4919721 842060519672750434220707 := by
  unfold tailWord_4919721
  simp only [CollatzResearch.WordTrace]
  refine ⟨179436966209698513298463017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119624644139799008865642011 179436966209698513298463017)
  ·
    refine ⟨134577724657273884973847263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179436966209698513298463017 134577724657273884973847263)
    ·
      refine ⟨201866586985910827460770895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134577724657273884973847263 201866586985910827460770895)
      ·
        refine ⟨302799880478866241191156343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201866586985910827460770895 302799880478866241191156343)
        ·
          refine ⟨454199820718299361786734515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302799880478866241191156343 454199820718299361786734515)
          ·
            refine ⟨681299731077449042680101773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454199820718299361786734515 681299731077449042680101773)
            ·
              refine ⟨255487399154043391005038165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 681299731077449042680101773 255487399154043391005038165)
              ·
                refine ⟨2993992958836445988340291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 255487399154043391005038165 2993992958836445988340291)
                ·
                  refine ⟨4490989438254668982510437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2993992958836445988340291 4490989438254668982510437)
                  ·
                    refine ⟨842060519672750434220707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4490989438254668982510437 842060519672750434220707)
                    ·
                      rfl

theorem cell23_4919721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 1, 4].length) (baseStart_4919721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919721 prefixEnd_4919721 := by exact prefixLift 4919721
  have htrace : WordTrace (prefixWord ++ tailWord_4919721) baseStart_4919721 baseEnd_4919721 := by
    simpa [prefixWord, tailWord_4919721, baseEnd_4919721] using wordTrace_append hprefix tailTrace_4919721
  have hstable : (prefixWord ++ tailWord_4919721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919721).length < 2 ^ (prefixWord ++ tailWord_4919721).sum := by decide
  have hdescent : baseEnd_4919721 < baseStart_4919721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919812 : List Nat := [2, 3, 2, 3, 1, 2, 2, 3, 1, 1, 3]
def baseStart_4919812 : Nat := 118140960795 + 4919812 * 2 ^ 59
def prefixEnd_4919812 : Nat := 4983230072969 + 3 ^ 40 * 4919812 * 2
def baseEnd_4919812 : Nat := 2526228285757810446624203

theorem tailTrace_4919812 : CollatzResearch.WordTrace tailWord_4919812 prefixEnd_4919812 2526228285757810446624203 := by
  unfold tailWord_4919812
  simp only [CollatzResearch.WordTrace]
  refine ⟨89720142626184417920012845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119626856834912557226683793 89720142626184417920012845)
  ·
    refine ⟨33645053484819156720004817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89720142626184417920012845 33645053484819156720004817)
    ·
      refine ⟨25233790113614367540003613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33645053484819156720004817 25233790113614367540003613)
      ·
        refine ⟨9462671292605387827501355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25233790113614367540003613 9462671292605387827501355)
        ·
          refine ⟨14194006938908081741252033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9462671292605387827501355 14194006938908081741252033)
          ·
            refine ⟨10645505204181061305939025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14194006938908081741252033 10645505204181061305939025)
            ·
              refine ⟨7984128903135795979454269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10645505204181061305939025 7984128903135795979454269)
              ·
                refine ⟨2994048338675923492295351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7984128903135795979454269 2994048338675923492295351)
                ·
                  refine ⟨4491072508013885238443027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2994048338675923492295351 4491072508013885238443027)
                  ·
                    refine ⟨6736608762020827857664541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4491072508013885238443027 6736608762020827857664541)
                    ·
                      refine ⟨2526228285757810446624203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6736608762020827857664541 2526228285757810446624203)
                      ·
                        rfl

theorem cell23_4919812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_4919812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919812 prefixEnd_4919812 := by exact prefixLift 4919812
  have htrace : WordTrace (prefixWord ++ tailWord_4919812) baseStart_4919812 baseEnd_4919812 := by
    simpa [prefixWord, tailWord_4919812, baseEnd_4919812] using wordTrace_append hprefix tailTrace_4919812
  have hstable : (prefixWord ++ tailWord_4919812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919812).length < 2 ^ (prefixWord ++ tailWord_4919812).sum := by decide
  have hdescent : baseEnd_4919812 < baseStart_4919812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919815 : List Nat := [1, 1, 4, 3, 3, 2, 2, 1, 1, 5]
def baseStart_4919815 : Nat := 118140960795 + 4919815 * 2 ^ 59
def prefixEnd_4919815 : Nat := 4983230072969 + 3 ^ 40 * 4919815 * 2
def baseEnd_4919815 : Nat := 842076608733257978295563

theorem tailTrace_4919815 : CollatzResearch.WordTrace tailWord_4919815 prefixEnd_4919815 842076608733257978295563 := by
  unfold tailWord_4919815
  simp only [CollatzResearch.WordTrace]
  refine ⟨179440394671357967352384899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119626929780905311568256599 179440394671357967352384899)
  ·
    refine ⟨269160592007036951028577349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179440394671357967352384899 269160592007036951028577349)
    ·
      refine ⟨50467611001319428317858253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 269160592007036951028577349 50467611001319428317858253)
      ·
        refine ⟨18925354125494785619196845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50467611001319428317858253 18925354125494785619196845)
        ·
          refine ⟨7097007797060544607198817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18925354125494785619196845 7097007797060544607198817)
          ·
            refine ⟨5322755847795408455399113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7097007797060544607198817 5322755847795408455399113)
            ·
              refine ⟨3992066885846556341549335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5322755847795408455399113 3992066885846556341549335)
              ·
                refine ⟨5988100328769834512324003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3992066885846556341549335 5988100328769834512324003)
                ·
                  refine ⟨8982150493154751768486005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5988100328769834512324003 8982150493154751768486005)
                  ·
                    refine ⟨842076608733257978295563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8982150493154751768486005 842076608733257978295563)
                    ·
                      rfl

theorem cell23_4919815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_4919815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919815 prefixEnd_4919815 := by exact prefixLift 4919815
  have htrace : WordTrace (prefixWord ++ tailWord_4919815) baseStart_4919815 baseEnd_4919815 := by
    simpa [prefixWord, tailWord_4919815, baseEnd_4919815] using wordTrace_append hprefix tailTrace_4919815
  have hstable : (prefixWord ++ tailWord_4919815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919815).length < 2 ^ (prefixWord ++ tailWord_4919815).sum := by decide
  have hdescent : baseEnd_4919815 < baseStart_4919815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919818 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 5, 2, 2]
def baseStart_4919818 : Nat := 118140960795 + 4919818 * 2 ^ 59
def prefixEnd_4919818 : Nat := 4983230072969 + 3 ^ 40 * 4919818 * 2
def baseEnd_4919818 : Nat := 2526231366641737423149175

theorem tailTrace_4919818 : CollatzResearch.WordTrace tailWord_4919818 prefixEnd_4919818 2526231366641737423149175 := by
  unfold tailWord_4919818
  simp only [CollatzResearch.WordTrace]
  refine ⟨44860126022586774716186027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119627002726898065909829405 44860126022586774716186027)
  ·
    refine ⟨67290189033880162074279041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44860126022586774716186027 67290189033880162074279041)
    ·
      refine ⟨50467641775410121555709281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67290189033880162074279041 50467641775410121555709281)
      ·
        refine ⟨37850731331557591166781961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50467641775410121555709281 37850731331557591166781961)
        ·
          refine ⟨28388048498668193375086471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37850731331557591166781961 28388048498668193375086471)
          ·
            refine ⟨42582072748002290062629707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28388048498668193375086471 42582072748002290062629707)
            ·
              refine ⟨63873109122003435093944561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42582072748002290062629707 63873109122003435093944561)
              ·
                refine ⟨47904831841502576320458421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63873109122003435093944561 47904831841502576320458421)
                ·
                  refine ⟨4491077985140866530042977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47904831841502576320458421 4491077985140866530042977)
                  ·
                    refine ⟨3368308488855649897532233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4491077985140866530042977 3368308488855649897532233)
                    ·
                      refine ⟨2526231366641737423149175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3368308488855649897532233 2526231366641737423149175)
                      ·
                        rfl

theorem cell23_4919818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_4919818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919818 prefixEnd_4919818 := by exact prefixLift 4919818
  have htrace : WordTrace (prefixWord ++ tailWord_4919818) baseStart_4919818 baseEnd_4919818 := by
    simpa [prefixWord, tailWord_4919818, baseEnd_4919818] using wordTrace_append hprefix tailTrace_4919818
  have hstable : (prefixWord ++ tailWord_4919818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919818).length < 2 ^ (prefixWord ++ tailWord_4919818).sum := by decide
  have hdescent : baseEnd_4919818 < baseStart_4919818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919848 : List Nat := [2, 1, 5, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_4919848 : Nat := 118140960795 + 4919848 * 2 ^ 59
def prefixEnd_4919848 : Nat := 4983230072969 + 3 ^ 40 * 4919848 * 2
def baseEnd_4919848 : Nat := 2526246771061372305774037

theorem tailTrace_4919848 : CollatzResearch.WordTrace tailWord_4919848 prefixEnd_4919848 2526246771061372305774037 := by
  unfold tailWord_4919848
  simp only [CollatzResearch.WordTrace]
  refine ⟨89720799140119206994168099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119627732186825609325557465 89720799140119206994168099)
  ·
    refine ⟨134581198710178810491252149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89720799140119206994168099 134581198710178810491252149)
    ·
      refine ⟨12616987379079263483554889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134581198710178810491252149 12616987379079263483554889)
      ·
        refine ⟨9462740534309447612666167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12616987379079263483554889 9462740534309447612666167)
        ·
          refine ⟨14194110801464171418999251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9462740534309447612666167 14194110801464171418999251)
          ·
            refine ⟨21291166202196257128498877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14194110801464171418999251 21291166202196257128498877)
            ·
              refine ⟨7984187325823596423187079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21291166202196257128498877 7984187325823596423187079)
              ·
                refine ⟨11976280988735394634780619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7984187325823596423187079 11976280988735394634780619)
                ·
                  refine ⟨17964421483103091952170929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11976280988735394634780619 17964421483103091952170929)
                  ·
                    refine ⟨13473316112327318964128197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17964421483103091952170929 13473316112327318964128197)
                    ·
                      refine ⟨2526246771061372305774037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13473316112327318964128197 2526246771061372305774037)
                      ·
                        rfl

theorem cell23_4919848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_4919848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919848 prefixEnd_4919848 := by exact prefixLift 4919848
  have htrace : WordTrace (prefixWord ++ tailWord_4919848) baseStart_4919848 baseEnd_4919848 := by
    simpa [prefixWord, tailWord_4919848, baseEnd_4919848] using wordTrace_append hprefix tailTrace_4919848
  have hstable : (prefixWord ++ tailWord_4919848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919848).length < 2 ^ (prefixWord ++ tailWord_4919848).sum := by decide
  have hdescent : baseEnd_4919848 < baseStart_4919848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919864 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 1, 4, 5]
def baseStart_4919864 : Nat := 118140960795 + 4919864 * 2 ^ 59
def prefixEnd_4919864 : Nat := 4983230072969 + 3 ^ 40 * 4919864 * 2
def baseEnd_4919864 : Nat := 2526254986751844243173963

theorem tailTrace_4919864 : CollatzResearch.WordTrace tailWord_4919864 prefixEnd_4919864 2526254986751844243173963 := by
  unfold tailWord_4919864
  simp only [CollatzResearch.WordTrace]
  refine ⟨89721090924090224360459323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119628121232120299147279097 89721090924090224360459323)
  ·
    refine ⟨134581636386135336540688985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89721090924090224360459323 134581636386135336540688985)
    ·
      refine ⟨100936227289601502405516739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134581636386135336540688985 100936227289601502405516739)
      ·
        refine ⟨151404340934402253608275109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100936227289601502405516739 151404340934402253608275109)
        ·
          refine ⟨28388313925200422551551583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151404340934402253608275109 28388313925200422551551583)
          ·
            refine ⟨42582470887800633827327375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28388313925200422551551583 42582470887800633827327375)
            ·
              refine ⟨63873706331700950740991063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42582470887800633827327375 63873706331700950740991063)
              ·
                refine ⟨95810559497551426111486595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63873706331700950740991063 95810559497551426111486595)
                ·
                  refine ⟨143715839246327139167229893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95810559497551426111486595 143715839246327139167229893)
                  ·
                    refine ⟨26946719858686338593855605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 143715839246327139167229893 26946719858686338593855605)
                    ·
                      refine ⟨2526254986751844243173963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26946719858686338593855605 2526254986751844243173963)
                      ·
                        rfl

theorem cell23_4919864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_4919864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919864 prefixEnd_4919864 := by exact prefixLift 4919864
  have htrace : WordTrace (prefixWord ++ tailWord_4919864) baseStart_4919864 baseEnd_4919864 := by
    simpa [prefixWord, tailWord_4919864, baseEnd_4919864] using wordTrace_append hprefix tailTrace_4919864
  have hstable : (prefixWord ++ tailWord_4919864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919864).length < 2 ^ (prefixWord ++ tailWord_4919864).sum := by decide
  have hdescent : baseEnd_4919864 < baseStart_4919864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919868 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 4, 1, 3]
def baseStart_4919868 : Nat := 118140960795 + 4919868 * 2 ^ 59
def prefixEnd_4919868 : Nat := 4983230072969 + 3 ^ 40 * 4919868 * 2
def baseEnd_4919868 : Nat := 2526257040674462227523945

theorem tailTrace_4919868 : CollatzResearch.WordTrace tailWord_4919868 prefixEnd_4919868 2526257040674462227523945 := by
  unfold tailWord_4919868
  simp only [CollatzResearch.WordTrace]
  refine ⟨89721163870082978702032129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119628218493443971602709505 89721163870082978702032129)
  ·
    refine ⟨67290872902562234026524097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89721163870082978702032129 67290872902562234026524097)
    ·
      refine ⟨50468154676921675519893073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67290872902562234026524097 50468154676921675519893073)
      ·
        refine ⟨37851116007691256639919805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50468154676921675519893073 37851116007691256639919805)
        ·
          refine ⟨14194168502884221239969927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37851116007691256639919805 14194168502884221239969927)
          ·
            refine ⟨21291252754326331859954891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14194168502884221239969927 21291252754326331859954891)
            ·
              refine ⟨31936879131489497789932337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21291252754326331859954891 31936879131489497789932337)
              ·
                refine ⟨23952659348617123342449253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31936879131489497789932337 23952659348617123342449253)
                ·
                  refine ⟨4491123627865710626709235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23952659348617123342449253 4491123627865710626709235)
                  ·
                    refine ⟨6736685441798565940063853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4491123627865710626709235 6736685441798565940063853)
                    ·
                      refine ⟨2526257040674462227523945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6736685441798565940063853 2526257040674462227523945)
                      ·
                        rfl

theorem cell23_4919868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_4919868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919868 prefixEnd_4919868 := by exact prefixLift 4919868
  have htrace : WordTrace (prefixWord ++ tailWord_4919868) baseStart_4919868 baseEnd_4919868 := by
    simpa [prefixWord, tailWord_4919868, baseEnd_4919868] using wordTrace_append hprefix tailTrace_4919868
  have hstable : (prefixWord ++ tailWord_4919868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919868).length < 2 ^ (prefixWord ++ tailWord_4919868).sum := by decide
  have hdescent : baseEnd_4919868 < baseStart_4919868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919869 : List Nat := [1, 4, 1, 3, 2, 3, 1, 3, 1, 2, 2]
def baseStart_4919869 : Nat := 118140960795 + 4919869 * 2 ^ 59
def prefixEnd_4919869 : Nat := 4983230072969 + 3 ^ 40 * 4919869 * 2
def baseEnd_4919869 : Nat := 2526257554155116723611441

theorem tailTrace_4919869 : CollatzResearch.WordTrace tailWord_4919869 prefixEnd_4919869 2526257554155116723611441 := by
  unfold tailWord_4919869
  simp only [CollatzResearch.WordTrace]
  refine ⟨179442364213162334574850661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119628242808774889716567107 179442364213162334574850661)
  ·
    refine ⟨33645443289967937732784499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179442364213162334574850661 33645443289967937732784499)
    ·
      refine ⟨50468164934951906599176749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33645443289967937732784499 50468164934951906599176749)
      ·
        refine ⟨18925561850606964974691281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50468164934951906599176749 18925561850606964974691281)
        ·
          refine ⟨14194171387955223731018461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18925561850606964974691281 14194171387955223731018461)
          ·
            refine ⟨5322814270483208899131923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14194171387955223731018461 5322814270483208899131923)
            ·
              refine ⟨7984221405724813348697885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5322814270483208899131923 7984221405724813348697885)
              ·
                refine ⟨2994083027146805005761707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7984221405724813348697885 2994083027146805005761707)
                ·
                  refine ⟨4491124540720207508642561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2994083027146805005761707 4491124540720207508642561)
                  ·
                    refine ⟨3368343405540155631481921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4491124540720207508642561 3368343405540155631481921)
                    ·
                      refine ⟨2526257554155116723611441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3368343405540155631481921 2526257554155116723611441)
                      ·
                        rfl

theorem cell23_4919869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_4919869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919869 prefixEnd_4919869 := by exact prefixLift 4919869
  have htrace : WordTrace (prefixWord ++ tailWord_4919869) baseStart_4919869 baseEnd_4919869 := by
    simpa [prefixWord, tailWord_4919869, baseEnd_4919869] using wordTrace_append hprefix tailTrace_4919869
  have hstable : (prefixWord ++ tailWord_4919869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919869).length < 2 ^ (prefixWord ++ tailWord_4919869).sum := by decide
  have hdescent : baseEnd_4919869 < baseStart_4919869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919885 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_4919885 : Nat := 118140960795 + 4919885 * 2 ^ 59
def prefixEnd_4919885 : Nat := 4983230072969 + 3 ^ 40 * 4919885 * 2
def baseEnd_4919885 : Nat := 2526265769845588661011367

theorem tailTrace_4919885 : CollatzResearch.WordTrace tailWord_4919885 prefixEnd_4919885 2526265769845588661011367 := by
  unfold tailWord_4919885
  simp only [CollatzResearch.WordTrace]
  refine ⟨179442947781104369307433109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119628631854069579538288739 179442947781104369307433109)
  ·
    refine ⟨8411388177239267311285927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 179442947781104369307433109 8411388177239267311285927)
    ·
      refine ⟨12617082265858900966928891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8411388177239267311285927 12617082265858900966928891)
      ·
        refine ⟨18925623398788351450393337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12617082265858900966928891 18925623398788351450393337)
        ·
          refine ⟨14194217549091263587795003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18925623398788351450393337 14194217549091263587795003)
          ·
            refine ⟨21291326323636895381692505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14194217549091263587795003 21291326323636895381692505)
            ·
              refine ⟨15968494742727671536269379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21291326323636895381692505 15968494742727671536269379)
              ·
                refine ⟨23952742114091507304404069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15968494742727671536269379 23952742114091507304404069)
                ·
                  refine ⟨4491139146392157619575763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23952742114091507304404069 4491139146392157619575763)
                  ·
                    refine ⟨6736708719588236429363645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4491139146392157619575763 6736708719588236429363645)
                    ·
                      refine ⟨2526265769845588661011367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6736708719588236429363645 2526265769845588661011367)
                      ·
                        rfl

theorem cell23_4919885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_4919885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919885 prefixEnd_4919885 := by exact prefixLift 4919885
  have htrace : WordTrace (prefixWord ++ tailWord_4919885) baseStart_4919885 baseEnd_4919885 := by
    simpa [prefixWord, tailWord_4919885, baseEnd_4919885] using wordTrace_append hprefix tailTrace_4919885
  have hstable : (prefixWord ++ tailWord_4919885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919885).length < 2 ^ (prefixWord ++ tailWord_4919885).sum := by decide
  have hdescent : baseEnd_4919885 < baseStart_4919885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919908 : List Nat := [2, 3, 1, 1, 2, 2, 2, 3, 1, 4, 2]
def baseStart_4919908 : Nat := 118140960795 + 4919908 * 2 ^ 59
def prefixEnd_4919908 : Nat := 4983230072969 + 3 ^ 40 * 4919908 * 2
def baseEnd_4919908 : Nat := 2526277579900642071023761

theorem tailTrace_4919908 : CollatzResearch.WordTrace tailWord_4919908 prefixEnd_4919908 2526277579900642071023761 := by
  unfold tailWord_4919908
  simp only [CollatzResearch.WordTrace]
  refine ⟨89721893330010522117760189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119629191106680696157013585 89721893330010522117760189)
  ·
    refine ⟨33645709998753945794160071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89721893330010522117760189 33645709998753945794160071)
    ·
      refine ⟨50468564998130918691240107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33645709998753945794160071 50468564998130918691240107)
      ·
        refine ⟨75702847497196378036860161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50468564998130918691240107 75702847497196378036860161)
        ·
          refine ⟨56777135622897283527645121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75702847497196378036860161 56777135622897283527645121)
          ·
            refine ⟨42582851717172962645733841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56777135622897283527645121 42582851717172962645733841)
            ·
              refine ⟨31937138787879721984300381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42582851717172962645733841 31937138787879721984300381)
              ·
                refine ⟨11976427045454895744112643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31937138787879721984300381 11976427045454895744112643)
                ·
                  refine ⟨17964640568182343616168965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11976427045454895744112643 17964640568182343616168965)
                  ·
                    refine ⟨3368370106534189428031681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17964640568182343616168965 3368370106534189428031681)
                    ·
                      refine ⟨2526277579900642071023761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3368370106534189428031681 2526277579900642071023761)
                      ·
                        rfl

theorem cell23_4919908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 1, 4, 2].length) (baseStart_4919908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919908 prefixEnd_4919908 := by exact prefixLift 4919908
  have htrace : WordTrace (prefixWord ++ tailWord_4919908) baseStart_4919908 baseEnd_4919908 := by
    simpa [prefixWord, tailWord_4919908, baseEnd_4919908] using wordTrace_append hprefix tailTrace_4919908
  have hstable : (prefixWord ++ tailWord_4919908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919908).length < 2 ^ (prefixWord ++ tailWord_4919908).sum := by decide
  have hdescent : baseEnd_4919908 < baseStart_4919908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919982 : List Nat := [4, 1, 4, 1, 1, 2, 2, 3, 5]
def baseStart_4919982 : Nat := 118140960795 + 4919982 * 2 ^ 59
def prefixEnd_4919982 : Nat := 4983230072969 + 3 ^ 40 * 4919982 * 2
def baseEnd_4919982 : Nat := 280701730829897197944269

theorem tailTrace_4919982 : CollatzResearch.WordTrace tailWord_4919982 prefixEnd_4919982 280701730829897197944269 := by
  unfold tailWord_4919982
  simp only [CollatzResearch.WordTrace]
  refine ⟨22430810707719119359214275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119630990441168636582476133 22430810707719119359214275)
  ·
    refine ⟨33646216061578679038821413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22430810707719119359214275 33646216061578679038821413)
    ·
      refine ⟨6308665511546002319779015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33646216061578679038821413 6308665511546002319779015)
      ·
        refine ⟨9462998267319003479668523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6308665511546002319779015 9462998267319003479668523)
        ·
          refine ⟨14194497400978505219502785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9462998267319003479668523 14194497400978505219502785)
          ·
            refine ⟨10645873050733878914627089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14194497400978505219502785 10645873050733878914627089)
            ·
              refine ⟨7984404788050409185970317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10645873050733878914627089 7984404788050409185970317)
              ·
                refine ⟨2994151795518903444738869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7984404788050409185970317 2994151795518903444738869)
                ·
                  refine ⟨280701730829897197944269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2994151795518903444738869 280701730829897197944269)
                  ·
                    rfl

theorem cell23_4919982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_4919982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919982 prefixEnd_4919982 := by exact prefixLift 4919982
  have htrace : WordTrace (prefixWord ++ tailWord_4919982) baseStart_4919982 baseEnd_4919982 := by
    simpa [prefixWord, tailWord_4919982, baseEnd_4919982] using wordTrace_append hprefix tailTrace_4919982
  have hstable : (prefixWord ++ tailWord_4919982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919982).length < 2 ^ (prefixWord ++ tailWord_4919982).sum := by decide
  have hdescent : baseEnd_4919982 < baseStart_4919982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4919998 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_4919998 : Nat := 118140960795 + 4919998 * 2 ^ 59
def prefixEnd_4919998 : Nat := 4983230072969 + 3 ^ 40 * 4919998 * 2
def baseEnd_4919998 : Nat := 2526323793159546718898347

theorem tailTrace_4919998 : CollatzResearch.WordTrace tailWord_4919998 prefixEnd_4919998 2526323793159546718898347 := by
  unfold tailWord_4919998
  simp only [CollatzResearch.WordTrace]
  refine ⟨22430883653711873700787081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119631379486463326404197765 22430883653711873700787081)
  ·
    refine ⟨16823162740283905275590311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22430883653711873700787081 16823162740283905275590311)
    ·
      refine ⟨25234744110425857913385467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16823162740283905275590311 25234744110425857913385467)
      ·
        refine ⟨37852116165638786870078201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25234744110425857913385467 37852116165638786870078201)
        ·
          refine ⟨28389087124229090152558651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37852116165638786870078201 28389087124229090152558651)
          ·
            refine ⟨42583630686343635228837977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28389087124229090152558651 42583630686343635228837977)
            ·
              refine ⟨31937723014757726421628483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42583630686343635228837977 31937723014757726421628483)
              ·
                refine ⟨47906584522136589632442725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31937723014757726421628483 47906584522136589632442725)
                ·
                  refine ⟨8982484597900610556083011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47906584522136589632442725 8982484597900610556083011)
                  ·
                    refine ⟨13473726896850915834124517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8982484597900610556083011 13473726896850915834124517)
                    ·
                      refine ⟨2526323793159546718898347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13473726896850915834124517 2526323793159546718898347)
                      ·
                        rfl

theorem cell23_4919998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_4919998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4919998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4919998 prefixEnd_4919998 := by exact prefixLift 4919998
  have htrace : WordTrace (prefixWord ++ tailWord_4919998) baseStart_4919998 baseEnd_4919998 := by
    simpa [prefixWord, tailWord_4919998, baseEnd_4919998] using wordTrace_append hprefix tailTrace_4919998
  have hstable : (prefixWord ++ tailWord_4919998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4919998).length < 2 ^ (prefixWord ++ tailWord_4919998).sum := by decide
  have hdescent : baseEnd_4919998 < baseStart_4919998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4919998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920008 : List Nat := [2, 1, 3, 1, 2, 3, 1, 3, 3, 4]
def baseStart_4920008 : Nat := 118140960795 + 4920008 * 2 ^ 59
def prefixEnd_4920008 : Nat := 4983230072969 + 3 ^ 40 * 4920008 * 2
def baseEnd_4920008 : Nat := 842109642655363893257767

theorem tailTrace_4920008 : CollatzResearch.WordTrace tailWord_4920008 prefixEnd_4920008 842109642655363893257767 := by
  unfold tailWord_4920008
  simp only [CollatzResearch.WordTrace]
  refine ⟨89723716979829380657080339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119631622639772507542773785 89723716979829380657080339)
  ·
    refine ⟨134585575469744070985620509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89723716979829380657080339 134585575469744070985620509)
    ·
      refine ⟨50469590801154026619607691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134585575469744070985620509 50469590801154026619607691)
      ·
        refine ⟨75704386201731039929411537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50469590801154026619607691 75704386201731039929411537)
        ·
          refine ⟨56778289651298279947058653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75704386201731039929411537 56778289651298279947058653)
          ·
            refine ⟨21291858619236854980146995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56778289651298279947058653 21291858619236854980146995)
            ·
              refine ⟨31937787928855282470220493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21291858619236854980146995 31937787928855282470220493)
              ·
                refine ⟨11976670473320730926332685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31937787928855282470220493 11976670473320730926332685)
                ·
                  refine ⟨4491251427495274097374757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11976670473320730926332685 4491251427495274097374757)
                  ·
                    refine ⟨842109642655363893257767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4491251427495274097374757 842109642655363893257767)
                    ·
                      rfl

theorem cell23_4920008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_4920008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920008 prefixEnd_4920008 := by exact prefixLift 4920008
  have htrace : WordTrace (prefixWord ++ tailWord_4920008) baseStart_4920008 baseEnd_4920008 := by
    simpa [prefixWord, tailWord_4920008, baseEnd_4920008] using wordTrace_append hprefix tailTrace_4920008
  have hstable : (prefixWord ++ tailWord_4920008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920008).length < 2 ^ (prefixWord ++ tailWord_4920008).sum := by decide
  have hdescent : baseEnd_4920008 < baseStart_4920008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920051 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 5, 5]
def baseStart_4920051 : Nat := 118140960795 + 4920051 * 2 ^ 59
def prefixEnd_4920051 : Nat := 4983230072969 + 3 ^ 40 * 4920051 * 2
def baseEnd_4920051 : Nat := 842117002544745003845201

theorem tailTrace_4920051 : CollatzResearch.WordTrace tailWord_4920051 prefixEnd_4920051 842117002544745003845201 := by
  unfold tailWord_4920051
  simp only [CollatzResearch.WordTrace]
  refine ⟨179449002298502979657976007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119632668199001986438650671 179449002298502979657976007)
  ·
    refine ⟨269173503447754469486964011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179449002298502979657976007 269173503447754469486964011)
    ·
      refine ⟨403760255171631704230446017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269173503447754469486964011 403760255171631704230446017)
      ·
        refine ⟨302820191378723778172834513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 403760255171631704230446017 302820191378723778172834513)
        ·
          refine ⟨227115143534042833629625885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302820191378723778172834513 227115143534042833629625885)
          ·
            refine ⟨85168178825266062611109707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227115143534042833629625885 85168178825266062611109707)
            ·
              refine ⟨127752268237899093916664561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85168178825266062611109707 127752268237899093916664561)
              ·
                refine ⟨95814201178424320437498421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127752268237899093916664561 95814201178424320437498421)
                ·
                  refine ⟨8982581360477280041015477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95814201178424320437498421 8982581360477280041015477)
                  ·
                    refine ⟨842117002544745003845201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8982581360477280041015477 842117002544745003845201)
                    ·
                      rfl

theorem cell23_4920051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 5].length) (baseStart_4920051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920051 prefixEnd_4920051 := by exact prefixLift 4920051
  have htrace : WordTrace (prefixWord ++ tailWord_4920051) baseStart_4920051 baseEnd_4920051 := by
    simpa [prefixWord, tailWord_4920051, baseEnd_4920051] using wordTrace_append hprefix tailTrace_4920051
  have hstable : (prefixWord ++ tailWord_4920051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920051).length < 2 ^ (prefixWord ++ tailWord_4920051).sum := by decide
  have hdescent : baseEnd_4920051 < baseStart_4920051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920068 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 3, 5]
def baseStart_4920068 : Nat := 118140960795 + 4920068 * 2 ^ 59
def prefixEnd_4920068 : Nat := 4983230072969 + 3 ^ 40 * 4920068 * 2
def baseEnd_4920068 : Nat := 842119912268453815007675

theorem tailTrace_4920068 : CollatzResearch.WordTrace tailWord_4920068 prefixEnd_4920068 842119912268453815007675 := by
  unfold tailWord_4920068
  simp only [CollatzResearch.WordTrace]
  refine ⟨89724811169720695780672429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119633081559627594374229905 89724811169720695780672429)
  ·
    refine ⟨33646804188645260917752161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89724811169720695780672429 33646804188645260917752161)
    ·
      refine ⟨25235103141483945688314121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33646804188645260917752161 25235103141483945688314121)
      ·
        refine ⟨18926327356112959266235591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25235103141483945688314121 18926327356112959266235591)
        ·
          refine ⟨28389491034169438899353387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18926327356112959266235591 28389491034169438899353387)
          ·
            refine ⟨42584236551254158349030081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28389491034169438899353387 42584236551254158349030081)
            ·
              refine ⟨31938177413440618761772561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42584236551254158349030081 31938177413440618761772561)
              ·
                refine ⟨23953633060080464071329421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31938177413440618761772561 23953633060080464071329421)
                ·
                  refine ⟨8982612397530174026748533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23953633060080464071329421 8982612397530174026748533)
                  ·
                    refine ⟨842119912268453815007675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8982612397530174026748533 842119912268453815007675)
                    ·
                      rfl

theorem cell23_4920068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_4920068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920068 prefixEnd_4920068 := by exact prefixLift 4920068
  have htrace : WordTrace (prefixWord ++ tailWord_4920068) baseStart_4920068 baseEnd_4920068 := by
    simpa [prefixWord, tailWord_4920068, baseEnd_4920068] using wordTrace_append hprefix tailTrace_4920068
  have hstable : (prefixWord ++ tailWord_4920068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920068).length < 2 ^ (prefixWord ++ tailWord_4920068).sum := by decide
  have hdescent : baseEnd_4920068 < baseStart_4920068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920092 : List Nat := [2, 2, 3, 1, 1, 4, 2, 1, 2, 3, 2]
def baseStart_4920092 : Nat := 118140960795 + 4920092 * 2 ^ 59
def prefixEnd_4920092 : Nat := 4983230072969 + 3 ^ 40 * 4920092 * 2
def baseEnd_4920092 : Nat := 2526372060341069351122915

theorem tailTrace_4920092 : CollatzResearch.WordTrace tailWord_4920092 prefixEnd_4920092 2526372060341069351122915 := by
  unfold tailWord_4920092
  simp only [CollatzResearch.WordTrace]
  refine ⟨89725248845677221830109265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119633665127569629106812353 89725248845677221830109265)
  ·
    refine ⟨67293936634257916372581949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89725248845677221830109265 67293936634257916372581949)
    ·
      refine ⟨25235226237846718639718231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67293936634257916372581949 25235226237846718639718231)
      ·
        refine ⟨37852839356770077959577347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25235226237846718639718231 37852839356770077959577347)
        ·
          refine ⟨56779259035155116939366021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37852839356770077959577347 56779259035155116939366021)
          ·
            refine ⟨10646111069091584426131129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56779259035155116939366021 10646111069091584426131129)
            ·
              refine ⟨7984583301818688319598347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10646111069091584426131129 7984583301818688319598347)
              ·
                refine ⟨11976874952728032479397521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7984583301818688319598347 11976874952728032479397521)
                ·
                  refine ⟨8982656214546024359548141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11976874952728032479397521 8982656214546024359548141)
                  ·
                    refine ⟨3368496080454759134830553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8982656214546024359548141 3368496080454759134830553)
                    ·
                      refine ⟨2526372060341069351122915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3368496080454759134830553 2526372060341069351122915)
                      ·
                        rfl

theorem cell23_4920092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_4920092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920092 prefixEnd_4920092 := by exact prefixLift 4920092
  have htrace : WordTrace (prefixWord ++ tailWord_4920092) baseStart_4920092 baseEnd_4920092 := by
    simpa [prefixWord, tailWord_4920092, baseEnd_4920092] using wordTrace_append hprefix tailTrace_4920092
  have hstable : (prefixWord ++ tailWord_4920092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920092).length < 2 ^ (prefixWord ++ tailWord_4920092).sum := by decide
  have hdescent : baseEnd_4920092 < baseStart_4920092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920098 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 3, 6]
def baseStart_4920098 : Nat := 118140960795 + 4920098 * 2 ^ 59
def prefixEnd_4920098 : Nat := 4983230072969 + 3 ^ 40 * 4920098 * 2
def baseEnd_4920098 : Nat := 842125047074998775882629

theorem tailTrace_4920098 : CollatzResearch.WordTrace tailWord_4920098 prefixEnd_4920098 842125047074998775882629 := by
  unfold tailWord_4920098
  simp only [CollatzResearch.WordTrace]
  refine ⟨44862679132333176671234237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119633811019555137789957965 44862679132333176671234237)
  ·
    refine ⟨16823504674624941251712839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44862679132333176671234237 16823504674624941251712839)
    ·
      refine ⟨25235257011937411877569259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16823504674624941251712839 25235257011937411877569259)
      ·
        refine ⟨37852885517906117816353889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25235257011937411877569259 37852885517906117816353889)
        ·
          refine ⟨28389664138429588362265417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37852885517906117816353889 28389664138429588362265417)
          ·
            refine ⟨21292248103822191271699063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28389664138429588362265417 21292248103822191271699063)
            ·
              refine ⟨31938372155733286907548595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21292248103822191271699063 31938372155733286907548595)
              ·
                refine ⟨47907558233599930361322893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31938372155733286907548595 47907558233599930361322893)
                ·
                  refine ⟨17965334337599973885496085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47907558233599930361322893 17965334337599973885496085)
                  ·
                    refine ⟨842125047074998775882629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17965334337599973885496085 842125047074998775882629)
                    ·
                      rfl

theorem cell23_4920098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_4920098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920098 prefixEnd_4920098 := by exact prefixLift 4920098
  have htrace : WordTrace (prefixWord ++ tailWord_4920098) baseStart_4920098 baseEnd_4920098 := by
    simpa [prefixWord, tailWord_4920098, baseEnd_4920098] using wordTrace_append hprefix tailTrace_4920098
  have hstable : (prefixWord ++ tailWord_4920098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920098).length < 2 ^ (prefixWord ++ tailWord_4920098).sum := by decide
  have hdescent : baseEnd_4920098 < baseStart_4920098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920105 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 5, 2, 2]
def baseStart_4920105 : Nat := 118140960795 + 4920105 * 2 ^ 59
def prefixEnd_4920105 : Nat := 4983230072969 + 3 ^ 40 * 4920105 * 2
def baseEnd_4920105 : Nat := 2526378735589577800260355

theorem tailTrace_4920105 : CollatzResearch.WordTrace tailWord_4920105 prefixEnd_4920105 2526378735589577800260355 := by
  unfold tailWord_4920105
  simp only [CollatzResearch.WordTrace]
  refine ⟨179450971840307346880441769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119633981226871564586961179 179450971840307346880441769)
  ·
    refine ⟨134588228880230510160331327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179450971840307346880441769 134588228880230510160331327)
    ·
      refine ⟨201882343320345765240496991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134588228880230510160331327 201882343320345765240496991)
      ·
        refine ⟨302823514980518647860745487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201882343320345765240496991 302823514980518647860745487)
        ·
          refine ⟨454235272470777971791118231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302823514980518647860745487 454235272470777971791118231)
          ·
            refine ⟨681352908706166957686677347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454235272470777971791118231 681352908706166957686677347)
            ·
              refine ⟨1022029363059250436530016021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681352908706166957686677347 1022029363059250436530016021)
              ·
                refine ⟨47907626393402364212344501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1022029363059250436530016021 47907626393402364212344501)
                ·
                  refine ⟨4491339974381471644907297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47907626393402364212344501 4491339974381471644907297)
                  ·
                    refine ⟨3368504980786103733680473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4491339974381471644907297 3368504980786103733680473)
                    ·
                      refine ⟨2526378735589577800260355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3368504980786103733680473 2526378735589577800260355)
                      ·
                        rfl

theorem cell23_4920105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 2, 2].length) (baseStart_4920105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920105 prefixEnd_4920105 := by exact prefixLift 4920105
  have htrace : WordTrace (prefixWord ++ tailWord_4920105) baseStart_4920105 baseEnd_4920105 := by
    simpa [prefixWord, tailWord_4920105, baseEnd_4920105] using wordTrace_append hprefix tailTrace_4920105
  have hstable : (prefixWord ++ tailWord_4920105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920105).length < 2 ^ (prefixWord ++ tailWord_4920105).sum := by decide
  have hdescent : baseEnd_4920105 < baseStart_4920105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920115 : List Nat := [1, 1, 1, 2, 6, 1, 1, 4, 2, 4]
def baseStart_4920115 : Nat := 118140960795 + 4920115 * 2 ^ 59
def prefixEnd_4920115 : Nat := 4983230072969 + 3 ^ 40 * 4920115 * 2
def baseEnd_4920115 : Nat := 842127956798707587045103

theorem tailTrace_4920115 : CollatzResearch.WordTrace tailWord_4920115 prefixEnd_4920115 842127956798707587045103 := by
  unfold tailWord_4920115
  simp only [CollatzResearch.WordTrace]
  refine ⟨179451336570271118588305799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119634224380180745725537199 179451336570271118588305799)
  ·
    refine ⟨269177004855406677882458699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179451336570271118588305799 269177004855406677882458699)
    ·
      refine ⟨403765507283110016823688049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269177004855406677882458699 403765507283110016823688049)
      ·
        refine ⟨302824130462332512617766037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 403765507283110016823688049 302824130462332512617766037)
        ·
          refine ⟨14194881115421836528957783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 302824130462332512617766037 14194881115421836528957783)
          ·
            refine ⟨21292321673132754793436675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14194881115421836528957783 21292321673132754793436675)
            ·
              refine ⟨31938482509699132190155013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21292321673132754793436675 31938482509699132190155013)
              ·
                refine ⟨5988465470568587285654065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31938482509699132190155013 5988465470568587285654065)
                ·
                  refine ⟨4491349102926440464240549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5988465470568587285654065 4491349102926440464240549)
                  ·
                    refine ⟨842127956798707587045103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4491349102926440464240549 842127956798707587045103)
                    ·
                      rfl

theorem cell23_4920115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 4].length) (baseStart_4920115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920115 prefixEnd_4920115 := by exact prefixLift 4920115
  have htrace : WordTrace (prefixWord ++ tailWord_4920115) baseStart_4920115 baseEnd_4920115 := by
    simpa [prefixWord, tailWord_4920115, baseEnd_4920115] using wordTrace_append hprefix tailTrace_4920115
  have hstable : (prefixWord ++ tailWord_4920115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920115).length < 2 ^ (prefixWord ++ tailWord_4920115).sum := by decide
  have hdescent : baseEnd_4920115 < baseStart_4920115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920116 : List Nat := [2, 5, 1, 1, 3, 1, 1, 4, 1, 1, 3]
def baseStart_4920116 : Nat := 118140960795 + 4920116 * 2 ^ 59
def prefixEnd_4920116 : Nat := 4983230072969 + 3 ^ 40 * 4920116 * 2
def baseEnd_4920116 : Nat := 2526384383876777257222805

theorem tailTrace_4920116 : CollatzResearch.WordTrace tailWord_4920116 prefixEnd_4920116 2526384383876777257222805 := by
  unfold tailWord_4920116
  simp only [CollatzResearch.WordTrace]
  refine ⟨89725686521633747879546101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119634248695511663839394801 89725686521633747879546101)
  ·
    refine ⟨8411783111403163863707447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89725686521633747879546101 8411783111403163863707447)
    ·
      refine ⟨12617674667104745795561171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8411783111403163863707447 12617674667104745795561171)
      ·
        refine ⟨18926512000657118693341757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12617674667104745795561171 18926512000657118693341757)
        ·
          refine ⟨7097442000246419510003159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18926512000657118693341757 7097442000246419510003159)
          ·
            refine ⟨10646163000369629265004739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7097442000246419510003159 10646163000369629265004739)
            ·
              refine ⟨15969244500554443897507109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10646163000369629265004739 15969244500554443897507109)
              ·
                refine ⟨2994233343853958230782583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15969244500554443897507109 2994233343853958230782583)
                ·
                  refine ⟨4491350015780937346173875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2994233343853958230782583 4491350015780937346173875)
                  ·
                    refine ⟨6737025023671406019260813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4491350015780937346173875 6737025023671406019260813)
                    ·
                      refine ⟨2526384383876777257222805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6737025023671406019260813 2526384383876777257222805)
                      ·
                        rfl

theorem cell23_4920116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_4920116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920116 prefixEnd_4920116 := by exact prefixLift 4920116
  have htrace : WordTrace (prefixWord ++ tailWord_4920116) baseStart_4920116 baseEnd_4920116 := by
    simpa [prefixWord, tailWord_4920116, baseEnd_4920116] using wordTrace_append hprefix tailTrace_4920116
  have hstable : (prefixWord ++ tailWord_4920116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920116).length < 2 ^ (prefixWord ++ tailWord_4920116).sum := by decide
  have hdescent : baseEnd_4920116 < baseStart_4920116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920145 : List Nat := [1, 2, 2, 1, 6, 1, 3, 7]
def baseStart_4920145 : Nat := 118140960795 + 4920145 * 2 ^ 59
def prefixEnd_4920145 : Nat := 4983230072969 + 3 ^ 40 * 4920145 * 2
def baseEnd_4920145 : Nat := 93570343511694727546673

theorem tailTrace_4920145 : CollatzResearch.WordTrace tailWord_4920145 prefixEnd_4920145 93570343511694727546673 := by
  unfold tailWord_4920145
  simp only [CollatzResearch.WordTrace]
  refine ⟨179452430760162433711897889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119634953840108289141265259 179452430760162433711897889)
  ·
    refine ⟨134589323070121825283923417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179452430760162433711897889 134589323070121825283923417)
    ·
      refine ⟨100941992302591368962942563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134589323070121825283923417 100941992302591368962942563)
      ·
        refine ⟨151412988453887053444413845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100941992302591368962942563 151412988453887053444413845)
        ·
          refine ⟨7097483833775955630206899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 151412988453887053444413845 7097483833775955630206899)
          ·
            refine ⟨10646225750663933445310349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7097483833775955630206899 10646225750663933445310349)
            ·
              refine ⟨3992334656498975041991381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10646225750663933445310349 3992334656498975041991381)
              ·
                refine ⟨93570343511694727546673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3992334656498975041991381 93570343511694727546673)
                ·
                  rfl

theorem cell23_4920145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 7].length) (baseStart_4920145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920145 prefixEnd_4920145 := by exact prefixLift 4920145
  have htrace : WordTrace (prefixWord ++ tailWord_4920145) baseStart_4920145 baseEnd_4920145 := by
    simpa [prefixWord, tailWord_4920145, baseEnd_4920145] using wordTrace_append hprefix tailTrace_4920145
  have hstable : (prefixWord ++ tailWord_4920145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920145).length < 2 ^ (prefixWord ++ tailWord_4920145).sum := by decide
  have hdescent : baseEnd_4920145 < baseStart_4920145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920156 : List Nat := [2, 2, 4, 2, 1, 1, 1, 5, 1, 2, 2]
def baseStart_4920156 : Nat := 118140960795 + 4920156 * 2 ^ 59
def prefixEnd_4920156 : Nat := 4983230072969 + 3 ^ 40 * 4920156 * 2
def baseEnd_4920156 : Nat := 2526404923102957100722621

theorem tailTrace_4920156 : CollatzResearch.WordTrace tailWord_4920156 prefixEnd_4920156 2526404923102957100722621 := by
  unfold tailWord_4920156
  simp only [CollatzResearch.WordTrace]
  refine ⟨89726415981561291295274161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119635221308748388393698881 89726415981561291295274161)
  ·
    refine ⟨67294811986170968471455621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89726415981561291295274161 67294811986170968471455621)
    ·
      refine ⟨12617777247407056588397929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67294811986170968471455621 12617777247407056588397929)
      ·
        refine ⟨9463332935555292441298447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12617777247407056588397929 9463332935555292441298447)
        ·
          refine ⟨14194999403332938661947671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9463332935555292441298447 14194999403332938661947671)
          ·
            refine ⟨21292499104999407992921507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14194999403332938661947671 21292499104999407992921507)
            ·
              refine ⟨31938748657499111989382261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21292499104999407992921507 31938748657499111989382261)
              ·
                refine ⟨2994257686640541749004587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31938748657499111989382261 2994257686640541749004587)
                ·
                  refine ⟨4491386529960812623506881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2994257686640541749004587 4491386529960812623506881)
                  ·
                    refine ⟨3368539897470609467630161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4491386529960812623506881 3368539897470609467630161)
                    ·
                      refine ⟨2526404923102957100722621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3368539897470609467630161 2526404923102957100722621)
                      ·
                        rfl

theorem cell23_4920156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_4920156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920156 prefixEnd_4920156 := by exact prefixLift 4920156
  have htrace : WordTrace (prefixWord ++ tailWord_4920156) baseStart_4920156 baseEnd_4920156 := by
    simpa [prefixWord, tailWord_4920156, baseEnd_4920156] using wordTrace_append hprefix tailTrace_4920156
  have hstable : (prefixWord ++ tailWord_4920156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920156).length < 2 ^ (prefixWord ++ tailWord_4920156).sum := by decide
  have hdescent : baseEnd_4920156 < baseStart_4920156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920178 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 1, 5, 4]
def baseStart_4920178 : Nat := 118140960795 + 4920178 * 2 ^ 59
def prefixEnd_4920178 : Nat := 4983230072969 + 3 ^ 40 * 4920178 * 2
def baseEnd_4920178 : Nat := 2526416219677356014647519

theorem tailTrace_4920178 : CollatzResearch.WordTrace tailWord_4920178 prefixEnd_4920178 2526416219677356014647519 := by
  unfold tailWord_4920178
  simp only [CollatzResearch.WordTrace]
  refine ⟨44863408592260720086962297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119635756246028586898566125 44863408592260720086962297)
  ·
    refine ⟨33647556444195540065221723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44863408592260720086962297 33647556444195540065221723)
    ·
      refine ⟨50471334666293310097832585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33647556444195540065221723 50471334666293310097832585)
      ·
        refine ⟨37853500999719982573374439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50471334666293310097832585 37853500999719982573374439)
        ·
          refine ⟨56780251499579973860061659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37853500999719982573374439 56780251499579973860061659)
          ·
            refine ⟨85170377249369960790092489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56780251499579973860061659 85170377249369960790092489)
            ·
              refine ⟨63877782937027470592569367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85170377249369960790092489 63877782937027470592569367)
              ·
                refine ⟨95816674405541205888854051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63877782937027470592569367 95816674405541205888854051)
                ·
                  refine ⟨143725011608311808833281077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95816674405541205888854051 143725011608311808833281077)
                  ·
                    refine ⟨13474219838279232078120101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 143725011608311808833281077 13474219838279232078120101)
                    ·
                      refine ⟨2526416219677356014647519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13474219838279232078120101 2526416219677356014647519)
                      ·
                        rfl

theorem cell23_4920178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_4920178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920178 prefixEnd_4920178 := by exact prefixLift 4920178
  have htrace : WordTrace (prefixWord ++ tailWord_4920178) baseStart_4920178 baseEnd_4920178 := by
    simpa [prefixWord, tailWord_4920178, baseEnd_4920178] using wordTrace_append hprefix tailTrace_4920178
  have hstable : (prefixWord ++ tailWord_4920178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920178).length < 2 ^ (prefixWord ++ tailWord_4920178).sum := by decide
  have hdescent : baseEnd_4920178 < baseStart_4920178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920199 : List Nat := [1, 1, 4, 2, 3, 2, 2, 2, 1, 3, 2]
def baseStart_4920199 : Nat := 118140960795 + 4920199 * 2 ^ 59
def prefixEnd_4920199 : Nat := 4983230072969 + 3 ^ 40 * 4920199 * 2
def baseEnd_4920199 : Nat := 2526427002771100432484923

theorem tailTrace_4920199 : CollatzResearch.WordTrace tailWord_4920199 prefixEnd_4920199 2526427002771100432484923 := by
  unfold tailWord_4920199
  simp only [CollatzResearch.WordTrace]
  refine ⟨179454400301966800934363651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119636266867977867289575767 179454400301966800934363651)
  ·
    refine ⟨269181600452950201401545477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179454400301966800934363651 269181600452950201401545477)
    ·
      refine ⟨50471550084928162762789777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 269181600452950201401545477 50471550084928162762789777)
      ·
        refine ⟨37853662563696122072092333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50471550084928162762789777 37853662563696122072092333)
        ·
          refine ⟨14195123461386045777034625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37853662563696122072092333 14195123461386045777034625)
          ·
            refine ⟨10646342596039534332775969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14195123461386045777034625 10646342596039534332775969)
            ·
              refine ⟨7984756947029650749581977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10646342596039534332775969 7984756947029650749581977)
              ·
                refine ⟨5988567710272238062186483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7984756947029650749581977 5988567710272238062186483)
                ·
                  refine ⟨8982851565408357093279725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5988567710272238062186483 8982851565408357093279725)
                  ·
                    refine ⟨3368569337028133909979897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8982851565408357093279725 3368569337028133909979897)
                    ·
                      refine ⟨2526427002771100432484923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3368569337028133909979897 2526427002771100432484923)
                      ·
                        rfl

theorem cell23_4920199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_4920199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920199 prefixEnd_4920199 := by exact prefixLift 4920199
  have htrace : WordTrace (prefixWord ++ tailWord_4920199) baseStart_4920199 baseEnd_4920199 := by
    simpa [prefixWord, tailWord_4920199, baseEnd_4920199] using wordTrace_append hprefix tailTrace_4920199
  have hstable : (prefixWord ++ tailWord_4920199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920199).length < 2 ^ (prefixWord ++ tailWord_4920199).sum := by decide
  have hdescent : baseEnd_4920199 < baseStart_4920199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920212 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 3, 4, 2]
def baseStart_4920212 : Nat := 118140960795 + 4920212 * 2 ^ 59
def prefixEnd_4920212 : Nat := 4983230072969 + 3 ^ 40 * 4920212 * 2
def baseEnd_4920212 : Nat := 2526433678019608881622363

theorem tailTrace_4920212 : CollatzResearch.WordTrace tailWord_4920212 prefixEnd_4920212 2526433678019608881622363 := by
  unfold tailWord_4920212
  simp only [CollatzResearch.WordTrace]
  refine ⟨89727437225459852077293445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119636582967279802769724593 89727437225459852077293445)
  ·
    refine ⟨16823894479773722264492521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89727437225459852077293445 16823894479773722264492521)
    ·
      refine ⟨12617920859830291698369391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16823894479773722264492521 12617920859830291698369391)
      ·
        refine ⟨18926881289745437547554087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12617920859830291698369391 18926881289745437547554087)
        ·
          refine ⟨28390321934618156321331131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18926881289745437547554087 28390321934618156321331131)
          ·
            refine ⟨42585482901927234481996697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28390321934618156321331131 42585482901927234481996697)
            ·
              refine ⟨31939112176445425861497523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42585482901927234481996697 31939112176445425861497523)
              ·
                refine ⟨47908668264668138792246285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31939112176445425861497523 47908668264668138792246285)
                ·
                  refine ⟨17965750599250552047092357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47908668264668138792246285 17965750599250552047092357)
                  ·
                    refine ⟨3368578237359478508829817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17965750599250552047092357 3368578237359478508829817)
                    ·
                      refine ⟨2526433678019608881622363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3368578237359478508829817 2526433678019608881622363)
                      ·
                        rfl

theorem cell23_4920212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_4920212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920212 prefixEnd_4920212 := by exact prefixLift 4920212
  have htrace : WordTrace (prefixWord ++ tailWord_4920212) baseStart_4920212 baseEnd_4920212 := by
    simpa [prefixWord, tailWord_4920212, baseEnd_4920212] using wordTrace_append hprefix tailTrace_4920212
  have hstable : (prefixWord ++ tailWord_4920212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920212).length < 2 ^ (prefixWord ++ tailWord_4920212).sum := by decide
  have hdescent : baseEnd_4920212 < baseStart_4920212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920228 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 1, 2, 7]
def baseStart_4920228 : Nat := 118140960795 + 4920228 * 2 ^ 59
def prefixEnd_4920228 : Nat := 4983230072969 + 3 ^ 40 * 4920228 * 2
def baseEnd_4920228 : Nat := 2526441893710080819022289

theorem tailTrace_4920228 : CollatzResearch.WordTrace tailWord_4920228 prefixEnd_4920228 2526441893710080819022289 := by
  unfold tailWord_4920228
  simp only [CollatzResearch.WordTrace]
  refine ⟨89727729009430869443584669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119636972012574492591446225 89727729009430869443584669)
  ·
    refine ⟨33647898378536576041344251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89727729009430869443584669 33647898378536576041344251)
    ·
      refine ⟨50471847567804864062016377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33647898378536576041344251 50471847567804864062016377)
      ·
        refine ⟨37853885675853648046512283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50471847567804864062016377 37853885675853648046512283)
        ·
          refine ⟨56780828513780472069768425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37853885675853648046512283 56780828513780472069768425)
          ·
            refine ⟨42585621385335354052326319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56780828513780472069768425 42585621385335354052326319)
            ·
              refine ⟨63878432078003031078489479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42585621385335354052326319 63878432078003031078489479)
              ·
                refine ⟨95817648117004546617734219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63878432078003031078489479 95817648117004546617734219)
                ·
                  refine ⟨143726472175506819926601329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95817648117004546617734219 143726472175506819926601329)
                  ·
                    refine ⟨107794854131630114944950997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 143726472175506819926601329 107794854131630114944950997)
                    ·
                      refine ⟨2526441893710080819022289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107794854131630114944950997 2526441893710080819022289)
                      ·
                        rfl

theorem cell23_4920228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_4920228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920228 prefixEnd_4920228 := by exact prefixLift 4920228
  have htrace : WordTrace (prefixWord ++ tailWord_4920228) baseStart_4920228 baseEnd_4920228 := by
    simpa [prefixWord, tailWord_4920228, baseEnd_4920228] using wordTrace_append hprefix tailTrace_4920228
  have hstable : (prefixWord ++ tailWord_4920228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920228).length < 2 ^ (prefixWord ++ tailWord_4920228).sum := by decide
  have hdescent : baseEnd_4920228 < baseStart_4920228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920245 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 1, 5, 3]
def baseStart_4920245 : Nat := 118140960795 + 4920245 * 2 ^ 59
def prefixEnd_4920245 : Nat := 4983230072969 + 3 ^ 40 * 4920245 * 2
def baseEnd_4920245 : Nat := 2526450622881207252509711

theorem tailTrace_4920245 : CollatzResearch.WordTrace tailWord_4920245 prefixEnd_4920245 2526450622881207252509711 := by
  unfold tailWord_4920245
  simp only [CollatzResearch.WordTrace]
  refine ⟨179456078059800150790538189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119637385373200100527025459 179456078059800150790538189)
  ·
    refine ⟨67296029272425056546451821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179456078059800150790538189 67296029272425056546451821)
    ·
      refine ⟨25236010977159396204919433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67296029272425056546451821 25236010977159396204919433)
      ·
        refine ⟨18927008232869547153689575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25236010977159396204919433 18927008232869547153689575)
        ·
          refine ⟨28390512349304320730534363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18927008232869547153689575 28390512349304320730534363)
          ·
            refine ⟨42585768523956481095801545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28390512349304320730534363 42585768523956481095801545)
            ·
              refine ⟨31939326392967360821851159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42585768523956481095801545 31939326392967360821851159)
              ·
                refine ⟨47908989589451041232776739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31939326392967360821851159 47908989589451041232776739)
                ·
                  refine ⟨71863484384176561849165109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47908989589451041232776739 71863484384176561849165109)
                  ·
                    refine ⟨6737201661016552673359229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71863484384176561849165109 6737201661016552673359229)
                    ·
                      refine ⟨2526450622881207252509711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6737201661016552673359229 2526450622881207252509711)
                      ·
                        rfl

theorem cell23_4920245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_4920245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920245 prefixEnd_4920245 := by exact prefixLift 4920245
  have htrace : WordTrace (prefixWord ++ tailWord_4920245) baseStart_4920245 baseEnd_4920245 := by
    simpa [prefixWord, tailWord_4920245, baseEnd_4920245] using wordTrace_append hprefix tailTrace_4920245
  have hstable : (prefixWord ++ tailWord_4920245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920245).length < 2 ^ (prefixWord ++ tailWord_4920245).sum := by decide
  have hdescent : baseEnd_4920245 < baseStart_4920245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920255 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 4, 5, 2]
def baseStart_4920255 : Nat := 118140960795 + 4920255 * 2 ^ 59
def prefixEnd_4920255 : Nat := 4983230072969 + 3 ^ 40 * 4920255 * 2
def baseEnd_4920255 : Nat := 2526455757687752213384665

theorem tailTrace_4920255 : CollatzResearch.WordTrace tailWord_4920255 prefixEnd_4920255 2526455757687752213384665 := by
  unfold tailWord_4920255
  simp only [CollatzResearch.WordTrace]
  refine ⟨179456442789763922498402219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119637628526509281665601479 179456442789763922498402219)
  ·
    refine ⟨269184664184645883747603329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179456442789763922498402219 269184664184645883747603329)
    ·
      refine ⟨201888498138484412810702497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269184664184645883747603329 201888498138484412810702497)
      ·
        refine ⟨151416373603863309608026873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201888498138484412810702497 151416373603863309608026873)
        ·
          refine ⟨113562280202897482206020155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151416373603863309608026873 113562280202897482206020155)
          ·
            refine ⟨170343420304346223309030233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113562280202897482206020155 170343420304346223309030233)
            ·
              refine ⟨127757565228259667481772675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170343420304346223309030233 127757565228259667481772675)
              ·
                refine ⟨191636347842389501222659013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127757565228259667481772675 191636347842389501222659013)
                ·
                  refine ⟨35931815220448031479248565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 191636347842389501222659013 35931815220448031479248565)
                  ·
                    refine ⟨3368607676917002951179553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35931815220448031479248565 3368607676917002951179553)
                    ·
                      refine ⟨2526455757687752213384665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3368607676917002951179553 2526455757687752213384665)
                      ·
                        rfl

theorem cell23_4920255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 5, 2].length) (baseStart_4920255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920255 prefixEnd_4920255 := by exact prefixLift 4920255
  have htrace : WordTrace (prefixWord ++ tailWord_4920255) baseStart_4920255 baseEnd_4920255 := by
    simpa [prefixWord, tailWord_4920255, baseEnd_4920255] using wordTrace_append hprefix tailTrace_4920255
  have hstable : (prefixWord ++ tailWord_4920255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920255).length < 2 ^ (prefixWord ++ tailWord_4920255).sum := by decide
  have hdescent : baseEnd_4920255 < baseStart_4920255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920392 : List Nat := [2, 1, 3, 1, 1, 1, 3, 5, 1, 1, 4]
def baseStart_4920392 : Nat := 118140960795 + 4920392 * 2 ^ 59
def prefixEnd_4920392 : Nat := 4983230072969 + 3 ^ 40 * 4920392 * 2
def baseEnd_4920392 : Nat := 2526526104537418177371535

theorem tailTrace_4920392 : CollatzResearch.WordTrace tailWord_4920392 prefixEnd_4920392 2526526104537418177371535 := by
  unfold tailWord_4920392
  simp only [CollatzResearch.WordTrace]
  refine ⟨89730719795133797448069715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119640959726845063264092953 89730719795133797448069715)
  ·
    refine ⟨134596079692700696172104573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89730719795133797448069715 134596079692700696172104573)
    ·
      refine ⟨50473529884762761064539215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134596079692700696172104573 50473529884762761064539215)
      ·
        refine ⟨75710294827144141596808823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50473529884762761064539215 75710294827144141596808823)
        ·
          refine ⟨113565442240716212395213235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75710294827144141596808823 113565442240716212395213235)
          ·
            refine ⟨170348163361074318592819853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113565442240716212395213235 170348163361074318592819853)
            ·
              refine ⟨63880561260402869472307445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170348163361074318592819853 63880561260402869472307445)
              ·
                refine ⟨5988802618162769013028823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63880561260402869472307445 5988802618162769013028823)
                ·
                  refine ⟨8983203927244153519543235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5988802618162769013028823 8983203927244153519543235)
                  ·
                    refine ⟨13474805890866230279314853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8983203927244153519543235 13474805890866230279314853)
                    ·
                      refine ⟨2526526104537418177371535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13474805890866230279314853 2526526104537418177371535)
                      ·
                        rfl

theorem cell23_4920392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_4920392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920392 prefixEnd_4920392 := by exact prefixLift 4920392
  have htrace : WordTrace (prefixWord ++ tailWord_4920392) baseStart_4920392 baseEnd_4920392 := by
    simpa [prefixWord, tailWord_4920392, baseEnd_4920392] using wordTrace_append hprefix tailTrace_4920392
  have hstable : (prefixWord ++ tailWord_4920392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920392).length < 2 ^ (prefixWord ++ tailWord_4920392).sum := by decide
  have hdescent : baseEnd_4920392 < baseStart_4920392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920405 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 3, 1, 6]
def baseStart_4920405 : Nat := 118140960795 + 4920405 * 2 ^ 59
def prefixEnd_4920405 : Nat := 4983230072969 + 3 ^ 40 * 4920405 * 2
def baseEnd_4920405 : Nat := 2526532779785926626508975

theorem tailTrace_4920405 : CollatzResearch.WordTrace tailWord_4920405 prefixEnd_4920405 2526532779785926626508975 := by
  unfold tailWord_4920405
  simp only [CollatzResearch.WordTrace]
  refine ⟨179461913739220498116362669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119641275826146998744241779 179461913739220498116362669)
  ·
    refine ⟨67298217652207686793636001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179461913739220498116362669 67298217652207686793636001)
    ·
      refine ⟨50473663239155765095227001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67298217652207686793636001 50473663239155765095227001)
      ·
        refine ⟨37855247429366823821420251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50473663239155765095227001 37855247429366823821420251)
        ·
          refine ⟨56782871144050235732130377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37855247429366823821420251 56782871144050235732130377)
          ·
            refine ⟨42587153358037676799097783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56782871144050235732130377 42587153358037676799097783)
            ·
              refine ⟨63880730037056515198646675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42587153358037676799097783 63880730037056515198646675)
              ·
                refine ⟨95821095055584772797970013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63880730037056515198646675 95821095055584772797970013)
                ·
                  refine ⟨35932910645844289799238755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95821095055584772797970013 35932910645844289799238755)
                  ·
                    refine ⟨53899365968766434698858133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35932910645844289799238755 53899365968766434698858133)
                    ·
                      refine ⟨2526532779785926626508975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53899365968766434698858133 2526532779785926626508975)
                      ·
                        rfl

theorem cell23_4920405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_4920405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920405 prefixEnd_4920405 := by exact prefixLift 4920405
  have htrace : WordTrace (prefixWord ++ tailWord_4920405) baseStart_4920405 baseEnd_4920405 := by
    simpa [prefixWord, tailWord_4920405, baseEnd_4920405] using wordTrace_append hprefix tailTrace_4920405
  have hstable : (prefixWord ++ tailWord_4920405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920405).length < 2 ^ (prefixWord ++ tailWord_4920405).sum := by decide
  have hdescent : baseEnd_4920405 < baseStart_4920405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920409 : List Nat := [1, 2, 1, 2, 2, 1, 2, 5, 3, 2, 2]
def baseStart_4920409 : Nat := 118140960795 + 4920409 * 2 ^ 59
def prefixEnd_4920409 : Nat := 4983230072969 + 3 ^ 40 * 4920409 * 2
def baseEnd_4920409 : Nat := 2526534833708544610858957

theorem tailTrace_4920409 : CollatzResearch.WordTrace tailWord_4920409 prefixEnd_4920409 2526534833708544610858957 := by
  unfold tailWord_4920409
  simp only [CollatzResearch.WordTrace]
  refine ⟨179462059631206006799508281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119641373087470671199672187 179462059631206006799508281)
  ·
    refine ⟨134596544723404505099631211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179462059631206006799508281 134596544723404505099631211)
    ·
      refine ⟨201894817085106757649446817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134596544723404505099631211 201894817085106757649446817)
      ·
        refine ⟨151421112813830068237085113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201894817085106757649446817 151421112813830068237085113)
        ·
          refine ⟨113565834610372551177813835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151421112813830068237085113 113565834610372551177813835)
          ·
            refine ⟨170348751915558826766720753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113565834610372551177813835 170348751915558826766720753)
            ·
              refine ⟨127761563936669120075040565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170348751915558826766720753 127761563936669120075040565)
              ·
                refine ⟨11977646619062730007035053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127761563936669120075040565 11977646619062730007035053)
                ·
                  refine ⟨4491617482148523752638145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11977646619062730007035053 4491617482148523752638145)
                  ·
                    refine ⟨3368713111611392814478609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4491617482148523752638145 3368713111611392814478609)
                    ·
                      refine ⟨2526534833708544610858957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3368713111611392814478609 2526534833708544610858957)
                      ·
                        rfl

theorem cell23_4920409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 2, 2].length) (baseStart_4920409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920409 prefixEnd_4920409 := by exact prefixLift 4920409
  have htrace : WordTrace (prefixWord ++ tailWord_4920409) baseStart_4920409 baseEnd_4920409 := by
    simpa [prefixWord, tailWord_4920409, baseEnd_4920409] using wordTrace_append hprefix tailTrace_4920409
  have hstable : (prefixWord ++ tailWord_4920409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920409).length < 2 ^ (prefixWord ++ tailWord_4920409).sum := by decide
  have hdescent : baseEnd_4920409 < baseStart_4920409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920412 : List Nat := [2, 2, 4, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_4920412 : Nat := 118140960795 + 4920412 * 2 ^ 59
def prefixEnd_4920412 : Nat := 4983230072969 + 3 ^ 40 * 4920412 * 2
def baseEnd_4920412 : Nat := 2526536374150508099121443

theorem tailTrace_4920412 : CollatzResearch.WordTrace tailWord_4920412 prefixEnd_4920412 2526536374150508099121443 := by
  unfold tailWord_4920412
  simp only [CollatzResearch.WordTrace]
  refine ⟨89731084525097569155933745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119641446033463425541244993 89731084525097569155933745)
  ·
    refine ⟨67298313393823176866950309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89731084525097569155933745 67298313393823176866950309)
    ·
      refine ⟨12618433761341845662553183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67298313393823176866950309 12618433761341845662553183)
      ·
        refine ⟨18927650642012768493829775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12618433761341845662553183 18927650642012768493829775)
        ·
          refine ⟨28391475963019152740744663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18927650642012768493829775 28391475963019152740744663)
          ·
            refine ⟨42587213944528729111116995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28391475963019152740744663 42587213944528729111116995)
            ·
              refine ⟨63880820916793093666675493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42587213944528729111116995 63880820916793093666675493)
              ·
                refine ⟨11977653921898705062501655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63880820916793093666675493 11977653921898705062501655)
                ·
                  refine ⟨17966480882848057593752483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11977653921898705062501655 17966480882848057593752483)
                  ·
                    refine ⟨26949721324272086390628725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17966480882848057593752483 26949721324272086390628725)
                    ·
                      refine ⟨2526536374150508099121443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26949721324272086390628725 2526536374150508099121443)
                      ·
                        rfl

theorem cell23_4920412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_4920412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920412 prefixEnd_4920412 := by exact prefixLift 4920412
  have htrace : WordTrace (prefixWord ++ tailWord_4920412) baseStart_4920412 baseEnd_4920412 := by
    simpa [prefixWord, tailWord_4920412, baseEnd_4920412] using wordTrace_append hprefix tailTrace_4920412
  have hstable : (prefixWord ++ tailWord_4920412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920412).length < 2 ^ (prefixWord ++ tailWord_4920412).sum := by decide
  have hdescent : baseEnd_4920412 < baseStart_4920412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920415 : List Nat := [1, 1, 2, 3, 1, 1, 6, 8]
def baseStart_4920415 : Nat := 118140960795 + 4920415 * 2 ^ 59
def prefixEnd_4920415 : Nat := 4983230072969 + 3 ^ 40 * 4920415 * 2
def baseEnd_4920415 : Nat := 93575478318239688421627

theorem tailTrace_4920415 : CollatzResearch.WordTrace tailWord_4920415 prefixEnd_4920415 93575478318239688421627 := by
  unfold tailWord_4920415
  simp only [CollatzResearch.WordTrace]
  refine ⟨179462278469184269824226699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119641518979456179882817799 179462278469184269824226699)
  ·
    refine ⟨269193417703776404736340049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179462278469184269824226699 269193417703776404736340049)
    ·
      refine ⟨201895063277832303552255037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269193417703776404736340049 201895063277832303552255037)
      ·
        refine ⟨75710648729187113832095639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201895063277832303552255037 75710648729187113832095639)
        ·
          refine ⟨113565973093780670748143459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75710648729187113832095639 113565973093780670748143459)
          ·
            refine ⟨170348959640671006122215189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113565973093780670748143459 170348959640671006122215189)
            ·
              refine ⟨7985107483156453411978837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 170348959640671006122215189 7985107483156453411978837)
              ·
                refine ⟨93575478318239688421627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7985107483156453411978837 93575478318239688421627)
                ·
                  rfl

theorem cell23_4920415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 8].length) (baseStart_4920415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920415 prefixEnd_4920415 := by exact prefixLift 4920415
  have htrace : WordTrace (prefixWord ++ tailWord_4920415) baseStart_4920415 baseEnd_4920415 := by
    simpa [prefixWord, tailWord_4920415, baseEnd_4920415] using wordTrace_append hprefix tailTrace_4920415
  have hstable : (prefixWord ++ tailWord_4920415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920415).length < 2 ^ (prefixWord ++ tailWord_4920415).sum := by decide
  have hdescent : baseEnd_4920415 < baseStart_4920415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920426 : List Nat := [3, 1, 3, 2, 2, 3, 1, 2, 1, 1, 4]
def baseStart_4920426 : Nat := 118140960795 + 4920426 * 2 ^ 59
def prefixEnd_4920426 : Nat := 4983230072969 + 3 ^ 40 * 4920426 * 2
def baseEnd_4920426 : Nat := 2526543562879671044346379

theorem tailTrace_4920426 : CollatzResearch.WordTrace tailWord_4920426 prefixEnd_4920426 2526543562879671044346379 := by
  unfold tailWord_4920426
  simp only [CollatzResearch.WordTrace]
  refine ⟨44865669918036104675719283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119641786448096279135251421 44865669918036104675719283)
  ·
    refine ⟨67298504877054157013578925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44865669918036104675719283 67298504877054157013578925)
    ·
      refine ⟨25236939328895308880092097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67298504877054157013578925 25236939328895308880092097)
      ·
        refine ⟨18927704496671481660069073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25236939328895308880092097 18927704496671481660069073)
        ·
          refine ⟨14195778372503611245051805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18927704496671481660069073 14195778372503611245051805)
          ·
            refine ⟨5323416889688854216894427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14195778372503611245051805 5323416889688854216894427)
            ·
              refine ⟨7985125334533281325341641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5323416889688854216894427 7985125334533281325341641)
              ·
                refine ⟨5988844000899960994006231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7985125334533281325341641 5988844000899960994006231)
                ·
                  refine ⟨8983266001349941491009347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5988844000899960994006231 8983266001349941491009347)
                  ·
                    refine ⟨13474899002024912236514021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8983266001349941491009347 13474899002024912236514021)
                    ·
                      refine ⟨2526543562879671044346379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13474899002024912236514021 2526543562879671044346379)
                      ·
                        rfl

theorem cell23_4920426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_4920426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920426 prefixEnd_4920426 := by exact prefixLift 4920426
  have htrace : WordTrace (prefixWord ++ tailWord_4920426) baseStart_4920426 baseEnd_4920426 := by
    simpa [prefixWord, tailWord_4920426, baseEnd_4920426] using wordTrace_append hprefix tailTrace_4920426
  have hstable : (prefixWord ++ tailWord_4920426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920426).length < 2 ^ (prefixWord ++ tailWord_4920426).sum := by decide
  have hdescent : baseEnd_4920426 < baseStart_4920426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920429 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 3, 2, 3]
def baseStart_4920429 : Nat := 118140960795 + 4920429 * 2 ^ 59
def prefixEnd_4920429 : Nat := 4983230072969 + 3 ^ 40 * 4920429 * 2
def baseEnd_4920429 : Nat := 2526545103321634532608865

theorem tailTrace_4920429 : CollatzResearch.WordTrace tailWord_4920429 prefixEnd_4920429 2526545103321634532608865 := by
  unfold tailWord_4920429
  simp only [CollatzResearch.WordTrace]
  refine ⟨179462789091133550215236341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119641859394089033476824227 179462789091133550215236341)
  ·
    refine ⟨16824636477293770332678407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 179462789091133550215236341 16824636477293770332678407)
    ·
      refine ⟨25236954715940655499017611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16824636477293770332678407 25236954715940655499017611)
      ·
        refine ⟨37855432073910983248526417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25236954715940655499017611 37855432073910983248526417)
        ·
          refine ⟨28391574055433237436394813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37855432073910983248526417 28391574055433237436394813)
          ·
            refine ⟨10646840270787464038648055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28391574055433237436394813 10646840270787464038648055)
            ·
              refine ⟨15970260406181196057972083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10646840270787464038648055 15970260406181196057972083)
              ·
                refine ⟨23955390609271794086958125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15970260406181196057972083 23955390609271794086958125)
                ·
                  refine ⟨8983271478476922782609297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23955390609271794086958125 8983271478476922782609297)
                  ·
                    refine ⟨6737453608857692086956973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8983271478476922782609297 6737453608857692086956973)
                    ·
                      refine ⟨2526545103321634532608865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6737453608857692086956973 2526545103321634532608865)
                      ·
                        rfl

theorem cell23_4920429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_4920429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920429 prefixEnd_4920429 := by exact prefixLift 4920429
  have htrace : WordTrace (prefixWord ++ tailWord_4920429) baseStart_4920429 baseEnd_4920429 := by
    simpa [prefixWord, tailWord_4920429, baseEnd_4920429] using wordTrace_append hprefix tailTrace_4920429
  have hstable : (prefixWord ++ tailWord_4920429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920429).length < 2 ^ (prefixWord ++ tailWord_4920429).sum := by decide
  have hdescent : baseEnd_4920429 < baseStart_4920429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920462 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 2, 7]
def baseStart_4920462 : Nat := 118140960795 + 4920462 * 2 ^ 59
def prefixEnd_4920462 : Nat := 4983230072969 + 3 ^ 40 * 4920462 * 2
def baseEnd_4920462 : Nat := 842187349394410967832071

theorem tailTrace_4920462 : CollatzResearch.WordTrace tailWord_4920462 prefixEnd_4920462 842187349394410967832071 := by
  unfold tailWord_4920462
  simp only [CollatzResearch.WordTrace]
  refine ⟨22432999087501749606398455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119642661800009331234125093 22432999087501749606398455)
  ·
    refine ⟨33649498631252624409597683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22432999087501749606398455 33649498631252624409597683)
    ·
      refine ⟨50474247946878936614396525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33649498631252624409597683 50474247946878936614396525)
      ·
        refine ⟨18927842980079601230398697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50474247946878936614396525 18927842980079601230398697)
        ·
          refine ⟨14195882235059700922799023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18927842980079601230398697 14195882235059700922799023)
          ·
            refine ⟨21293823352589551384198535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14195882235059700922799023 21293823352589551384198535)
            ·
              refine ⟨31940735028884327076297803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21293823352589551384198535 31940735028884327076297803)
              ·
                refine ⟨47911102543326490614446705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31940735028884327076297803 47911102543326490614446705)
                ·
                  refine ⟨35933326907494867960835029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47911102543326490614446705 35933326907494867960835029)
                  ·
                    refine ⟨842187349394410967832071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35933326907494867960835029 842187349394410967832071)
                    ·
                      rfl

theorem cell23_4920462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_4920462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920462 prefixEnd_4920462 := by exact prefixLift 4920462
  have htrace : WordTrace (prefixWord ++ tailWord_4920462) baseStart_4920462 baseEnd_4920462 := by
    simpa [prefixWord, tailWord_4920462, baseEnd_4920462] using wordTrace_append hprefix tailTrace_4920462
  have hstable : (prefixWord ++ tailWord_4920462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920462).length < 2 ^ (prefixWord ++ tailWord_4920462).sum := by decide
  have hdescent : baseEnd_4920462 < baseStart_4920462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920476 : List Nat := [2, 2, 3, 2, 1, 2, 2, 3, 2, 1, 3]
def baseStart_4920476 : Nat := 118140960795 + 4920476 * 2 ^ 59
def prefixEnd_4920476 : Nat := 4983230072969 + 3 ^ 40 * 4920476 * 2
def baseEnd_4920476 : Nat := 2526569236912395848721149

theorem tailTrace_4920476 : CollatzResearch.WordTrace tailWord_4920476 prefixEnd_4920476 2526569236912395848721149 := by
  unfold tailWord_4920476
  simp only [CollatzResearch.WordTrace]
  refine ⟨89732251660981638621098641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119643002214642184828131521 89732251660981638621098641)
  ·
    refine ⟨67299188745736228965823981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89732251660981638621098641 67299188745736228965823981)
    ·
      refine ⟨25237195779651085862183993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67299188745736228965823981 25237195779651085862183993)
      ·
        refine ⟨18927896834738314396637995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25237195779651085862183993 18927896834738314396637995)
        ·
          refine ⟨28391845252107471594956993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18927896834738314396637995 28391845252107471594956993)
          ·
            refine ⟨21293883939080603696217745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28391845252107471594956993 21293883939080603696217745)
            ·
              refine ⟨15970412954310452772163309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21293883939080603696217745 15970412954310452772163309)
              ·
                refine ⟨5988904857866419789561241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15970412954310452772163309 5988904857866419789561241)
                ·
                  refine ⟨4491678643399814842170931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5988904857866419789561241 4491678643399814842170931)
                  ·
                    refine ⟨6737517965099722263256397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4491678643399814842170931 6737517965099722263256397)
                    ·
                      refine ⟨2526569236912395848721149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6737517965099722263256397 2526569236912395848721149)
                      ·
                        rfl

theorem cell23_4920476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_4920476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920476 prefixEnd_4920476 := by exact prefixLift 4920476
  have htrace : WordTrace (prefixWord ++ tailWord_4920476) baseStart_4920476 baseEnd_4920476 := by
    simpa [prefixWord, tailWord_4920476, baseEnd_4920476] using wordTrace_append hprefix tailTrace_4920476
  have hstable : (prefixWord ++ tailWord_4920476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920476).length < 2 ^ (prefixWord ++ tailWord_4920476).sum := by decide
  have hdescent : baseEnd_4920476 < baseStart_4920476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920499 : List Nat := [1, 1, 1, 2, 3, 2, 4, 2, 1, 4, 2]
def baseStart_4920499 : Nat := 118140960795 + 4920499 * 2 ^ 59
def prefixEnd_4920499 : Nat := 4983230072969 + 3 ^ 40 * 4920499 * 2
def baseEnd_4920499 : Nat := 2526581046967449258733543

theorem tailTrace_4920499 : CollatzResearch.WordTrace tailWord_4920499 prefixEnd_4920499 2526581046967449258733543 := by
  unfold tailWord_4920499
  simp only [CollatzResearch.WordTrace]
  refine ⟨179465342200879952170284551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119643561467253301446856367 179465342200879952170284551)
  ·
    refine ⟨269198013301319928255426827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179465342200879952170284551 269198013301319928255426827)
    ·
      refine ⟨403797019951979892383140241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269198013301319928255426827 403797019951979892383140241)
      ·
        refine ⟨302847764963984919287355181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 403797019951979892383140241 302847764963984919287355181)
        ·
          refine ⟨113567911861494344732758193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 302847764963984919287355181 113567911861494344732758193)
          ·
            refine ⟨85175933896120758549568645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113567911861494344732758193 85175933896120758549568645)
            ·
              refine ⟨15970487605522642228044121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85175933896120758549568645 15970487605522642228044121)
              ·
                refine ⟨11977865704141981671033091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15970487605522642228044121 11977865704141981671033091)
                ·
                  refine ⟨17966798556212972506549637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11977865704141981671033091 17966798556212972506549637)
                  ·
                    refine ⟨3368774729289932344978057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17966798556212972506549637 3368774729289932344978057)
                    ·
                      refine ⟨2526581046967449258733543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3368774729289932344978057 2526581046967449258733543)
                      ·
                        rfl

theorem cell23_4920499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 4, 2].length) (baseStart_4920499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920499 prefixEnd_4920499 := by exact prefixLift 4920499
  have htrace : WordTrace (prefixWord ++ tailWord_4920499) baseStart_4920499 baseEnd_4920499 := by
    simpa [prefixWord, tailWord_4920499, baseEnd_4920499] using wordTrace_append hprefix tailTrace_4920499
  have hstable : (prefixWord ++ tailWord_4920499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920499).length < 2 ^ (prefixWord ++ tailWord_4920499).sum := by decide
  have hdescent : baseEnd_4920499 < baseStart_4920499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920515 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 9]
def baseStart_4920515 : Nat := 118140960795 + 4920515 * 2 ^ 59
def prefixEnd_4920515 : Nat := 4983230072969 + 3 ^ 40 * 4920515 * 2
def baseEnd_4920515 : Nat := 2526589262657921196133469

theorem tailTrace_4920515 : CollatzResearch.WordTrace tailWord_4920515 prefixEnd_4920515 2526589262657921196133469 := by
  unfold tailWord_4920515
  simp only [CollatzResearch.WordTrace]
  refine ⟨179465925768821986902866999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119643950512547991268577999 179465925768821986902866999)
  ·
    refine ⟨269198888653232980354300499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179465925768821986902866999 269198888653232980354300499)
    ·
      refine ⟨403798332979849470531450749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269198888653232980354300499 403798332979849470531450749)
      ·
        refine ⟨151424374867443551449294031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 403798332979849470531450749 151424374867443551449294031)
        ·
          refine ⟨227136562301165327173941047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151424374867443551449294031 227136562301165327173941047)
          ·
            refine ⟨340704843451747990760911571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227136562301165327173941047 340704843451747990760911571)
            ·
              refine ⟨511057265177621986141367357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340704843451747990760911571 511057265177621986141367357)
              ·
                refine ⟨191646474441608244803012759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 511057265177621986141367357 191646474441608244803012759)
                ·
                  refine ⟨287469711662412367204519139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191646474441608244803012759 287469711662412367204519139)
                  ·
                    refine ⟨431204567493618550806778709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 287469711662412367204519139 431204567493618550806778709)
                    ·
                      refine ⟨2526589262657921196133469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 431204567493618550806778709 2526589262657921196133469)
                      ·
                        rfl

theorem cell23_4920515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_4920515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920515 prefixEnd_4920515 := by exact prefixLift 4920515
  have htrace : WordTrace (prefixWord ++ tailWord_4920515) baseStart_4920515 baseEnd_4920515 := by
    simpa [prefixWord, tailWord_4920515, baseEnd_4920515] using wordTrace_append hprefix tailTrace_4920515
  have hstable : (prefixWord ++ tailWord_4920515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920515).length < 2 ^ (prefixWord ++ tailWord_4920515).sum := by decide
  have hdescent : baseEnd_4920515 < baseStart_4920515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920522 : List Nat := [3, 1, 2, 1, 3, 2, 1, 3, 7]
def baseStart_4920522 : Nat := 118140960795 + 4920522 * 2 ^ 59
def prefixEnd_4920522 : Nat := 4983230072969 + 3 ^ 40 * 4920522 * 2
def baseEnd_4920522 : Nat := 280732539669166963193993

theorem tailTrace_4920522 : CollatzResearch.WordTrace tailWord_4920522 prefixEnd_4920522 280732539669166963193993 := by
  unfold tailWord_4920522
  simp only [CollatzResearch.WordTrace]
  refine ⟨44866545269949156774592955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119644120719864418065581213 44866545269949156774592955)
  ·
    refine ⟨67299817904923735161889433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44866545269949156774592955 67299817904923735161889433)
    ·
      refine ⟨50474863428692801371417075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67299817904923735161889433 50474863428692801371417075)
      ·
        refine ⟨75712295143039202057125613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50474863428692801371417075 75712295143039202057125613)
        ·
          refine ⟨28392110678639700771422105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75712295143039202057125613 28392110678639700771422105)
          ·
            refine ⟨21294083008979775578566579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28392110678639700771422105 21294083008979775578566579)
            ·
              refine ⟨31941124513469663367849869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21294083008979775578566579 31941124513469663367849869)
              ·
                refine ⟨11977921692551123762943701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31941124513469663367849869 11977921692551123762943701)
                ·
                  refine ⟨280732539669166963193993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11977921692551123762943701 280732539669166963193993)
                  ·
                    rfl

theorem cell23_4920522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 7].length) (baseStart_4920522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920522 prefixEnd_4920522 := by exact prefixLift 4920522
  have htrace : WordTrace (prefixWord ++ tailWord_4920522) baseStart_4920522 baseEnd_4920522 := by
    simpa [prefixWord, tailWord_4920522, baseEnd_4920522] using wordTrace_append hprefix tailTrace_4920522
  have hstable : (prefixWord ++ tailWord_4920522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920522).length < 2 ^ (prefixWord ++ tailWord_4920522).sum := by decide
  have hdescent : baseEnd_4920522 < baseStart_4920522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920533 : List Nat := [1, 3, 2, 4, 1, 3, 1, 1, 1, 4, 2]
def baseStart_4920533 : Nat := 118140960795 + 4920533 * 2 ^ 59
def prefixEnd_4920533 : Nat := 4983230072969 + 3 ^ 40 * 4920533 * 2
def baseEnd_4920533 : Nat := 2526598505309702125708387

theorem tailTrace_4920533 : CollatzResearch.WordTrace tailWord_4920533 prefixEnd_4920533 2526598505309702125708387 := by
  unfold tailWord_4920533
  simp only [CollatzResearch.WordTrace]
  refine ⟨179466582282756775977022253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119644388188504517318014835 179466582282756775977022253)
  ·
    refine ⟨67299968356033790991383345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179466582282756775977022253 67299968356033790991383345)
    ·
      refine ⟨50474976267025343243537509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67299968356033790991383345 50474976267025343243537509)
      ·
        refine ⟨9464058050067251858163283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50474976267025343243537509 9464058050067251858163283)
        ·
          refine ⟨14196087075100877787244925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9464058050067251858163283 14196087075100877787244925)
          ·
            refine ⟨5323532653162829170216847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14196087075100877787244925 5323532653162829170216847)
            ·
              refine ⟨7985298979744243755325271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5323532653162829170216847 7985298979744243755325271)
              ·
                refine ⟨11977948469616365632987907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7985298979744243755325271 11977948469616365632987907)
                ·
                  refine ⟨17966922704424548449481861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11977948469616365632987907 17966922704424548449481861)
                  ·
                    refine ⟨3368798007079602834277849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17966922704424548449481861 3368798007079602834277849)
                    ·
                      refine ⟨2526598505309702125708387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3368798007079602834277849 2526598505309702125708387)
                      ·
                        rfl

theorem cell23_4920533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_4920533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920533 prefixEnd_4920533 := by exact prefixLift 4920533
  have htrace : WordTrace (prefixWord ++ tailWord_4920533) baseStart_4920533 baseEnd_4920533 := by
    simpa [prefixWord, tailWord_4920533, baseEnd_4920533] using wordTrace_append hprefix tailTrace_4920533
  have hstable : (prefixWord ++ tailWord_4920533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920533).length < 2 ^ (prefixWord ++ tailWord_4920533).sum := by decide
  have hdescent : baseEnd_4920533 < baseStart_4920533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920552 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 1, 7]
def baseStart_4920552 : Nat := 118140960795 + 4920552 * 2 ^ 59
def prefixEnd_4920552 : Nat := 4983230072969 + 3 ^ 40 * 4920552 * 2
def baseEnd_4920552 : Nat := 842202753814045850456933

theorem tailTrace_4920552 : CollatzResearch.WordTrace tailWord_4920552 prefixEnd_4920552 842202753814045850456933 := by
  unfold tailWord_4920552
  simp only [CollatzResearch.WordTrace]
  refine ⟨89733637634843971110981955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119644850179791961481309273 89733637634843971110981955)
  ·
    refine ⟨134600456452265956666472933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89733637634843971110981955 134600456452265956666472933)
    ·
      refine ⟨25237585584799866874963675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134600456452265956666472933 25237585584799866874963675)
      ·
        refine ⟨37856378377199800312445513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25237585584799866874963675 37856378377199800312445513)
        ·
          refine ⟨28392283782899850234334135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37856378377199800312445513 28392283782899850234334135)
          ·
            refine ⟨42588425674349775351501203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28392283782899850234334135 42588425674349775351501203)
            ·
              refine ⟨63882638511524663027251805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42588425674349775351501203 63882638511524663027251805)
              ·
                refine ⟨23955989441821748635219427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63882638511524663027251805 23955989441821748635219427)
                ·
                  refine ⟨35933984162732622952829141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23955989441821748635219427 35933984162732622952829141)
                  ·
                    refine ⟨842202753814045850456933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35933984162732622952829141 842202753814045850456933)
                    ·
                      rfl

theorem cell23_4920552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_4920552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920552 prefixEnd_4920552 := by exact prefixLift 4920552
  have htrace : WordTrace (prefixWord ++ tailWord_4920552) baseStart_4920552 baseEnd_4920552 := by
    simpa [prefixWord, tailWord_4920552, baseEnd_4920552] using wordTrace_append hprefix tailTrace_4920552
  have hstable : (prefixWord ++ tailWord_4920552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920552).length < 2 ^ (prefixWord ++ tailWord_4920552).sum := by decide
  have hdescent : baseEnd_4920552 < baseStart_4920552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920556 : List Nat := [2, 2, 1, 1, 2, 6, 1, 3, 5]
def baseStart_4920556 : Nat := 118140960795 + 4920556 * 2 ^ 59
def prefixEnd_4920556 : Nat := 4983230072969 + 3 ^ 40 * 4920556 * 2
def baseEnd_4920556 : Nat := 280734479484972837302309

theorem tailTrace_4920556 : CollatzResearch.WordTrace tailWord_4920556 prefixEnd_4920556 280734479484972837302309 := by
  unfold tailWord_4920556
  simp only [CollatzResearch.WordTrace]
  refine ⟨89733710580836725452554761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119644947441115633936739681 89733710580836725452554761)
  ·
    refine ⟨67300282935627544089416071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89733710580836725452554761 67300282935627544089416071)
    ·
      refine ⟨100950424403441316134124107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67300282935627544089416071 100950424403441316134124107)
      ·
        refine ⟨151425636605161974201186161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100950424403441316134124107 151425636605161974201186161)
        ·
          refine ⟨113569227453871480650889621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151425636605161974201186161 113569227453871480650889621)
          ·
            refine ⟨5323557536900225655510451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 113569227453871480650889621 5323557536900225655510451)
            ·
              refine ⟨7985336305350338483265677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5323557536900225655510451 7985336305350338483265677)
              ·
                refine ⟨2994501114506376931224629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7985336305350338483265677 2994501114506376931224629)
                ·
                  refine ⟨280734479484972837302309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2994501114506376931224629 280734479484972837302309)
                  ·
                    rfl

theorem cell23_4920556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 5].length) (baseStart_4920556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920556 prefixEnd_4920556 := by exact prefixLift 4920556
  have htrace : WordTrace (prefixWord ++ tailWord_4920556) baseStart_4920556 baseEnd_4920556 := by
    simpa [prefixWord, tailWord_4920556, baseEnd_4920556] using wordTrace_append hprefix tailTrace_4920556
  have hstable : (prefixWord ++ tailWord_4920556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920556).length < 2 ^ (prefixWord ++ tailWord_4920556).sum := by decide
  have hdescent : baseEnd_4920556 < baseStart_4920556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920599 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 5, 4]
def baseStart_4920599 : Nat := 118140960795 + 4920599 * 2 ^ 59
def prefixEnd_4920599 : Nat := 4983230072969 + 3 ^ 40 * 4920599 * 2
def baseEnd_4920599 : Nat := 842210798344299622494361

theorem tailTrace_4920599 : CollatzResearch.WordTrace tailWord_4920599 prefixEnd_4920599 842210798344299622494361 := by
  unfold tailWord_4920599
  simp only [CollatzResearch.WordTrace]
  refine ⟨179468989500517669248924851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119645993000345112832616567 179468989500517669248924851)
  ·
    refine ⟨269203484250776503873387277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179468989500517669248924851 269203484250776503873387277)
    ·
      refine ⟨100951306594041188952520229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269203484250776503873387277 100951306594041188952520229)
      ·
        refine ⟨18928369986382722928597543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100951306594041188952520229 18928369986382722928597543)
        ·
          refine ⟨28392554979574084392896315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18928369986382722928597543 28392554979574084392896315)
          ·
            refine ⟨42588832469361126589344473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28392554979574084392896315 42588832469361126589344473)
            ·
              refine ⟨31941624352020844942008355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42588832469361126589344473 31941624352020844942008355)
              ·
                refine ⟨47912436528031267413012533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31941624352020844942008355 47912436528031267413012533)
                ·
                  refine ⟨4491790924502931319969925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47912436528031267413012533 4491790924502931319969925)
                  ·
                    refine ⟨842210798344299622494361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4491790924502931319969925 842210798344299622494361)
                    ·
                      rfl

theorem cell23_4920599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 4].length) (baseStart_4920599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920599 prefixEnd_4920599 := by exact prefixLift 4920599
  have htrace : WordTrace (prefixWord ++ tailWord_4920599) baseStart_4920599 baseEnd_4920599 := by
    simpa [prefixWord, tailWord_4920599, baseEnd_4920599] using wordTrace_append hprefix tailTrace_4920599
  have hstable : (prefixWord ++ tailWord_4920599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920599).length < 2 ^ (prefixWord ++ tailWord_4920599).sum := by decide
  have hdescent : baseEnd_4920599 < baseStart_4920599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920626 : List Nat := [3, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3]
def baseStart_4920626 : Nat := 118140960795 + 4920626 * 2 ^ 59
def prefixEnd_4920626 : Nat := 4983230072969 + 3 ^ 40 * 4920626 * 2
def baseEnd_4920626 : Nat := 2526646259010570261845459

theorem tailTrace_4920626 : CollatzResearch.WordTrace tailWord_4920626 prefixEnd_4920626 2526646259010570261845459 := by
  unfold tailWord_4920626
  simp only [CollatzResearch.WordTrace]
  refine ⟨44867493567854963215039433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119646649514279901906771821 44867493567854963215039433)
  ·
    refine ⟨33650620175891222411279575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44867493567854963215039433 33650620175891222411279575)
    ·
      refine ⟨50475930263836833616919363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33650620175891222411279575 50475930263836833616919363)
      ·
        refine ⟨75713895395755250425379045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50475930263836833616919363 75713895395755250425379045)
        ·
          refine ⟨14196355386704109454758571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75713895395755250425379045 14196355386704109454758571)
          ·
            refine ⟨21294533080056164182137857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14196355386704109454758571 21294533080056164182137857)
            ·
              refine ⟨15970899810042123136603393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21294533080056164182137857 15970899810042123136603393)
              ·
                refine ⟨11978174857531592352452545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15970899810042123136603393 11978174857531592352452545)
                ·
                  refine ⟨8983631143148694264339409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11978174857531592352452545 8983631143148694264339409)
                  ·
                    refine ⟨6737723357361520698254557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8983631143148694264339409 6737723357361520698254557)
                    ·
                      refine ⟨2526646259010570261845459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6737723357361520698254557 2526646259010570261845459)
                      ·
                        rfl

theorem cell23_4920626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_4920626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920626 prefixEnd_4920626 := by exact prefixLift 4920626
  have htrace : WordTrace (prefixWord ++ tailWord_4920626) baseStart_4920626 baseEnd_4920626 := by
    simpa [prefixWord, tailWord_4920626, baseEnd_4920626] using wordTrace_append hprefix tailTrace_4920626
  have hstable : (prefixWord ++ tailWord_4920626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920626).length < 2 ^ (prefixWord ++ tailWord_4920626).sum := by decide
  have hdescent : baseEnd_4920626 < baseStart_4920626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920629 : List Nat := [1, 3, 3, 1, 2, 2, 1, 4, 6]
def baseStart_4920629 : Nat := 118140960795 + 4920629 * 2 ^ 59
def prefixEnd_4920629 : Nat := 4983230072969 + 3 ^ 40 * 4920629 * 2
def baseEnd_4920629 : Nat := 280738644383614861123105

theorem tailTrace_4920629 : CollatzResearch.WordTrace tailWord_4920629 prefixEnd_4920629 280738644383614861123105 := by
  unfold tailWord_4920629
  simp only [CollatzResearch.WordTrace]
  refine ⟨179470083690408984372516941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119646722460272656248344627 179470083690408984372516941)
  ·
    refine ⟨67301281383903369139693853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179470083690408984372516941 67301281383903369139693853)
    ·
      refine ⟨25237980518963763427385195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67301281383903369139693853 25237980518963763427385195)
      ·
        refine ⟨37856970778445645141077793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25237980518963763427385195 37856970778445645141077793)
        ·
          refine ⟨28392728083834233855808345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37856970778445645141077793 28392728083834233855808345)
          ·
            refine ⟨21294546062875675391856259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28392728083834233855808345 21294546062875675391856259)
            ·
              refine ⟨31941819094313513087784389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21294546062875675391856259 31941819094313513087784389)
              ·
                refine ⟨5989091080183783703959573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31941819094313513087784389 5989091080183783703959573)
                ·
                  refine ⟨280738644383614861123105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5989091080183783703959573 280738644383614861123105)
                  ·
                    rfl

theorem cell23_4920629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 6].length) (baseStart_4920629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920629 prefixEnd_4920629 := by exact prefixLift 4920629
  have htrace : WordTrace (prefixWord ++ tailWord_4920629) baseStart_4920629 baseEnd_4920629 := by
    simpa [prefixWord, tailWord_4920629, baseEnd_4920629] using wordTrace_append hprefix tailTrace_4920629
  have hstable : (prefixWord ++ tailWord_4920629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920629).length < 2 ^ (prefixWord ++ tailWord_4920629).sum := by decide
  have hdescent : baseEnd_4920629 < baseStart_4920629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920632 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 1, 2, 6]
def baseStart_4920632 : Nat := 118140960795 + 4920632 * 2 ^ 59
def prefixEnd_4920632 : Nat := 4983230072969 + 3 ^ 40 * 4920632 * 2
def baseEnd_4920632 : Nat := 2526649339894497238370431

theorem tailTrace_4920632 : CollatzResearch.WordTrace tailWord_4920632 prefixEnd_4920632 2526649339894497238370431 := by
  unfold tailWord_4920632
  simp only [CollatzResearch.WordTrace]
  refine ⟨89735096554699057942438075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119646795406265410589917433 89735096554699057942438075)
  ·
    refine ⟨134602644832048586913657113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89735096554699057942438075 134602644832048586913657113)
    ·
      refine ⟨100951983624036440185242835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134602644832048586913657113 100951983624036440185242835)
      ·
        refine ⟨151427975436054660277864253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100951983624036440185242835 151427975436054660277864253)
        ·
          refine ⟨56785490788520497604199095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151427975436054660277864253 56785490788520497604199095)
          ·
            refine ⟨85178236182780746406298643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56785490788520497604199095 85178236182780746406298643)
            ·
              refine ⟨127767354274171119609447965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85178236182780746406298643 127767354274171119609447965)
              ·
                refine ⟨47912757852814169853542987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127767354274171119609447965 47912757852814169853542987)
                ·
                  refine ⟨71869136779221254780314481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47912757852814169853542987 71869136779221254780314481)
                  ·
                    refine ⟨53901852584415941085235861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71869136779221254780314481 53901852584415941085235861)
                    ·
                      refine ⟨2526649339894497238370431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53901852584415941085235861 2526649339894497238370431)
                      ·
                        rfl

theorem cell23_4920632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_4920632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920632 prefixEnd_4920632 := by exact prefixLift 4920632
  have htrace : WordTrace (prefixWord ++ tailWord_4920632) baseStart_4920632 baseEnd_4920632 := by
    simpa [prefixWord, tailWord_4920632, baseEnd_4920632] using wordTrace_append hprefix tailTrace_4920632
  have hstable : (prefixWord ++ tailWord_4920632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920632).length < 2 ^ (prefixWord ++ tailWord_4920632).sum := by decide
  have hdescent : baseEnd_4920632 < baseStart_4920632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920656 : List Nat := [2, 1, 1, 1, 1, 5, 3, 2, 3, 1, 3]
def baseStart_4920656 : Nat := 118140960795 + 4920656 * 2 ^ 59
def prefixEnd_4920656 : Nat := 4983230072969 + 3 ^ 40 * 4920656 * 2
def baseEnd_4920656 : Nat := 2526661663430205144470321

theorem tailTrace_4920656 : CollatzResearch.WordTrace tailWord_4920656 prefixEnd_4920656 2526661663430205144470321 := by
  unfold tailWord_4920656
  simp only [CollatzResearch.WordTrace]
  refine ⟨89735534230655583991874911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119647378974207445322499881 89735534230655583991874911)
  ·
    refine ⟨134603301345983375987812367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89735534230655583991874911 134603301345983375987812367)
    ·
      refine ⟨201904952018975063981718551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134603301345983375987812367 201904952018975063981718551)
      ·
        refine ⟨302857428028462595972577827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201904952018975063981718551 302857428028462595972577827)
        ·
          refine ⟨454286142042693893958866741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302857428028462595972577827 454286142042693893958866741)
          ·
            refine ⟨42589325816502552558643757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 454286142042693893958866741 42589325816502552558643757)
            ·
              refine ⟨15970997181188457209491409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42589325816502552558643757 15970997181188457209491409)
              ·
                refine ⟨11978247885891342907118557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15970997181188457209491409 11978247885891342907118557)
                ·
                  refine ⟨4491842957209253590169459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11978247885891342907118557 4491842957209253590169459)
                  ·
                    refine ⟨6737764435813880385254189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4491842957209253590169459 6737764435813880385254189)
                    ·
                      refine ⟨2526661663430205144470321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6737764435813880385254189 2526661663430205144470321)
                      ·
                        rfl

theorem cell23_4920656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 3, 1, 3].length) (baseStart_4920656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920656 prefixEnd_4920656 := by exact prefixLift 4920656
  have htrace : WordTrace (prefixWord ++ tailWord_4920656) baseStart_4920656 baseEnd_4920656 := by
    simpa [prefixWord, tailWord_4920656, baseEnd_4920656] using wordTrace_append hprefix tailTrace_4920656
  have hstable : (prefixWord ++ tailWord_4920656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920656).length < 2 ^ (prefixWord ++ tailWord_4920656).sum := by decide
  have hdescent : baseEnd_4920656 < baseStart_4920656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920659 : List Nat := [1, 1, 1, 2, 1, 1, 6, 4, 1, 5]
def baseStart_4920659 : Nat := 118140960795 + 4920659 * 2 ^ 59
def prefixEnd_4920659 : Nat := 4983230072969 + 3 ^ 40 * 4920659 * 2
def baseEnd_4920659 : Nat := 842221067957389544244269

theorem tailTrace_4920659 : CollatzResearch.WordTrace tailWord_4920659 prefixEnd_4920659 842221067957389544244269 := by
  unfold tailWord_4920659
  simp only [CollatzResearch.WordTrace]
  refine ⟨179471177880300299496109031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119647451920200199664072687 179471177880300299496109031)
  ·
    refine ⟨269206766820450449244163547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179471177880300299496109031 269206766820450449244163547)
    ·
      refine ⟨403810150230675673866245321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269206766820450449244163547 403810150230675673866245321)
      ·
        refine ⟨302857612673006755399683991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 403810150230675673866245321 302857612673006755399683991)
        ·
          refine ⟨454286419009510133099525987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302857612673006755399683991 454286419009510133099525987)
          ·
            refine ⟨681429628514265199649288981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454286419009510133099525987 681429628514265199649288981)
            ·
              refine ⟨31942013836606181233560421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 681429628514265199649288981 31942013836606181233560421)
              ·
                refine ⟨5989127594363658981292579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31942013836606181233560421 5989127594363658981292579)
                ·
                  refine ⟨8983691391545488471938869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5989127594363658981292579 8983691391545488471938869)
                  ·
                    refine ⟨842221067957389544244269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8983691391545488471938869 842221067957389544244269)
                    ·
                      rfl

theorem cell23_4920659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 5].length) (baseStart_4920659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920659 prefixEnd_4920659 := by exact prefixLift 4920659
  have htrace : WordTrace (prefixWord ++ tailWord_4920659) baseStart_4920659 baseEnd_4920659 := by
    simpa [prefixWord, tailWord_4920659, baseEnd_4920659] using wordTrace_append hprefix tailTrace_4920659
  have hstable : (prefixWord ++ tailWord_4920659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920659).length < 2 ^ (prefixWord ++ tailWord_4920659).sum := by decide
  have hdescent : baseEnd_4920659 < baseStart_4920659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920676 : List Nat := [2, 3, 1, 1, 3, 3, 1, 3, 1, 5]
def baseStart_4920676 : Nat := 118140960795 + 4920676 * 2 ^ 59
def prefixEnd_4920676 : Nat := 4983230072969 + 3 ^ 40 * 4920676 * 2
def baseEnd_4920676 : Nat := 842223977681098355406743

theorem tailTrace_4920676 : CollatzResearch.WordTrace tailWord_4920676 prefixEnd_4920676 842223977681098355406743 := by
  unfold tailWord_4920676
  simp only [CollatzResearch.WordTrace]
  refine ⟨89735898960619355699738941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119647865280825807599651921 89735898960619355699738941)
  ·
    refine ⟨33650962110232258387402103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89735898960619355699738941 33650962110232258387402103)
    ·
      refine ⟨50476443165348387581103155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33650962110232258387402103 50476443165348387581103155)
      ·
        refine ⟨75714664748022581371654733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50476443165348387581103155 75714664748022581371654733)
        ·
          refine ⟨28392999280508468014370525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75714664748022581371654733 28392999280508468014370525)
          ·
            refine ⟨10647374730190675505388947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28392999280508468014370525 10647374730190675505388947)
            ·
              refine ⟨15971062095286013258083421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10647374730190675505388947 15971062095286013258083421)
              ·
                refine ⟨5989148285732254971781283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15971062095286013258083421 5989148285732254971781283)
                ·
                  refine ⟨8983722428598382457671925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5989148285732254971781283 8983722428598382457671925)
                  ·
                    refine ⟨842223977681098355406743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8983722428598382457671925 842223977681098355406743)
                    ·
                      rfl

theorem cell23_4920676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_4920676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920676 prefixEnd_4920676 := by exact prefixLift 4920676
  have htrace : WordTrace (prefixWord ++ tailWord_4920676) baseStart_4920676 baseEnd_4920676 := by
    simpa [prefixWord, tailWord_4920676, baseEnd_4920676] using wordTrace_append hprefix tailTrace_4920676
  have hstable : (prefixWord ++ tailWord_4920676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920676).length < 2 ^ (prefixWord ++ tailWord_4920676).sum := by decide
  have hdescent : baseEnd_4920676 < baseStart_4920676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920699 : List Nat := [1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 5]
def baseStart_4920699 : Nat := 118140960795 + 4920699 * 2 ^ 59
def prefixEnd_4920699 : Nat := 4983230072969 + 3 ^ 40 * 4920699 * 2
def baseEnd_4920699 : Nat := 2526683743098348476232623

theorem tailTrace_4920699 : CollatzResearch.WordTrace tailWord_4920699 prefixEnd_4920699 2526683743098348476232623 := by
  unfold tailWord_4920699
  simp only [CollatzResearch.WordTrace]
  refine ⟨179472636800155386327565151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119648424533436924218376767 179472636800155386327565151)
  ·
    refine ⟨269208955200233079491347727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179472636800155386327565151 269208955200233079491347727)
    ·
      refine ⟨403813432800349619237021591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269208955200233079491347727 403813432800349619237021591)
      ·
        refine ⟨605720149200524428855532387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403813432800349619237021591 605720149200524428855532387)
        ·
          refine ⟨908580223800786643283298581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605720149200524428855532387 908580223800786643283298581)
          ·
            refine ⟨42589697990661873903904621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 908580223800786643283298581 42589697990661873903904621)
            ·
              refine ⟨15971136746498202713964233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42589697990661873903904621 15971136746498202713964233)
              ·
                refine ⟨11978352559873652035473175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15971136746498202713964233 11978352559873652035473175)
                ·
                  refine ⟨17967528839810478053209763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11978352559873652035473175 17967528839810478053209763)
                  ·
                    refine ⟨26951293259715717079814645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17967528839810478053209763 26951293259715717079814645)
                    ·
                      refine ⟨2526683743098348476232623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26951293259715717079814645 2526683743098348476232623)
                      ·
                        rfl

theorem cell23_4920699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 5].length) (baseStart_4920699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920699 prefixEnd_4920699 := by exact prefixLift 4920699
  have htrace : WordTrace (prefixWord ++ tailWord_4920699) baseStart_4920699 baseEnd_4920699 := by
    simpa [prefixWord, tailWord_4920699, baseEnd_4920699] using wordTrace_append hprefix tailTrace_4920699
  have hstable : (prefixWord ++ tailWord_4920699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920699).length < 2 ^ (prefixWord ++ tailWord_4920699).sum := by decide
  have hdescent : baseEnd_4920699 < baseStart_4920699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920713 : List Nat := [1, 2, 1, 1, 7, 1, 2, 2, 1, 1, 4]
def baseStart_4920713 : Nat := 118140960795 + 4920713 * 2 ^ 59
def prefixEnd_4920713 : Nat := 4983230072969 + 3 ^ 40 * 4920713 * 2
def baseEnd_4920713 : Nat := 2526690931827511421457559

theorem tailTrace_4920713 : CollatzResearch.WordTrace tailWord_4920713 prefixEnd_4920713 2526690931827511421457559 := by
  unfold tailWord_4920713
  simp only [CollatzResearch.WordTrace]
  refine ⟨179473147422104666718574793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119648764948069777812383195 179473147422104666718574793)
  ·
    refine ⟨134604860566578500038931095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179473147422104666718574793 134604860566578500038931095)
    ·
      refine ⟨201907290849867750058396643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134604860566578500038931095 201907290849867750058396643)
      ·
        refine ⟨302860936274801625087594965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201907290849867750058396643 302860936274801625087594965)
        ·
          refine ⟨7098303193940663087990507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 302860936274801625087594965 7098303193940663087990507)
          ·
            refine ⟨10647454790910994631985761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7098303193940663087990507 10647454790910994631985761)
            ·
              refine ⟨7985591093183245973989321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10647454790910994631985761 7985591093183245973989321)
              ·
                refine ⟨5989193319887434480491991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7985591093183245973989321 5989193319887434480491991)
                ·
                  refine ⟨8983789979831151720737987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5989193319887434480491991 8983789979831151720737987)
                  ·
                    refine ⟨13475684969746727581106981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8983789979831151720737987 13475684969746727581106981)
                    ·
                      refine ⟨2526690931827511421457559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13475684969746727581106981 2526690931827511421457559)
                      ·
                        rfl

theorem cell23_4920713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 1, 4].length) (baseStart_4920713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920713 prefixEnd_4920713 := by exact prefixLift 4920713
  have htrace : WordTrace (prefixWord ++ tailWord_4920713) baseStart_4920713 baseEnd_4920713 := by
    simpa [prefixWord, tailWord_4920713, baseEnd_4920713] using wordTrace_append hprefix tailTrace_4920713
  have hstable : (prefixWord ++ tailWord_4920713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920713).length < 2 ^ (prefixWord ++ tailWord_4920713).sum := by decide
  have hdescent : baseEnd_4920713 < baseStart_4920713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920733 : List Nat := [1, 4, 2, 1, 3, 1, 2, 3, 1, 2, 3]
def baseStart_4920733 : Nat := 118140960795 + 4920733 * 2 ^ 59
def prefixEnd_4920733 : Nat := 4983230072969 + 3 ^ 40 * 4920733 * 2
def baseEnd_4920733 : Nat := 2526701201440601343207467

theorem tailTrace_4920733 : CollatzResearch.WordTrace tailWord_4920733 prefixEnd_4920733 2526701201440601343207467 := by
  unfold tailWord_4920733
  simp only [CollatzResearch.WordTrace]
  refine ⟨179473876882032210134302853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119649251254688140089535235 179473876882032210134302853)
  ·
    refine ⟨33651351915381039400181785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179473876882032210134302853 33651351915381039400181785)
    ·
      refine ⟨25238513936535779550136339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33651351915381039400181785 25238513936535779550136339)
      ·
        refine ⟨37857770904803669325204509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25238513936535779550136339 37857770904803669325204509)
        ·
          refine ⟨14196664089301375996951691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37857770904803669325204509 14196664089301375996951691)
          ·
            refine ⟨21294996133952063995427537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14196664089301375996951691 21294996133952063995427537)
            ·
              refine ⟨15971247100464047996570653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21294996133952063995427537 15971247100464047996570653)
              ·
                refine ⟨5989217662674017998713995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15971247100464047996570653 5989217662674017998713995)
                ·
                  refine ⟨8983826494011026998070993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5989217662674017998713995 8983826494011026998070993)
                  ·
                    refine ⟨6737869870508270248553245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8983826494011026998070993 6737869870508270248553245)
                    ·
                      refine ⟨2526701201440601343207467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6737869870508270248553245 2526701201440601343207467)
                      ·
                        rfl

theorem cell23_4920733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_4920733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920733 prefixEnd_4920733 := by exact prefixLift 4920733
  have htrace : WordTrace (prefixWord ++ tailWord_4920733) baseStart_4920733 baseEnd_4920733 := by
    simpa [prefixWord, tailWord_4920733, baseEnd_4920733] using wordTrace_append hprefix tailTrace_4920733
  have hstable : (prefixWord ++ tailWord_4920733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920733).length < 2 ^ (prefixWord ++ tailWord_4920733).sum := by decide
  have hdescent : baseEnd_4920733 < baseStart_4920733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920813 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 2, 6]
def baseStart_4920813 : Nat := 118140960795 + 4920813 * 2 ^ 59
def prefixEnd_4920813 : Nat := 4983230072969 + 3 ^ 40 * 4920813 * 2
def baseEnd_4920813 : Nat := 842247426630987010069033

theorem tailTrace_4920813 : CollatzResearch.WordTrace tailWord_4920813 prefixEnd_4920813 842247426630987010069033 := by
  unfold tailWord_4920813
  simp only [CollatzResearch.WordTrace]
  refine ⟨179476794721742383797215093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119651196481161589198143395 179476794721742383797215093)
  ·
    refine ⟨16825949505163348480988915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 179476794721742383797215093 16825949505163348480988915)
    ·
      refine ⟨25238924257745022721483373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16825949505163348480988915 25238924257745022721483373)
      ·
        refine ⟨9464596596654383520556265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25238924257745022721483373 9464596596654383520556265)
        ·
          refine ⟨7098447447490787640417199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9464596596654383520556265 7098447447490787640417199)
          ·
            refine ⟨10647671171236181460625799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7098447447490787640417199 10647671171236181460625799)
            ·
              refine ⟨15971506756854272190938699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10647671171236181460625799 15971506756854272190938699)
              ·
                refine ⟨23957260135281408286408049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15971506756854272190938699 23957260135281408286408049)
                ·
                  refine ⟨17967945101461056214806037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23957260135281408286408049 17967945101461056214806037)
                  ·
                    refine ⟨842247426630987010069033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17967945101461056214806037 842247426630987010069033)
                    ·
                      rfl

theorem cell23_4920813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_4920813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920813 prefixEnd_4920813 := by exact prefixLift 4920813
  have htrace : WordTrace (prefixWord ++ tailWord_4920813) baseStart_4920813 baseEnd_4920813 := by
    simpa [prefixWord, tailWord_4920813, baseEnd_4920813] using wordTrace_append hprefix tailTrace_4920813
  have hstable : (prefixWord ++ tailWord_4920813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920813).length < 2 ^ (prefixWord ++ tailWord_4920813).sum := by decide
  have hdescent : baseEnd_4920813 < baseStart_4920813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920816 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 4]
def baseStart_4920816 : Nat := 118140960795 + 4920816 * 2 ^ 59
def prefixEnd_4920816 : Nat := 4983230072969 + 3 ^ 40 * 4920816 * 2
def baseEnd_4920816 : Nat := 2526743820334924518469585

theorem tailTrace_4920816 : CollatzResearch.WordTrace tailWord_4920816 prefixEnd_4920816 2526743820334924518469585 := by
  unfold tailWord_4920816
  simp only [CollatzResearch.WordTrace]
  refine ⟨89738452070365757654787151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119651269427154343539716201 89738452070365757654787151)
  ·
    refine ⟨134607678105548636482180727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89738452070365757654787151 134607678105548636482180727)
    ·
      refine ⟨201911517158322954723271091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134607678105548636482180727 201911517158322954723271091)
      ·
        refine ⟨302867275737484432084906637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201911517158322954723271091 302867275737484432084906637)
        ·
          refine ⟨113575228401556662031839989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 302867275737484432084906637 113575228401556662031839989)
          ·
            refine ⟨10647677662645937065484999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113575228401556662031839989 10647677662645937065484999)
            ·
              refine ⟨15971516493968905598227499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10647677662645937065484999 15971516493968905598227499)
              ·
                refine ⟨23957274740953358397341249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15971516493968905598227499 23957274740953358397341249)
                ·
                  refine ⟨17967956055715018798005937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23957274740953358397341249 17967956055715018798005937)
                  ·
                    refine ⟨13475967041786264098504453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17967956055715018798005937 13475967041786264098504453)
                    ·
                      refine ⟨2526743820334924518469585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13475967041786264098504453 2526743820334924518469585)
                      ·
                        rfl

theorem cell23_4920816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 4].length) (baseStart_4920816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920816 prefixEnd_4920816 := by exact prefixLift 4920816
  have htrace : WordTrace (prefixWord ++ tailWord_4920816) baseStart_4920816 baseEnd_4920816 := by
    simpa [prefixWord, tailWord_4920816, baseEnd_4920816] using wordTrace_append hprefix tailTrace_4920816
  have hstable : (prefixWord ++ tailWord_4920816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920816).length < 2 ^ (prefixWord ++ tailWord_4920816).sum := by decide
  have hdescent : baseEnd_4920816 < baseStart_4920816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920866 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_4920866 : Nat := 118140960795 + 4920866 * 2 ^ 59
def prefixEnd_4920866 : Nat := 4983230072969 + 3 ^ 40 * 4920866 * 2
def baseEnd_4920866 : Nat := 2526769494367649322844355

theorem tailTrace_4920866 : CollatzResearch.WordTrace tailWord_4920866 prefixEnd_4920866 2526769494367649322844355 := by
  unfold tailWord_4920866
  simp only [CollatzResearch.WordTrace]
  refine ⟨44869681947637593462223613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119652485193700249232596301 44869681947637593462223613)
  ·
    refine ⟨16826130730364097548333855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44869681947637593462223613 16826130730364097548333855)
    ·
      refine ⟨25239196095546146322500783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16826130730364097548333855 25239196095546146322500783)
      ·
        refine ⟨37858794143319219483751175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25239196095546146322500783 37858794143319219483751175)
        ·
          refine ⟨56788191214978829225626763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37858794143319219483751175 56788191214978829225626763)
          ·
            refine ⟨85182286822468243838440145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56788191214978829225626763 85182286822468243838440145)
            ·
              refine ⟨63886715116851182878830109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85182286822468243838440145 63886715116851182878830109)
              ·
                refine ⟨23957518168819193579561291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63886715116851182878830109 23957518168819193579561291)
                ·
                  refine ⟨35936277253228790369341937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23957518168819193579561291 35936277253228790369341937)
                  ·
                    refine ⟨26952207939921592777006453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35936277253228790369341937 26952207939921592777006453)
                    ·
                      refine ⟨2526769494367649322844355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26952207939921592777006453 2526769494367649322844355)
                      ·
                        rfl

theorem cell23_4920866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_4920866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920866 prefixEnd_4920866 := by exact prefixLift 4920866
  have htrace : WordTrace (prefixWord ++ tailWord_4920866) baseStart_4920866 baseEnd_4920866 := by
    simpa [prefixWord, tailWord_4920866, baseEnd_4920866] using wordTrace_append hprefix tailTrace_4920866
  have hstable : (prefixWord ++ tailWord_4920866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920866).length < 2 ^ (prefixWord ++ tailWord_4920866).sum := by decide
  have hdescent : baseEnd_4920866 < baseStart_4920866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920913 : List Nat := [1, 2, 2, 1, 3, 2, 3, 2, 2, 2, 3]
def baseStart_4920913 : Nat := 118140960795 + 4920913 * 2 ^ 59
def prefixEnd_4920913 : Nat := 4983230072969 + 3 ^ 40 * 4920913 * 2
def baseEnd_4920913 : Nat := 2526793627958410638956639

theorem tailTrace_4920913 : CollatzResearch.WordTrace tailWord_4920913 prefixEnd_4920913 2526793627958410638956639 := by
  unfold tailWord_4920913
  simp only [CollatzResearch.WordTrace]
  refine ⟨179480442021380100875855393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119653628014253400583903595 179480442021380100875855393)
  ·
    refine ⟨134610331516035075656891545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179480442021380100875855393 134610331516035075656891545)
    ·
      refine ⟨100957748637026306742668659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134610331516035075656891545 100957748637026306742668659)
      ·
        refine ⟨151436622955539460114002989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100957748637026306742668659 151436622955539460114002989)
        ·
          refine ⟨56788733608327297542751121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151436622955539460114002989 56788733608327297542751121)
          ·
            refine ⟨42591550206245473157063341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56788733608327297542751121 42591550206245473157063341)
            ·
              refine ⟨15971831327342052433898753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42591550206245473157063341 15971831327342052433898753)
              ·
                refine ⟨11978873495506539325424065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15971831327342052433898753 11978873495506539325424065)
                ·
                  refine ⟨8984155121629904494068049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11978873495506539325424065 8984155121629904494068049)
                  ·
                    refine ⟨6738116341222428370551037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8984155121629904494068049 6738116341222428370551037)
                    ·
                      refine ⟨2526793627958410638956639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6738116341222428370551037 2526793627958410638956639)
                      ·
                        rfl

theorem cell23_4920913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 2, 3].length) (baseStart_4920913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920913 prefixEnd_4920913 := by exact prefixLift 4920913
  have htrace : WordTrace (prefixWord ++ tailWord_4920913) baseStart_4920913 baseEnd_4920913 := by
    simpa [prefixWord, tailWord_4920913, baseEnd_4920913] using wordTrace_append hprefix tailTrace_4920913
  have hstable : (prefixWord ++ tailWord_4920913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920913).length < 2 ^ (prefixWord ++ tailWord_4920913).sum := by decide
  have hdescent : baseEnd_4920913 < baseStart_4920913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920916 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 8]
def baseStart_4920916 : Nat := 118140960795 + 4920916 * 2 ^ 59
def prefixEnd_4920916 : Nat := 4983230072969 + 3 ^ 40 * 4920916 * 2
def baseEnd_4920916 : Nat := 280755018711152680802125

theorem tailTrace_4920916 : CollatzResearch.WordTrace tailWord_4920916 prefixEnd_4920916 280755018711152680802125 := by
  unfold tailWord_4920916
  simp only [CollatzResearch.WordTrace]
  refine ⟨89740275720184616194107301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119653700960246154925476401 89740275720184616194107301)
  ·
    refine ⟨16826301697534615536395119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89740275720184616194107301 16826301697534615536395119)
    ·
      refine ⟨25239452546301923304592679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16826301697534615536395119 25239452546301923304592679)
      ·
        refine ⟨37859178819452884956889019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25239452546301923304592679 37859178819452884956889019)
        ·
          refine ⟨56788768229179327435333529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37859178819452884956889019 56788768229179327435333529)
          ·
            refine ⟨42591576171884495576500147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56788768229179327435333529 42591576171884495576500147)
            ·
              refine ⟨63887364257826743364750221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42591576171884495576500147 63887364257826743364750221)
              ·
                refine ⟨23957761596685028761781333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63887364257826743364750221 23957761596685028761781333)
                ·
                  refine ⟨280755018711152680802125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23957761596685028761781333 280755018711152680802125)
                  ·
                    rfl

theorem cell23_4920916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_4920916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920916 prefixEnd_4920916 := by exact prefixLift 4920916
  have htrace : WordTrace (prefixWord ++ tailWord_4920916) baseStart_4920916 baseEnd_4920916 := by
    simpa [prefixWord, tailWord_4920916, baseEnd_4920916] using wordTrace_append hprefix tailTrace_4920916
  have hstable : (prefixWord ++ tailWord_4920916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920916).length < 2 ^ (prefixWord ++ tailWord_4920916).sum := by decide
  have hdescent : baseEnd_4920916 < baseStart_4920916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920933 : List Nat := [1, 3, 1, 3, 3, 2, 1, 3, 6]
def baseStart_4920933 : Nat := 118140960795 + 4920933 * 2 ^ 59
def prefixEnd_4920933 : Nat := 4983230072969 + 3 ^ 40 * 4920933 * 2
def baseEnd_4920933 : Nat := 280755988619055617856283

theorem tailTrace_4920933 : CollatzResearch.WordTrace tailWord_4920933 prefixEnd_4920933 280755988619055617856283 := by
  unfold tailWord_4920933
  simp only [CollatzResearch.WordTrace]
  refine ⟨179481171481307644291583453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119654114320871762861055635 179481171481307644291583453)
  ·
    refine ⟨67305439305490366609343795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179481171481307644291583453 67305439305490366609343795)
    ·
      refine ⟨100958158958235549914015693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67305439305490366609343795 100958158958235549914015693)
      ·
        refine ⟨37859309609338331217755885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100958158958235549914015693 37859309609338331217755885)
        ·
          refine ⟨14197241103501874206658457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37859309609338331217755885 14197241103501874206658457)
          ·
            refine ⟨10647930827626405654993843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14197241103501874206658457 10647930827626405654993843)
            ·
              refine ⟨15971896241439608482490765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10647930827626405654993843 15971896241439608482490765)
              ·
                refine ⟨5989461090539853180934037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15971896241439608482490765 5989461090539853180934037)
                ·
                  refine ⟨280755988619055617856283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5989461090539853180934037 280755988619055617856283)
                  ·
                    rfl

theorem cell23_4920933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 6].length) (baseStart_4920933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920933 prefixEnd_4920933 := by exact prefixLift 4920933
  have htrace : WordTrace (prefixWord ++ tailWord_4920933) baseStart_4920933 baseEnd_4920933 := by
    simpa [prefixWord, tailWord_4920933, baseEnd_4920933] using wordTrace_append hprefix tailTrace_4920933
  have hstable : (prefixWord ++ tailWord_4920933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920933).length < 2 ^ (prefixWord ++ tailWord_4920933).sum := by decide
  have hdescent : baseEnd_4920933 < baseStart_4920933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920943 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 5, 1, 3]
def baseStart_4920943 : Nat := 118140960795 + 4920943 * 2 ^ 59
def prefixEnd_4920943 : Nat := 4983230072969 + 3 ^ 40 * 4920943 * 2
def baseEnd_4920943 : Nat := 2526809032378045521581501

theorem tailTrace_4920943 : CollatzResearch.WordTrace tailWord_4920943 prefixEnd_4920943 2526809032378045521581501 := by
  unfold tailWord_4920943
  simp only [CollatzResearch.WordTrace]
  refine ⟨179481536211271415999447483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119654357474180943999631655 179481536211271415999447483)
  ·
    refine ⟨269222304316907123999171225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179481536211271415999447483 269222304316907123999171225)
    ·
      refine ⟨201916728237680342999378419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269222304316907123999171225 201916728237680342999378419)
      ·
        refine ⟨302875092356520514499067629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201916728237680342999378419 302875092356520514499067629)
        ·
          refine ⟨113578159633695192937150361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 302875092356520514499067629 113578159633695192937150361)
          ·
            refine ⟨85183619725271394702862771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113578159633695192937150361 85183619725271394702862771)
            ·
              refine ⟨127775429587907092054294157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85183619725271394702862771 127775429587907092054294157)
              ·
                refine ⟨47915786095465159520360309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127775429587907092054294157 47915786095465159520360309)
                ·
                  refine ⟨4492104946449858705033779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47915786095465159520360309 4492104946449858705033779)
                  ·
                    refine ⟨6738157419674788057550669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4492104946449858705033779 6738157419674788057550669)
                    ·
                      refine ⟨2526809032378045521581501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6738157419674788057550669 2526809032378045521581501)
                      ·
                        rfl

theorem cell23_4920943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 1, 3].length) (baseStart_4920943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920943 prefixEnd_4920943 := by exact prefixLift 4920943
  have htrace : WordTrace (prefixWord ++ tailWord_4920943) baseStart_4920943 baseEnd_4920943 := by
    simpa [prefixWord, tailWord_4920943, baseEnd_4920943] using wordTrace_append hprefix tailTrace_4920943
  have hstable : (prefixWord ++ tailWord_4920943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920943).length < 2 ^ (prefixWord ++ tailWord_4920943).sum := by decide
  have hdescent : baseEnd_4920943 < baseStart_4920943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920983 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 4]
def baseStart_4920983 : Nat := 118140960795 + 4920983 * 2 ^ 59
def prefixEnd_4920983 : Nat := 4983230072969 + 3 ^ 40 * 4920983 * 2
def baseEnd_4920983 : Nat := 2526829571604225365081317

theorem tailTrace_4920983 : CollatzResearch.WordTrace tailWord_4920983 prefixEnd_4920983 2526829571604225365081317 := by
  unfold tailWord_4920983
  simp only [CollatzResearch.WordTrace]
  refine ⟨179482995131126502830903603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119655330087417668553935735 179482995131126502830903603)
  ·
    refine ⟨269224492696689754246355405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179482995131126502830903603 269224492696689754246355405)
    ·
      refine ⟨100959184761258657842383277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269224492696689754246355405 100959184761258657842383277)
      ·
        refine ⟨37859694285471996690893729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100959184761258657842383277 37859694285471996690893729)
        ·
          refine ⟨28394770714103997518170297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37859694285471996690893729 28394770714103997518170297)
          ·
            refine ⟨21296078035577998138627723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28394770714103997518170297 21296078035577998138627723)
            ·
              refine ⟨31944117053366997207941585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21296078035577998138627723 31944117053366997207941585)
              ·
                refine ⟨23958087790025247905956189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31944117053366997207941585 23958087790025247905956189)
                ·
                  refine ⟨8984282921259467964733571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23958087790025247905956189 8984282921259467964733571)
                  ·
                    refine ⟨13476424381889201947100357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8984282921259467964733571 13476424381889201947100357)
                    ·
                      refine ⟨2526829571604225365081317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13476424381889201947100357 2526829571604225365081317)
                      ·
                        rfl

theorem cell23_4920983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_4920983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920983 prefixEnd_4920983 := by exact prefixLift 4920983
  have htrace : WordTrace (prefixWord ++ tailWord_4920983) baseStart_4920983 baseEnd_4920983 := by
    simpa [prefixWord, tailWord_4920983, baseEnd_4920983] using wordTrace_append hprefix tailTrace_4920983
  have hstable : (prefixWord ++ tailWord_4920983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920983).length < 2 ^ (prefixWord ++ tailWord_4920983).sum := by decide
  have hdescent : baseEnd_4920983 < baseStart_4920983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920993 : List Nat := [1, 2, 3, 3, 2, 1, 1, 3, 1, 6]
def baseStart_4920993 : Nat := 118140960795 + 4920993 * 2 ^ 59
def prefixEnd_4920993 : Nat := 4983230072969 + 3 ^ 40 * 4920993 * 2
def baseEnd_4920993 : Nat := 842278235470256775318757

theorem tailTrace_4920993 : CollatzResearch.WordTrace tailWord_4920993 prefixEnd_4920993 842278235470256775318757 := by
  unfold tailWord_4920993
  simp only [CollatzResearch.WordTrace]
  refine ⟨179483359861090274538767633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119655573240726849692511755 179483359861090274538767633)
  ·
    refine ⟨134612519895817705904075725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179483359861090274538767633 134612519895817705904075725)
    ·
      refine ⟨50479694960931639714028397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134612519895817705904075725 50479694960931639714028397)
      ·
        refine ⟨18929885610349364892760649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50479694960931639714028397 18929885610349364892760649)
        ·
          refine ⟨14197414207762023669570487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18929885610349364892760649 14197414207762023669570487)
          ·
            refine ⟨21296121311643035504355731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14197414207762023669570487 21296121311643035504355731)
            ·
              refine ⟨31944181967464553256533597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21296121311643035504355731 31944181967464553256533597)
              ·
                refine ⟨11979068237799207471200099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31944181967464553256533597 11979068237799207471200099)
                ·
                  refine ⟨17968602356698811206800149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11979068237799207471200099 17968602356698811206800149)
                  ·
                    refine ⟨842278235470256775318757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17968602356698811206800149 842278235470256775318757)
                    ·
                      rfl

theorem cell23_4920993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_4920993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920993 prefixEnd_4920993 := by exact prefixLift 4920993
  have htrace : WordTrace (prefixWord ++ tailWord_4920993) baseStart_4920993 baseEnd_4920993 := by
    simpa [prefixWord, tailWord_4920993, baseEnd_4920993] using wordTrace_append hprefix tailTrace_4920993
  have hstable : (prefixWord ++ tailWord_4920993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920993).length < 2 ^ (prefixWord ++ tailWord_4920993).sum := by decide
  have hdescent : baseEnd_4920993 < baseStart_4920993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4920994 : List Nat := [3, 3, 1, 4, 1, 1, 1, 2, 3, 1, 3]
def baseStart_4920994 : Nat := 118140960795 + 4920994 * 2 ^ 59
def prefixEnd_4920994 : Nat := 4983230072969 + 3 ^ 40 * 4920994 * 2
def baseEnd_4920994 : Nat := 2526835219891424822043767

theorem tailTrace_4920994 : CollatzResearch.WordTrace tailWord_4920994 prefixEnd_4920994 2526835219891424822043767 := by
  unfold tailWord_4920994
  simp only [CollatzResearch.WordTrace]
  refine ⟨44870849083521662927388509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119655597556057767806369357 44870849083521662927388509)
  ·
    refine ⟨16826568406320623597770691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44870849083521662927388509 16826568406320623597770691)
    ·
      refine ⟨25239852609480935396656037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16826568406320623597770691 25239852609480935396656037)
      ·
        refine ⟨4732472364277675386873007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25239852609480935396656037 4732472364277675386873007)
        ·
          refine ⟨7098708546416513080309511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4732472364277675386873007 7098708546416513080309511)
          ·
            refine ⟨10648062819624769620464267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7098708546416513080309511 10648062819624769620464267)
            ·
              refine ⟨15972094229437154430696401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10648062819624769620464267 15972094229437154430696401)
              ·
                refine ⟨11979070672077865823022301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15972094229437154430696401 11979070672077865823022301)
                ·
                  refine ⟨4492151502029199683633363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11979070672077865823022301 4492151502029199683633363)
                  ·
                    refine ⟨6738227253043799525450045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4492151502029199683633363 6738227253043799525450045)
                    ·
                      refine ⟨2526835219891424822043767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6738227253043799525450045 2526835219891424822043767)
                      ·
                        rfl

theorem cell23_4920994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_4920994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4920994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4920994 prefixEnd_4920994 := by exact prefixLift 4920994
  have htrace : WordTrace (prefixWord ++ tailWord_4920994) baseStart_4920994 baseEnd_4920994 := by
    simpa [prefixWord, tailWord_4920994, baseEnd_4920994] using wordTrace_append hprefix tailTrace_4920994
  have hstable : (prefixWord ++ tailWord_4920994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4920994).length < 2 ^ (prefixWord ++ tailWord_4920994).sum := by decide
  have hdescent : baseEnd_4920994 < baseStart_4920994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4920994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921014 : List Nat := [5, 1, 3, 1, 1, 1, 4, 1, 1, 5]
def baseStart_4921014 : Nat := 118140960795 + 4921014 * 2 ^ 59
def prefixEnd_4921014 : Nat := 4983230072969 + 3 ^ 40 * 4921014 * 2
def baseEnd_4921014 : Nat := 842281829834838247931225

theorem tailTrace_4921014 : CollatzResearch.WordTrace tailWord_4921014 prefixEnd_4921014 842281829834838247931225 := by
  unfold tailWord_4921014
  simp only [CollatzResearch.WordTrace]
  refine ⟨11217757862125887195330131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119656083862676130083521397 11217757862125887195330131)
  ·
    refine ⟨16826636793188830792995197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11217757862125887195330131 16826636793188830792995197)
    ·
      refine ⟨6309988797445811547373199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16826636793188830792995197 6309988797445811547373199)
      ·
        refine ⟨9464983196168717321059799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6309988797445811547373199 9464983196168717321059799)
        ·
          refine ⟨14197474794253075981589699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9464983196168717321059799 14197474794253075981589699)
          ·
            refine ⟨21296212191379613972384549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14197474794253075981589699 21296212191379613972384549)
            ·
              refine ⟨3993039785883677619822103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21296212191379613972384549 3993039785883677619822103)
              ·
                refine ⟨5989559678825516429733155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3993039785883677619822103 5989559678825516429733155)
                ·
                  refine ⟨8984339518238274644599733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5989559678825516429733155 8984339518238274644599733)
                  ·
                    refine ⟨842281829834838247931225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8984339518238274644599733 842281829834838247931225)
                    ·
                      rfl

theorem cell23_4921014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_4921014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921014 prefixEnd_4921014 := by exact prefixLift 4921014
  have htrace : WordTrace (prefixWord ++ tailWord_4921014) baseStart_4921014 baseEnd_4921014 := by
    simpa [prefixWord, tailWord_4921014, baseEnd_4921014] using wordTrace_append hprefix tailTrace_4921014
  have hstable : (prefixWord ++ tailWord_4921014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921014).length < 2 ^ (prefixWord ++ tailWord_4921014).sum := by decide
  have hdescent : baseEnd_4921014 < baseStart_4921014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921034 : List Nat := [3, 1, 2, 1, 5, 1, 2, 1, 3, 2, 2]
def baseStart_4921034 : Nat := 118140960795 + 4921034 * 2 ^ 59
def prefixEnd_4921034 : Nat := 4983230072969 + 3 ^ 40 * 4921034 * 2
def baseEnd_4921034 : Nat := 2526855759117604665543583

theorem tailTrace_4921034 : CollatzResearch.WordTrace tailWord_4921034 prefixEnd_4921034 2526855759117604665543583 := by
  unfold tailWord_4921034
  simp only [CollatzResearch.WordTrace]
  refine ⟨44871213813485434635252539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119656570169294492360673437 44871213813485434635252539)
  ·
    refine ⟨67306820720228151952878809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44871213813485434635252539 67306820720228151952878809)
    ·
      refine ⟨50480115540171113964659107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67306820720228151952878809 50480115540171113964659107)
      ·
        refine ⟨75720173310256670946988661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50480115540171113964659107 75720173310256670946988661)
        ·
          refine ⟨7098766247836562901280187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75720173310256670946988661 7098766247836562901280187)
          ·
            refine ⟨10648149371754844351920281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7098766247836562901280187 10648149371754844351920281)
            ·
              refine ⟨7986112028816133263940211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10648149371754844351920281 7986112028816133263940211)
              ·
                refine ⟨11979168043224199895910317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7986112028816133263940211 11979168043224199895910317)
                ·
                  refine ⟨4492188016209074960966369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11979168043224199895910317 4492188016209074960966369)
                  ·
                    refine ⟨3369141012156806220724777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4492188016209074960966369 3369141012156806220724777)
                    ·
                      refine ⟨2526855759117604665543583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3369141012156806220724777 2526855759117604665543583)
                      ·
                        rfl

theorem cell23_4921034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 3, 2, 2].length) (baseStart_4921034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921034 prefixEnd_4921034 := by exact prefixLift 4921034
  have htrace : WordTrace (prefixWord ++ tailWord_4921034) baseStart_4921034 baseEnd_4921034 := by
    simpa [prefixWord, tailWord_4921034, baseEnd_4921034] using wordTrace_append hprefix tailTrace_4921034
  have hstable : (prefixWord ++ tailWord_4921034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921034).length < 2 ^ (prefixWord ++ tailWord_4921034).sum := by decide
  have hdescent : baseEnd_4921034 < baseStart_4921034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921037 : List Nat := [1, 6, 2, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_4921037 : Nat := 118140960795 + 4921037 * 2 ^ 59
def prefixEnd_4921037 : Nat := 4983230072969 + 3 ^ 40 * 4921037 * 2
def baseEnd_4921037 : Nat := 2526857299559568153806069

theorem tailTrace_4921037 : CollatzResearch.WordTrace tailWord_4921037 prefixEnd_4921037 2526857299559568153806069 := by
  unfold tailWord_4921037
  simp only [CollatzResearch.WordTrace]
  refine ⟨179484964672930870053369365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119656643115287246702246243 179484964672930870053369365)
  ·
    refine ⟨8413357719043634533751689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 179484964672930870053369365 8413357719043634533751689)
    ·
      refine ⟨6310018289282725900313767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8413357719043634533751689 6310018289282725900313767)
      ·
        refine ⟨9465027433924088850470651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6310018289282725900313767 9465027433924088850470651)
        ·
          refine ⟨14197541150886133275705977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9465027433924088850470651 14197541150886133275705977)
          ·
            refine ⟨10648155863164599956779483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14197541150886133275705977 10648155863164599956779483)
            ·
              refine ⟨15972233794746899935169225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10648155863164599956779483 15972233794746899935169225)
              ·
                refine ⟨11979175346060174951376919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15972233794746899935169225 11979175346060174951376919)
                ·
                  refine ⟨17968763019090262427065379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11979175346060174951376919 17968763019090262427065379)
                  ·
                    refine ⟨26953144528635393640598069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17968763019090262427065379 26953144528635393640598069)
                    ·
                      refine ⟨2526857299559568153806069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26953144528635393640598069 2526857299559568153806069)
                      ·
                        rfl

theorem cell23_4921037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_4921037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921037 prefixEnd_4921037 := by exact prefixLift 4921037
  have htrace : WordTrace (prefixWord ++ tailWord_4921037) baseStart_4921037 baseEnd_4921037 := by
    simpa [prefixWord, tailWord_4921037, baseEnd_4921037] using wordTrace_append hprefix tailTrace_4921037
  have hstable : (prefixWord ++ tailWord_4921037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921037).length < 2 ^ (prefixWord ++ tailWord_4921037).sum := by decide
  have hdescent : baseEnd_4921037 < baseStart_4921037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921044 : List Nat := [2, 4, 1, 3, 1, 2, 3, 1, 2, 4]
def baseStart_4921044 : Nat := 118140960795 + 4921044 * 2 ^ 59
def prefixEnd_4921044 : Nat := 4983230072969 + 3 ^ 40 * 4921044 * 2
def baseEnd_4921044 : Nat := 842286964641383208806179

theorem tailTrace_4921044 : CollatzResearch.WordTrace tailWord_4921044 prefixEnd_4921044 842286964641383208806179 := by
  unfold tailWord_4921044
  simp only [CollatzResearch.WordTrace]
  refine ⟨89742609991952755124437093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119656813322603673499249457 89742609991952755124437093)
  ·
    refine ⟨16826739373491141585831955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89742609991952755124437093 16826739373491141585831955)
    ·
      refine ⟨25240109060236712378747933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16826739373491141585831955 25240109060236712378747933)
      ·
        refine ⟨9465040897588767142030475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25240109060236712378747933 9465040897588767142030475)
        ·
          refine ⟨14197561346383150713045713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9465040897588767142030475 14197561346383150713045713)
          ·
            refine ⟨10648171009787363034784285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14197561346383150713045713 10648171009787363034784285)
            ·
              refine ⟨3993064128670261138044107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10648171009787363034784285 3993064128670261138044107)
              ·
                refine ⟨5989596193005391707066161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3993064128670261138044107 5989596193005391707066161)
                ·
                  refine ⟨4492197144754043780299621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5989596193005391707066161 4492197144754043780299621)
                  ·
                    refine ⟨842286964641383208806179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4492197144754043780299621 842286964641383208806179)
                    ·
                      rfl

theorem cell23_4921044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_4921044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921044 prefixEnd_4921044 := by exact prefixLift 4921044
  have htrace : WordTrace (prefixWord ++ tailWord_4921044) baseStart_4921044 baseEnd_4921044 := by
    simpa [prefixWord, tailWord_4921044, baseEnd_4921044] using wordTrace_append hprefix tailTrace_4921044
  have hstable : (prefixWord ++ tailWord_4921044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921044).length < 2 ^ (prefixWord ++ tailWord_4921044).sum := by decide
  have hdescent : baseEnd_4921044 < baseStart_4921044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921050 : List Nat := [3, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3]
def baseStart_4921050 : Nat := 118140960795 + 4921050 * 2 ^ 59
def prefixEnd_4921050 : Nat := 4983230072969 + 3 ^ 40 * 4921050 * 2
def baseEnd_4921050 : Nat := 2526863974808076602943509

theorem tailTrace_4921050 : CollatzResearch.WordTrace tailWord_4921050 prefixEnd_4921050 2526863974808076602943509 := by
  unfold tailWord_4921050
  simp only [CollatzResearch.WordTrace]
  refine ⟨44871359705470943318398151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119656959214589182182395069 44871359705470943318398151)
  ·
    refine ⟨67307039558206414977597227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44871359705470943318398151 67307039558206414977597227)
    ·
      refine ⟨100960559337309622466395841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67307039558206414977597227 100960559337309622466395841)
      ·
        refine ⟨75720419502982216849796881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100960559337309622466395841 75720419502982216849796881)
        ·
          refine ⟨56790314627236662637347661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75720419502982216849796881 56790314627236662637347661)
          ·
            refine ⟨21296367985213748489005373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56790314627236662637347661 21296367985213748489005373)
            ·
              refine ⟨7986137994455155683377015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21296367985213748489005373 7986137994455155683377015)
              ·
                refine ⟨11979206991682733525065523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7986137994455155683377015 11979206991682733525065523)
                ·
                  refine ⟨17968810487524100287598285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11979206991682733525065523 17968810487524100287598285)
                  ·
                    refine ⟨6738303932821537607849357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17968810487524100287598285 6738303932821537607849357)
                    ·
                      refine ⟨2526863974808076602943509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6738303932821537607849357 2526863974808076602943509)
                      ·
                        rfl

theorem cell23_4921050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_4921050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921050 prefixEnd_4921050 := by exact prefixLift 4921050
  have htrace : WordTrace (prefixWord ++ tailWord_4921050) baseStart_4921050 baseEnd_4921050 := by
    simpa [prefixWord, tailWord_4921050, baseEnd_4921050] using wordTrace_append hprefix tailTrace_4921050
  have hstable : (prefixWord ++ tailWord_4921050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921050).length < 2 ^ (prefixWord ++ tailWord_4921050).sum := by decide
  have hdescent : baseEnd_4921050 < baseStart_4921050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921057 : List Nat := [1, 2, 3, 1, 6, 1, 2, 7]
def baseStart_4921057 : Nat := 118140960795 + 4921057 * 2 ^ 59
def prefixEnd_4921057 : Nat := 4983230072969 + 3 ^ 40 * 4921057 * 2
def baseEnd_4921057 : Nat := 93587687747135484279851

theorem tailTrace_4921057 : CollatzResearch.WordTrace tailWord_4921057 prefixEnd_4921057 93587687747135484279851 := by
  unfold tailWord_4921057
  simp only [CollatzResearch.WordTrace]
  refine ⟨179485694132858413469097425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119657129421905608979398283 179485694132858413469097425)
  ·
    refine ⟨134614270599643810101823069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179485694132858413469097425 134614270599643810101823069)
    ·
      refine ⟨50480351474866428788183651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134614270599643810101823069 50480351474866428788183651)
      ·
        refine ⟨75720527212299643182275477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50480351474866428788183651 75720527212299643182275477)
        ·
          refine ⟨3549399713076545774169163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 75720527212299643182275477 3549399713076545774169163)
          ·
            refine ⟨5324099569614818661253745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3549399713076545774169163 5324099569614818661253745)
            ·
              refine ⟨3993074677211113995940309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5324099569614818661253745 3993074677211113995940309)
              ·
                refine ⟨93587687747135484279851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3993074677211113995940309 93587687747135484279851)
                ·
                  rfl

theorem cell23_4921057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 7].length) (baseStart_4921057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921057 prefixEnd_4921057 := by exact prefixLift 4921057
  have htrace : WordTrace (prefixWord ++ tailWord_4921057) baseStart_4921057 baseEnd_4921057 := by
    simpa [prefixWord, tailWord_4921057, baseEnd_4921057] using wordTrace_append hprefix tailTrace_4921057
  have hstable : (prefixWord ++ tailWord_4921057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921057).length < 2 ^ (prefixWord ++ tailWord_4921057).sum := by decide
  have hdescent : baseEnd_4921057 < baseStart_4921057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921090 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_4921090 : Nat := 118140960795 + 4921090 * 2 ^ 59
def prefixEnd_4921090 : Nat := 4983230072969 + 3 ^ 40 * 4921090 * 2
def baseEnd_4921090 : Nat := 2526884514034256446443325

theorem tailTrace_4921090 : CollatzResearch.WordTrace tailWord_4921090 prefixEnd_4921090 2526884514034256446443325 := by
  unfold tailWord_4921090
  simp only [CollatzResearch.WordTrace]
  refine ⟨44871724435434715026262181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119657931827825906736699149 44871724435434715026262181)
  ·
    refine ⟨8413448331644009067424159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44871724435434715026262181 8413448331644009067424159)
    ·
      refine ⟨12620172497466013601136239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8413448331644009067424159 12620172497466013601136239)
      ·
        refine ⟨18930258746199020401704359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12620172497466013601136239 18930258746199020401704359)
        ·
          refine ⟨28395388119298530602556539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18930258746199020401704359 28395388119298530602556539)
          ·
            refine ⟨42593082178947795903834809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28395388119298530602556539 42593082178947795903834809)
            ·
              refine ⟨31944811634210846927876107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42593082178947795903834809 31944811634210846927876107)
              ·
                refine ⟨47917217451316270391814161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31944811634210846927876107 47917217451316270391814161)
                ·
                  refine ⟨35937913088487202793860621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47917217451316270391814161 35937913088487202793860621)
                  ·
                    refine ⟨13476717408182701047697733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35937913088487202793860621 13476717408182701047697733)
                    ·
                      refine ⟨2526884514034256446443325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13476717408182701047697733 2526884514034256446443325)
                      ·
                        rfl

theorem cell23_4921090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_4921090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921090 prefixEnd_4921090 := by exact prefixLift 4921090
  have htrace : WordTrace (prefixWord ++ tailWord_4921090) baseStart_4921090 baseEnd_4921090 := by
    simpa [prefixWord, tailWord_4921090, baseEnd_4921090] using wordTrace_append hprefix tailTrace_4921090
  have hstable : (prefixWord ++ tailWord_4921090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921090).length < 2 ^ (prefixWord ++ tailWord_4921090).sum := by decide
  have hdescent : baseEnd_4921090 < baseStart_4921090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921141 : List Nat := [1, 3, 3, 1, 4, 1, 2, 2, 2, 2, 2]
def baseStart_4921141 : Nat := 118140960795 + 4921141 * 2 ^ 59
def prefixEnd_4921141 : Nat := 4983230072969 + 3 ^ 40 * 4921141 * 2
def baseEnd_4921141 : Nat := 2526910701547635746905591

theorem tailTrace_4921141 : CollatzResearch.WordTrace tailWord_4921141 prefixEnd_4921141 2526910701547635746905591 := by
  unfold tailWord_4921141
  simp only [CollatzResearch.WordTrace]
  refine ⟨179488757864554095815155277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119659171909702730543436851 179488757864554095815155277)
  ·
    refine ⟨67308284199207785930683229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179488757864554095815155277 67308284199207785930683229)
    ·
      refine ⟨25240606574702919724006211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67308284199207785930683229 25240606574702919724006211)
      ·
        refine ⟨37860909862054379586009317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25240606574702919724006211 37860909862054379586009317)
        ·
          refine ⟨7098920599135196172376747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37860909862054379586009317 7098920599135196172376747)
          ·
            refine ⟨10648380898702794258565121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7098920599135196172376747 10648380898702794258565121)
            ·
              refine ⟨7986285674027095693923841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10648380898702794258565121 7986285674027095693923841)
              ·
                refine ⟨5989714255520321770442881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7986285674027095693923841 5989714255520321770442881)
                ·
                  refine ⟨4492285691640241327832161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5989714255520321770442881 4492285691640241327832161)
                  ·
                    refine ⟨3369214268730180995874121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4492285691640241327832161 3369214268730180995874121)
                    ·
                      refine ⟨2526910701547635746905591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3369214268730180995874121 2526910701547635746905591)
                      ·
                        rfl

theorem cell23_4921141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_4921141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921141 prefixEnd_4921141 := by exact prefixLift 4921141
  have htrace : WordTrace (prefixWord ++ tailWord_4921141) baseStart_4921141 baseEnd_4921141 := by
    simpa [prefixWord, tailWord_4921141, baseEnd_4921141] using wordTrace_append hprefix tailTrace_4921141
  have hstable : (prefixWord ++ tailWord_4921141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921141).length < 2 ^ (prefixWord ++ tailWord_4921141).sum := by decide
  have hdescent : baseEnd_4921141 < baseStart_4921141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921143 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 4, 5]
def baseStart_4921143 : Nat := 118140960795 + 4921143 * 2 ^ 59
def prefixEnd_4921143 : Nat := 4983230072969 + 3 ^ 40 * 4921143 * 2
def baseEnd_4921143 : Nat := 842303909502981579693527

theorem tailTrace_4921143 : CollatzResearch.WordTrace tailWord_4921143 prefixEnd_4921143 842303909502981579693527 := by
  unfold tailWord_4921143
  simp only [CollatzResearch.WordTrace]
  refine ⟨179488830810546850156728083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119659220540364566771152055 179488830810546850156728083)
  ·
    refine ⟨269233246215820275235092125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179488830810546850156728083 269233246215820275235092125)
    ·
      refine ⟨100962467330932603213159547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269233246215820275235092125 100962467330932603213159547)
      ·
        refine ⟨151443700996398904819739321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100962467330932603213159547 151443700996398904819739321)
        ·
          refine ⟨113582775747299178614804491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151443700996398904819739321 113582775747299178614804491)
          ·
            refine ⟨170374163620948767922206737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113582775747299178614804491 170374163620948767922206737)
            ·
              refine ⟨127780622715711575941655053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170374163620948767922206737 127780622715711575941655053)
              ·
                refine ⟨47917733518391840978120645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127780622715711575941655053 47917733518391840978120645)
                ·
                  refine ⟨8984575034698470183397621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47917733518391840978120645 8984575034698470183397621)
                  ·
                    refine ⟨842303909502981579693527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8984575034698470183397621 842303909502981579693527)
                    ·
                      rfl

theorem cell23_4921143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_4921143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921143 prefixEnd_4921143 := by exact prefixLift 4921143
  have htrace : WordTrace (prefixWord ++ tailWord_4921143) baseStart_4921143 baseEnd_4921143 := by
    simpa [prefixWord, tailWord_4921143, baseEnd_4921143] using wordTrace_append hprefix tailTrace_4921143
  have hstable : (prefixWord ++ tailWord_4921143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921143).length < 2 ^ (prefixWord ++ tailWord_4921143).sum := by decide
  have hdescent : baseEnd_4921143 < baseStart_4921143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921158 : List Nat := [6, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2]
def baseStart_4921158 : Nat := 118140960795 + 4921158 * 2 ^ 59
def prefixEnd_4921158 : Nat := 4983230072969 + 3 ^ 40 * 4921158 * 2
def baseEnd_4921158 : Nat := 2526919430718762180393013

theorem tailTrace_4921158 : CollatzResearch.WordTrace tailWord_4921158 prefixEnd_4921158 2526919430718762180393013 := by
  unfold tailWord_4921158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5609043059546640866203879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 119659585270328338479016085 5609043059546640866203879)
  ·
    refine ⟨8413564589319961299305819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5609043059546640866203879 8413564589319961299305819)
    ·
      refine ⟨12620346883979941948958729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8413564589319961299305819 12620346883979941948958729)
      ·
        refine ⟨9465260162984956461719047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12620346883979941948958729 9465260162984956461719047)
        ·
          refine ⟨14197890244477434692578571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9465260162984956461719047 14197890244477434692578571)
          ·
            refine ⟨21296835366716152038867857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14197890244477434692578571 21296835366716152038867857)
            ·
              refine ⟨15972626525037114029150893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21296835366716152038867857 15972626525037114029150893)
              ·
                refine ⟨5989734946888917760931585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15972626525037114029150893 5989734946888917760931585)
                ·
                  refine ⟨4492301210166688320698689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5989734946888917760931585 4492301210166688320698689)
                  ·
                    refine ⟨3369225907625016240524017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4492301210166688320698689 3369225907625016240524017)
                    ·
                      refine ⟨2526919430718762180393013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3369225907625016240524017 2526919430718762180393013)
                      ·
                        rfl

theorem cell23_4921158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_4921158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921158 prefixEnd_4921158 := by exact prefixLift 4921158
  have htrace : WordTrace (prefixWord ++ tailWord_4921158) baseStart_4921158 baseEnd_4921158 := by
    simpa [prefixWord, tailWord_4921158, baseEnd_4921158] using wordTrace_append hprefix tailTrace_4921158
  have hstable : (prefixWord ++ tailWord_4921158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921158).length < 2 ^ (prefixWord ++ tailWord_4921158).sum := by decide
  have hdescent : baseEnd_4921158 < baseStart_4921158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921193 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 1, 6, 4]
def baseStart_4921193 : Nat := 118140960795 + 4921193 * 2 ^ 59
def prefixEnd_4921193 : Nat := 4983230072969 + 3 ^ 40 * 4921193 * 2
def baseEnd_4921193 : Nat := 2526937402541669543455351

theorem tailTrace_4921193 : CollatzResearch.WordTrace tailWord_4921193 prefixEnd_4921193 2526937402541669543455351 := by
  unfold tailWord_4921193
  simp only [CollatzResearch.WordTrace]
  refine ⟨179490654460365708696048233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119660436306910472464032155 179490654460365708696048233)
  ·
    refine ⟨134617990845274281522036175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179490654460365708696048233 134617990845274281522036175)
    ·
      refine ⟨201926986267911422283054263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134617990845274281522036175 201926986267911422283054263)
      ·
        refine ⟨302890479401867133424581395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201926986267911422283054263 302890479401867133424581395)
        ·
          refine ⟨454335719102800700136872093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302890479401867133424581395 454335719102800700136872093)
          ·
            refine ⟨170375894663550262551327035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 454335719102800700136872093 170375894663550262551327035)
            ·
              refine ⟨255563841995325393826990553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170375894663550262551327035 255563841995325393826990553)
              ·
                refine ⟨191672881496494045370242915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255563841995325393826990553 191672881496494045370242915)
                ·
                  refine ⟨287509322244741068055364373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191672881496494045370242915 287509322244741068055364373)
                  ·
                    refine ⟨13476999480222237565095205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 287509322244741068055364373 13476999480222237565095205)
                    ·
                      refine ⟨2526937402541669543455351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13476999480222237565095205 2526937402541669543455351)
                      ·
                        rfl

theorem cell23_4921193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 6, 4].length) (baseStart_4921193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921193 prefixEnd_4921193 := by exact prefixLift 4921193
  have htrace : WordTrace (prefixWord ++ tailWord_4921193) baseStart_4921193 baseEnd_4921193 := by
    simpa [prefixWord, tailWord_4921193, baseEnd_4921193] using wordTrace_append hprefix tailTrace_4921193
  have hstable : (prefixWord ++ tailWord_4921193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921193).length < 2 ^ (prefixWord ++ tailWord_4921193).sum := by decide
  have hdescent : baseEnd_4921193 < baseStart_4921193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921197 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 2, 4, 2]
def baseStart_4921197 : Nat := 118140960795 + 4921197 * 2 ^ 59
def prefixEnd_4921197 : Nat := 4983230072969 + 3 ^ 40 * 4921197 * 2
def baseEnd_4921197 : Nat := 2526939456464287527805333

theorem tailTrace_4921197 : CollatzResearch.WordTrace tailWord_4921197 prefixEnd_4921197 2526939456464287527805333 := by
  unfold tailWord_4921197
  simp only [CollatzResearch.WordTrace]
  refine ⟨179490800352351217379193845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119660533568234144919462563 179490800352351217379193845)
  ·
    refine ⟨16827262533032926629299423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 179490800352351217379193845 16827262533032926629299423)
    ·
      refine ⟨25240893799549389943949135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16827262533032926629299423 25240893799549389943949135)
      ·
        refine ⟨37861340699324084915923703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25240893799549389943949135 37861340699324084915923703)
        ·
          refine ⟨56792011048986127373885555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37861340699324084915923703 56792011048986127373885555)
          ·
            refine ⟨85188016573479191060828333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56792011048986127373885555 85188016573479191060828333)
            ·
              refine ⟨31945506215054696647810625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85188016573479191060828333 31945506215054696647810625)
              ·
                refine ⟨23959129661291022485857969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31945506215054696647810625 23959129661291022485857969)
                ·
                  refine ⟨17969347245968266864393477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23959129661291022485857969 17969347245968266864393477)
                  ·
                    refine ⟨3369252608619050037073777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17969347245968266864393477 3369252608619050037073777)
                    ·
                      refine ⟨2526939456464287527805333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3369252608619050037073777 2526939456464287527805333)
                      ·
                        rfl

theorem cell23_4921197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_4921197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921197 prefixEnd_4921197 := by exact prefixLift 4921197
  have htrace : WordTrace (prefixWord ++ tailWord_4921197) baseStart_4921197 baseEnd_4921197 := by
    simpa [prefixWord, tailWord_4921197, baseEnd_4921197] using wordTrace_append hprefix tailTrace_4921197
  have hstable : (prefixWord ++ tailWord_4921197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921197).length < 2 ^ (prefixWord ++ tailWord_4921197).sum := by decide
  have hdescent : baseEnd_4921197 < baseStart_4921197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921200 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 3]
def baseStart_4921200 : Nat := 118140960795 + 4921200 * 2 ^ 59
def prefixEnd_4921200 : Nat := 4983230072969 + 3 ^ 40 * 4921200 * 2
def baseEnd_4921200 : Nat := 2526940996906251016067819

theorem tailTrace_4921200 : CollatzResearch.WordTrace tailWord_4921200 prefixEnd_4921200 2526940996906251016067819 := by
  unfold tailWord_4921200
  simp only [CollatzResearch.WordTrace]
  refine ⟨89745454885670174445776527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119660606514226899261035369 89745454885670174445776527)
  ·
    refine ⟨134618182328505261668664791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89745454885670174445776527 134618182328505261668664791)
    ·
      refine ⟨201927273492757892502997187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134618182328505261668664791 201927273492757892502997187)
      ·
        refine ⟨302890910239136838754495781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201927273492757892502997187 302890910239136838754495781)
        ·
          refine ⟨56792045669838157266467959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 302890910239136838754495781 56792045669838157266467959)
          ·
            refine ⟨85188068504757235899701939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56792045669838157266467959 85188068504757235899701939)
            ·
              refine ⟨127782102757135853849552909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85188068504757235899701939 127782102757135853849552909)
              ·
                refine ⟨47918288533925945193582341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127782102757135853849552909 47918288533925945193582341)
                ·
                  refine ⟨8984679100111114723796689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47918288533925945193582341 8984679100111114723796689)
                  ·
                    refine ⟨6738509325083336042847517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8984679100111114723796689 6738509325083336042847517)
                    ·
                      refine ⟨2526940996906251016067819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6738509325083336042847517 2526940996906251016067819)
                      ·
                        rfl

theorem cell23_4921200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 3].length) (baseStart_4921200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921200 prefixEnd_4921200 := by exact prefixLift 4921200
  have htrace : WordTrace (prefixWord ++ tailWord_4921200) baseStart_4921200 baseEnd_4921200 := by
    simpa [prefixWord, tailWord_4921200, baseEnd_4921200] using wordTrace_append hprefix tailTrace_4921200
  have hstable : (prefixWord ++ tailWord_4921200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921200).length < 2 ^ (prefixWord ++ tailWord_4921200).sum := by decide
  have hdescent : baseEnd_4921200 < baseStart_4921200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921220 : List Nat := [2, 3, 2, 1, 1, 1, 2, 5, 6]
def baseStart_4921220 : Nat := 118140960795 + 4921220 * 2 ^ 59
def prefixEnd_4921220 : Nat := 4983230072969 + 3 ^ 40 * 4921220 * 2
def baseEnd_4921220 : Nat := 280772362946593437535303

theorem tailTrace_4921220 : CollatzResearch.WordTrace tailWord_4921220 prefixEnd_4921220 280772362946593437535303 := by
  unfold tailWord_4921220
  simp only [CollatzResearch.WordTrace]
  refine ⟨89745819615633946153640557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119661092820845261538187409 89745819615633946153640557)
  ·
    refine ⟨33654682355862729807615209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89745819615633946153640557 33654682355862729807615209)
    ·
      refine ⟨25241011766897047355711407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33654682355862729807615209 25241011766897047355711407)
      ·
        refine ⟨37861517650345571033567111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25241011766897047355711407 37861517650345571033567111)
        ·
          refine ⟨56792276475518356550350667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37861517650345571033567111 56792276475518356550350667)
          ·
            refine ⟨85188414713277534825526001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56792276475518356550350667 85188414713277534825526001)
            ·
              refine ⟨63891311034958151119144501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85188414713277534825526001 63891311034958151119144501)
              ·
                refine ⟨5989810409527326667419797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63891311034958151119144501 5989810409527326667419797)
                ·
                  refine ⟨280772362946593437535303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5989810409527326667419797 280772362946593437535303)
                  ·
                    rfl

theorem cell23_4921220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_4921220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921220 prefixEnd_4921220 := by exact prefixLift 4921220
  have htrace : WordTrace (prefixWord ++ tailWord_4921220) baseStart_4921220 baseEnd_4921220 := by
    simpa [prefixWord, tailWord_4921220, baseEnd_4921220] using wordTrace_append hprefix tailTrace_4921220
  have hstable : (prefixWord ++ tailWord_4921220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921220).length < 2 ^ (prefixWord ++ tailWord_4921220).sum := by decide
  have hdescent : baseEnd_4921220 < baseStart_4921220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921280 : List Nat := [2, 1, 1, 2, 3, 2, 2, 3, 1, 6]
def baseStart_4921280 : Nat := 118140960795 + 4921280 * 2 ^ 59
def prefixEnd_4921280 : Nat := 4983230072969 + 3 ^ 40 * 4921280 * 2
def baseEnd_4921280 : Nat := 842327358452870234355817

theorem tailTrace_4921280 : CollatzResearch.WordTrace tailWord_4921280 prefixEnd_4921280 842327358452870234355817 := by
  unfold tailWord_4921280
  simp only [CollatzResearch.WordTrace]
  refine ⟨89746913805525261277232647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119662551740700348369643529 89746913805525261277232647)
  ·
    refine ⟨134620370708287891915848971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89746913805525261277232647 134620370708287891915848971)
    ·
      refine ⟨201930556062431837873773457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134620370708287891915848971 201930556062431837873773457)
      ·
        refine ⟨151447917046823878405330093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201930556062431837873773457 151447917046823878405330093)
        ·
          refine ⟨56792968892558954401998785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151447917046823878405330093 56792968892558954401998785)
          ·
            refine ⟨42594726669419215801499089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56792968892558954401998785 42594726669419215801499089)
            ·
              refine ⟨31946045002064411851124317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42594726669419215801499089 31946045002064411851124317)
              ·
                refine ⟨11979766875774154444171619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31946045002064411851124317 11979766875774154444171619)
                ·
                  refine ⟨17969650313661231666257429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11979766875774154444171619 17969650313661231666257429)
                  ·
                    refine ⟨842327358452870234355817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17969650313661231666257429 842327358452870234355817)
                    ·
                      rfl

theorem cell23_4921280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 1, 6].length) (baseStart_4921280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921280 prefixEnd_4921280 := by exact prefixLift 4921280
  have htrace : WordTrace (prefixWord ++ tailWord_4921280) baseStart_4921280 baseEnd_4921280 := by
    simpa [prefixWord, tailWord_4921280, baseEnd_4921280] using wordTrace_append hprefix tailTrace_4921280
  have hstable : (prefixWord ++ tailWord_4921280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921280).length < 2 ^ (prefixWord ++ tailWord_4921280).sum := by decide
  have hdescent : baseEnd_4921280 < baseStart_4921280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921290 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 3, 1, 5]
def baseStart_4921290 : Nat := 118140960795 + 4921290 * 2 ^ 59
def prefixEnd_4921290 : Nat := 4983230072969 + 3 ^ 40 * 4921290 * 2
def baseEnd_4921290 : Nat := 2526987210165155663942405

theorem tailTrace_4921290 : CollatzResearch.WordTrace tailWord_4921290 prefixEnd_4921290 2526987210165155663942405 := by
  unfold tailWord_4921290
  simp only [CollatzResearch.WordTrace]
  refine ⟨44873548085253573565582331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119662794894009529508219549 44873548085253573565582331)
  ·
    refine ⟨67310322127880360348373497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44873548085253573565582331 67310322127880360348373497)
    ·
      refine ⟨50482741595910270261280123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67310322127880360348373497 50482741595910270261280123)
      ·
        refine ⟨75724112393865405391920185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50482741595910270261280123 75724112393865405391920185)
        ·
          refine ⟨56793084295399054043940139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75724112393865405391920185 56793084295399054043940139)
          ·
            refine ⟨85189626443098581065910209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56793084295399054043940139 85189626443098581065910209)
            ·
              refine ⟨63892219832323935799432657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85189626443098581065910209 63892219832323935799432657)
              ·
                refine ⟨47919164874242951849574493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63892219832323935799432657 47919164874242951849574493)
                ·
                  refine ⟨17969686827841106943590435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47919164874242951849574493 17969686827841106943590435)
                  ·
                    refine ⟨26954530241761660415385653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17969686827841106943590435 26954530241761660415385653)
                    ·
                      refine ⟨2526987210165155663942405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26954530241761660415385653 2526987210165155663942405)
                      ·
                        rfl

theorem cell23_4921290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_4921290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921290 prefixEnd_4921290 := by exact prefixLift 4921290
  have htrace : WordTrace (prefixWord ++ tailWord_4921290) baseStart_4921290 baseEnd_4921290 := by
    simpa [prefixWord, tailWord_4921290, baseEnd_4921290] using wordTrace_append hprefix tailTrace_4921290
  have hstable : (prefixWord ++ tailWord_4921290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921290).length < 2 ^ (prefixWord ++ tailWord_4921290).sum := by decide
  have hdescent : baseEnd_4921290 < baseStart_4921290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921304 : List Nat := [2, 1, 2, 2, 2, 2, 5, 1, 1, 1, 4]
def baseStart_4921304 : Nat := 118140960795 + 4921304 * 2 ^ 59
def prefixEnd_4921304 : Nat := 4983230072969 + 3 ^ 40 * 4921304 * 2
def baseEnd_4921304 : Nat := 2526994398894318609167341

theorem tailTrace_4921304 : CollatzResearch.WordTrace tailWord_4921304 prefixEnd_4921304 2526994398894318609167341 := by
  unfold tailWord_4921304
  simp only [CollatzResearch.WordTrace]
  refine ⟨89747351481481787326669483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119663135308642383102225977 89747351481481787326669483)
  ·
    refine ⟨134621027222222680990004225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89747351481481787326669483 134621027222222680990004225)
    ·
      refine ⟨100965770416667010742503169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134621027222222680990004225 100965770416667010742503169)
      ·
        refine ⟨75724327812500258056877377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100965770416667010742503169 75724327812500258056877377)
        ·
          refine ⟨56793245859375193542658033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75724327812500258056877377 56793245859375193542658033)
          ·
            refine ⟨42594934394531395156993525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56793245859375193542658033 42594934394531395156993525)
            ·
              refine ⟨3993275099487318295968143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42594934394531395156993525 3993275099487318295968143)
              ·
                refine ⟨5989912649230977443952215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3993275099487318295968143 5989912649230977443952215)
                ·
                  refine ⟨8984868973846466165928323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5989912649230977443952215 8984868973846466165928323)
                  ·
                    refine ⟨13477303460769699248892485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8984868973846466165928323 13477303460769699248892485)
                    ·
                      refine ⟨2526994398894318609167341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13477303460769699248892485 2526994398894318609167341)
                      ·
                        rfl

theorem cell23_4921304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 1, 1, 4].length) (baseStart_4921304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921304 prefixEnd_4921304 := by exact prefixLift 4921304
  have htrace : WordTrace (prefixWord ++ tailWord_4921304) baseStart_4921304 baseEnd_4921304 := by
    simpa [prefixWord, tailWord_4921304, baseEnd_4921304] using wordTrace_append hprefix tailTrace_4921304
  have hstable : (prefixWord ++ tailWord_4921304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921304).length < 2 ^ (prefixWord ++ tailWord_4921304).sum := by decide
  have hdescent : baseEnd_4921304 < baseStart_4921304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921337 : List Nat := [1, 2, 1, 3, 1, 4, 1, 3, 1, 3, 3]
def baseStart_4921337 : Nat := 118140960795 + 4921337 * 2 ^ 59
def prefixEnd_4921337 : Nat := 4983230072969 + 3 ^ 40 * 4921337 * 2
def baseEnd_4921337 : Nat := 2527011343755916980054689

theorem tailTrace_4921337 : CollatzResearch.WordTrace tailWord_4921337 prefixEnd_4921337 2527011343755916980054689 := by
  unfold tailWord_4921337
  simp only [CollatzResearch.WordTrace]
  refine ⟨179495906571844021289290265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119663937714562680859526843 179495906571844021289290265)
  ·
    refine ⟨134621929928883015966967699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179495906571844021289290265 134621929928883015966967699)
    ·
      refine ⟨201932894893324523950451549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134621929928883015966967699 201932894893324523950451549)
      ·
        refine ⟨75724835584996696481419331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201932894893324523950451549 75724835584996696481419331)
        ·
          refine ⟨113587253377495044722128997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75724835584996696481419331 113587253377495044722128997)
          ·
            refine ⟨21297610008280320885399187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113587253377495044722128997 21297610008280320885399187)
            ·
              refine ⟨31946415012420481328098781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21297610008280320885399187 31946415012420481328098781)
              ·
                refine ⟨11979905629657680498037043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31946415012420481328098781 11979905629657680498037043)
                ·
                  refine ⟨17969858444486520747055565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11979905629657680498037043 17969858444486520747055565)
                  ·
                    refine ⟨6738696916682445280145837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17969858444486520747055565 6738696916682445280145837)
                    ·
                      refine ⟨2527011343755916980054689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6738696916682445280145837 2527011343755916980054689)
                      ·
                        rfl

theorem cell23_4921337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_4921337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921337 prefixEnd_4921337 := by exact prefixLift 4921337
  have htrace : WordTrace (prefixWord ++ tailWord_4921337) baseStart_4921337 baseEnd_4921337 := by
    simpa [prefixWord, tailWord_4921337, baseEnd_4921337] using wordTrace_append hprefix tailTrace_4921337
  have hstable : (prefixWord ++ tailWord_4921337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921337).length < 2 ^ (prefixWord ++ tailWord_4921337).sum := by decide
  have hdescent : baseEnd_4921337 < baseStart_4921337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921340 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 2, 7]
def baseStart_4921340 : Nat := 118140960795 + 4921340 * 2 ^ 59
def prefixEnd_4921340 : Nat := 4983230072969 + 3 ^ 40 * 4921340 * 2
def baseEnd_4921340 : Nat := 842337628065960156105725

theorem tailTrace_4921340 : CollatzResearch.WordTrace tailWord_4921340 prefixEnd_4921340 842337628065960156105725 := by
  unfold tailWord_4921340
  simp only [CollatzResearch.WordTrace]
  refine ⟨89748007995416576400824737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119664010660555435201099649 89748007995416576400824737)
  ·
    refine ⟨67311005996562432300618553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89748007995416576400824737 67311005996562432300618553)
    ·
      refine ⟨50483254497421824225463915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67311005996562432300618553 50483254497421824225463915)
      ·
        refine ⟨75724881746132736338195873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50483254497421824225463915 75724881746132736338195873)
        ·
          refine ⟨56793661309599552253646905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75724881746132736338195873 56793661309599552253646905)
          ·
            refine ⟨42595245982199664190235179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56793661309599552253646905 42595245982199664190235179)
            ·
              refine ⟨63892868973299496285352769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42595245982199664190235179 63892868973299496285352769)
              ·
                refine ⟨47919651729974622214014577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63892868973299496285352769 47919651729974622214014577)
                ·
                  refine ⟨35939738797480966660510933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47919651729974622214014577 35939738797480966660510933)
                  ·
                    refine ⟨842337628065960156105725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35939738797480966660510933 842337628065960156105725)
                    ·
                      rfl

theorem cell23_4921340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_4921340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921340 prefixEnd_4921340 := by exact prefixLift 4921340
  have htrace : WordTrace (prefixWord ++ tailWord_4921340) baseStart_4921340 baseEnd_4921340 := by
    simpa [prefixWord, tailWord_4921340, baseEnd_4921340] using wordTrace_append hprefix tailTrace_4921340
  have hstable : (prefixWord ++ tailWord_4921340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921340).length < 2 ^ (prefixWord ++ tailWord_4921340).sum := by decide
  have hdescent : baseEnd_4921340 < baseStart_4921340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921360 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 4]
def baseStart_4921360 : Nat := 118140960795 + 4921360 * 2 ^ 59
def prefixEnd_4921360 : Nat := 4983230072969 + 3 ^ 40 * 4921360 * 2
def baseEnd_4921360 : Nat := 2527023153810970390067083

theorem tailTrace_4921360 : CollatzResearch.WordTrace tailWord_4921360 prefixEnd_4921360 2527023153810970390067083 := by
  unfold tailWord_4921360
  simp only [CollatzResearch.WordTrace]
  refine ⟨89748372725380348108688767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119664496967173797478251689 89748372725380348108688767)
  ·
    refine ⟨134622559088070522163033151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89748372725380348108688767 134622559088070522163033151)
    ·
      refine ⟨201933838632105783244549727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134622559088070522163033151 201933838632105783244549727)
      ·
        refine ⟨302900757948158674866824591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201933838632105783244549727 302900757948158674866824591)
        ·
          refine ⟨454351136922238012300236887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302900757948158674866824591 454351136922238012300236887)
          ·
            refine ⟨681526705383357018450355331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454351136922238012300236887 681526705383357018450355331)
            ·
              refine ⟨1022290058075035527675532997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681526705383357018450355331 1022290058075035527675532997)
              ·
                refine ⟨191679385889069161439162437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1022290058075035527675532997 191679385889069161439162437)
                ·
                  refine ⟨35939884854200467769842957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 191679385889069161439162437 35939884854200467769842957)
                  ·
                    refine ⟨13477456820325175413691109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35939884854200467769842957 13477456820325175413691109)
                    ·
                      refine ⟨2527023153810970390067083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13477456820325175413691109 2527023153810970390067083)
                      ·
                        rfl

theorem cell23_4921360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 4].length) (baseStart_4921360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921360 prefixEnd_4921360 := by exact prefixLift 4921360
  have htrace : WordTrace (prefixWord ++ tailWord_4921360) baseStart_4921360 baseEnd_4921360 := by
    simpa [prefixWord, tailWord_4921360, baseEnd_4921360] using wordTrace_append hprefix tailTrace_4921360
  have hstable : (prefixWord ++ tailWord_4921360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921360).length < 2 ^ (prefixWord ++ tailWord_4921360).sum := by decide
  have hdescent : baseEnd_4921360 < baseStart_4921360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921397 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 2, 4, 3]
def baseStart_4921397 : Nat := 118140960795 + 4921397 * 2 ^ 59
def prefixEnd_4921397 : Nat := 4983230072969 + 3 ^ 40 * 4921397 * 2
def baseEnd_4921397 : Nat := 2527042152595186745304413

theorem tailTrace_4921397 : CollatzResearch.WordTrace tailWord_4921397 prefixEnd_4921397 2527042152595186745304413 := by
  unfold tailWord_4921397
  simp only [CollatzResearch.WordTrace]
  refine ⟨179498094951626651536474445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119665396634417767690982963 179498094951626651536474445)
  ·
    refine ⟨67311785606859994326177917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179498094951626651536474445 67311785606859994326177917)
    ·
      refine ⟨25241919602572497872316719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67311785606859994326177917 25241919602572497872316719)
      ·
        refine ⟨37862879403858746808475079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25241919602572497872316719 37862879403858746808475079)
        ·
          refine ⟨56794319105788120212712619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37862879403858746808475079 56794319105788120212712619)
          ·
            refine ⟨85191478658682180319068929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56794319105788120212712619 85191478658682180319068929)
            ·
              refine ⟨63893608994011635239301697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85191478658682180319068929 63893608994011635239301697)
              ·
                refine ⟨47920206745508726429476273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63893608994011635239301697 47920206745508726429476273)
                ·
                  refine ⟨35940155059131544822107205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47920206745508726429476273 35940155059131544822107205)
                  ·
                    refine ⟨6738779073587164654145101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35940155059131544822107205 6738779073587164654145101)
                    ·
                      refine ⟨2527042152595186745304413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6738779073587164654145101 2527042152595186745304413)
                      ·
                        rfl

theorem cell23_4921397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_4921397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921397 prefixEnd_4921397 := by exact prefixLift 4921397
  have htrace : WordTrace (prefixWord ++ tailWord_4921397) baseStart_4921397 baseEnd_4921397 := by
    simpa [prefixWord, tailWord_4921397, baseEnd_4921397] using wordTrace_append hprefix tailTrace_4921397
  have hstable : (prefixWord ++ tailWord_4921397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921397).length < 2 ^ (prefixWord ++ tailWord_4921397).sum := by decide
  have hdescent : baseEnd_4921397 < baseStart_4921397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921398 : List Nat := [5, 1, 2, 1, 1, 1, 4, 2, 1, 3, 2]
def baseStart_4921398 : Nat := 118140960795 + 4921398 * 2 ^ 59
def prefixEnd_4921398 : Nat := 4983230072969 + 3 ^ 40 * 4921398 * 2
def baseEnd_4921398 : Nat := 2527042666075841241391909

theorem tailTrace_4921398 : CollatzResearch.WordTrace tailWord_4921398 prefixEnd_4921398 2527042666075841241391909 := by
  unfold tailWord_4921398
  simp only [CollatzResearch.WordTrace]
  refine ⟨11218633214038939294203803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119665420949748685804840565 11218633214038939294203803)
  ·
    refine ⟨16827949821058408941305705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11218633214038939294203803 16827949821058408941305705)
    ·
      refine ⟨12620962365793806705979279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16827949821058408941305705 12620962365793806705979279)
      ·
        refine ⟨18931443548690710058968919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12620962365793806705979279 18931443548690710058968919)
        ·
          refine ⟨28397165323036065088453379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18931443548690710058968919 28397165323036065088453379)
          ·
            refine ⟨42595747984554097632680069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28397165323036065088453379 42595747984554097632680069)
            ·
              refine ⟨7986702747103893306127513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42595747984554097632680069 7986702747103893306127513)
              ·
                refine ⟨5990027060327919979595635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7986702747103893306127513 5990027060327919979595635)
                ·
                  refine ⟨8985040590491879969393453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5990027060327919979595635 8985040590491879969393453)
                  ·
                    refine ⟨3369390221434454988522545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8985040590491879969393453 3369390221434454988522545)
                    ·
                      refine ⟨2527042666075841241391909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3369390221434454988522545 2527042666075841241391909)
                      ·
                        rfl

theorem cell23_4921398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_4921398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921398 prefixEnd_4921398 := by exact prefixLift 4921398
  have htrace : WordTrace (prefixWord ++ tailWord_4921398) baseStart_4921398 baseEnd_4921398 := by
    simpa [prefixWord, tailWord_4921398, baseEnd_4921398] using wordTrace_append hprefix tailTrace_4921398
  have hstable : (prefixWord ++ tailWord_4921398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921398).length < 2 ^ (prefixWord ++ tailWord_4921398).sum := by decide
  have hdescent : baseEnd_4921398 < baseStart_4921398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921445 : List Nat := [1, 3, 1, 3, 2, 4, 2, 1, 2, 2, 2]
def baseStart_4921445 : Nat := 118140960795 + 4921445 * 2 ^ 59
def prefixEnd_4921445 : Nat := 4983230072969 + 3 ^ 40 * 4921445 * 2
def baseEnd_4921445 : Nat := 2527066799666602557504193

theorem tailTrace_4921445 : CollatzResearch.WordTrace tailWord_4921445 prefixEnd_4921445 2527066799666602557504193 := by
  unfold tailWord_4921445
  simp only [CollatzResearch.WordTrace]
  refine ⟨179499845655452755734221789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119666563770301837156147859 179499845655452755734221789)
  ·
    refine ⟨67312442120794783400333171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179499845655452755734221789 67312442120794783400333171)
    ·
      refine ⟨100968663181192175100499757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67312442120794783400333171 100968663181192175100499757)
      ·
        refine ⟨37863248692947065662687409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100968663181192175100499757 37863248692947065662687409)
        ·
          refine ⟨28397436519710299247015557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37863248692947065662687409 28397436519710299247015557)
          ·
            refine ⟨5324519347445681108815417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28397436519710299247015557 5324519347445681108815417)
            ·
              refine ⟨3993389510584260831611563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5324519347445681108815417 3993389510584260831611563)
              ·
                refine ⟨5990084265876391247417345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3993389510584260831611563 5990084265876391247417345)
                ·
                  refine ⟨4492563199407293435563009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5990084265876391247417345 4492563199407293435563009)
                  ·
                    refine ⟨3369422399555470076672257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4492563199407293435563009 3369422399555470076672257)
                    ·
                      refine ⟨2527066799666602557504193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3369422399555470076672257 2527066799666602557504193)
                      ·
                        rfl

theorem cell23_4921445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_4921445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921445 prefixEnd_4921445 := by exact prefixLift 4921445
  have htrace : WordTrace (prefixWord ++ tailWord_4921445) baseStart_4921445 baseEnd_4921445 := by
    simpa [prefixWord, tailWord_4921445, baseEnd_4921445] using wordTrace_append hprefix tailTrace_4921445
  have hstable : (prefixWord ++ tailWord_4921445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921445).length < 2 ^ (prefixWord ++ tailWord_4921445).sum := by decide
  have hdescent : baseEnd_4921445 < baseStart_4921445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921447 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 4, 5]
def baseStart_4921447 : Nat := 118140960795 + 4921447 * 2 ^ 59
def prefixEnd_4921447 : Nat := 4983230072969 + 3 ^ 40 * 4921447 * 2
def baseEnd_4921447 : Nat := 842355942209303849893061

theorem tailTrace_4921447 : CollatzResearch.WordTrace tailWord_4921447 prefixEnd_4921447 842355942209303849893061 := by
  unfold tailWord_4921447
  simp only [CollatzResearch.WordTrace]
  refine ⟨179499918601445510075794595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119666612400963673383863063 179499918601445510075794595)
  ·
    refine ⟨269249877902168265113691893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179499918601445510075794595 269249877902168265113691893)
    ·
      refine ⟨25242176053328274854408615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 269249877902168265113691893 25242176053328274854408615)
      ·
        refine ⟨37863264079992412281612923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25242176053328274854408615 37863264079992412281612923)
        ·
          refine ⟨56794896119988618422419385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37863264079992412281612923 56794896119988618422419385)
          ·
            refine ⟨42596172089991463816814539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56794896119988618422419385 42596172089991463816814539)
            ·
              refine ⟨63894258134987195725221809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42596172089991463816814539 63894258134987195725221809)
              ·
                refine ⟨47920693601240396793916357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63894258134987195725221809 47920693601240396793916357)
                ·
                  refine ⟨8985130050232574398859317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47920693601240396793916357 8985130050232574398859317)
                  ·
                    refine ⟨842355942209303849893061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8985130050232574398859317 842355942209303849893061)
                    ·
                      rfl

theorem cell23_4921447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_4921447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921447 prefixEnd_4921447 := by exact prefixLift 4921447
  have htrace : WordTrace (prefixWord ++ tailWord_4921447) baseStart_4921447 baseEnd_4921447 := by
    simpa [prefixWord, tailWord_4921447, baseEnd_4921447] using wordTrace_append hprefix tailTrace_4921447
  have hstable : (prefixWord ++ tailWord_4921447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921447).length < 2 ^ (prefixWord ++ tailWord_4921447).sum := by decide
  have hdescent : baseEnd_4921447 < baseStart_4921447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921501 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 2, 4, 2]
def baseStart_4921501 : Nat := 118140960795 + 4921501 * 2 ^ 59
def prefixEnd_4921501 : Nat := 4983230072969 + 3 ^ 40 * 4921501 * 2
def baseEnd_4921501 : Nat := 2527095554583254338403935

theorem tailTrace_4921501 : CollatzResearch.WordTrace tailWord_4921501 prefixEnd_4921501 2527095554583254338403935 := by
  unfold tailWord_4921501
  simp only [CollatzResearch.WordTrace]
  refine ⟨179501888143249877298260357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119667925428833251532173571 179501888143249877298260357)
  ·
    refine ⟨33656604026859351993423817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179501888143249877298260357 33656604026859351993423817)
    ·
      refine ⟨25242453020144513995067863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33656604026859351993423817 25242453020144513995067863)
      ·
        refine ⟨37863679530216770992601795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25242453020144513995067863 37863679530216770992601795)
        ·
          refine ⟨56795519295325156488902693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37863679530216770992601795 56795519295325156488902693)
          ·
            refine ⟨10649159867873466841669255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56795519295325156488902693 10649159867873466841669255)
            ·
              refine ⟨15973739801810200262503883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10649159867873466841669255 15973739801810200262503883)
              ·
                refine ⟨23960609702715300393755825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15973739801810200262503883 23960609702715300393755825)
                ·
                  refine ⟨17970457277036475295316869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23960609702715300393755825 17970457277036475295316869)
                  ·
                    refine ⟨3369460739444339117871913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17970457277036475295316869 3369460739444339117871913)
                    ·
                      refine ⟨2527095554583254338403935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3369460739444339117871913 2527095554583254338403935)
                      ·
                        rfl

theorem cell23_4921501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_4921501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921501 prefixEnd_4921501 := by exact prefixLift 4921501
  have htrace : WordTrace (prefixWord ++ tailWord_4921501) baseStart_4921501 baseEnd_4921501 := by
    simpa [prefixWord, tailWord_4921501, baseEnd_4921501] using wordTrace_append hprefix tailTrace_4921501
  have hstable : (prefixWord ++ tailWord_4921501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921501).length < 2 ^ (prefixWord ++ tailWord_4921501).sum := by decide
  have hdescent : baseEnd_4921501 < baseStart_4921501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921518 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_4921518 : Nat := 118140960795 + 4921518 * 2 ^ 59
def prefixEnd_4921518 : Nat := 4983230072969 + 3 ^ 40 * 4921518 * 2
def baseEnd_4921518 : Nat := 2527104283754380771891357

theorem tailTrace_4921518 : CollatzResearch.WordTrace tailWord_4921518 prefixEnd_4921518 2527104283754380771891357 := by
  unfold tailWord_4921518
  simp only [CollatzResearch.WordTrace]
  refine ⟨22437813523023536150203651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119668338789458859467752805 22437813523023536150203651)
  ·
    refine ⟨33656720284535304225305477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22437813523023536150203651 33656720284535304225305477)
    ·
      refine ⟨6310635053350369542244777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33656720284535304225305477 6310635053350369542244777)
      ·
        refine ⟨4732976290012777156683583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6310635053350369542244777 4732976290012777156683583)
        ·
          refine ⟨7099464435019165735025375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4732976290012777156683583 7099464435019165735025375)
          ·
            refine ⟨10649196652528748602538063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7099464435019165735025375 10649196652528748602538063)
            ·
              refine ⟨15973794978793122903807095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10649196652528748602538063 15973794978793122903807095)
              ·
                refine ⟨23960692468189684355710643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15973794978793122903807095 23960692468189684355710643)
                ·
                  refine ⟨35941038702284526533565965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23960692468189684355710643 35941038702284526533565965)
                  ·
                    refine ⟨13477889513356697450087237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35941038702284526533565965 13477889513356697450087237)
                    ·
                      refine ⟨2527104283754380771891357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13477889513356697450087237 2527104283754380771891357)
                      ·
                        rfl

theorem cell23_4921518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_4921518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921518 prefixEnd_4921518 := by exact prefixLift 4921518
  have htrace : WordTrace (prefixWord ++ tailWord_4921518) baseStart_4921518 baseEnd_4921518 := by
    simpa [prefixWord, tailWord_4921518, baseEnd_4921518] using wordTrace_append hprefix tailTrace_4921518
  have hstable : (prefixWord ++ tailWord_4921518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921518).length < 2 ^ (prefixWord ++ tailWord_4921518).sum := by decide
  have hdescent : baseEnd_4921518 < baseStart_4921518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921521 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 1, 4, 3]
def baseStart_4921521 : Nat := 118140960795 + 4921521 * 2 ^ 59
def prefixEnd_4921521 : Nat := 4983230072969 + 3 ^ 40 * 4921521 * 2
def baseEnd_4921521 : Nat := 2527105824196344260153843

theorem tailTrace_4921521 : CollatzResearch.WordTrace tailWord_4921521 prefixEnd_4921521 2527105824196344260153843 := by
  unfold tailWord_4921521
  simp only [CollatzResearch.WordTrace]
  refine ⟨179502617603177420713988417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119668411735451613809325611 179502617603177420713988417)
  ·
    refine ⟨134626963202383065535491313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179502617603177420713988417 134626963202383065535491313)
    ·
      refine ⟨100970222401787299151618485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134626963202383065535491313 100970222401787299151618485)
      ·
        refine ⟨9465958350167559295464233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100970222401787299151618485 9465958350167559295464233)
        ·
          refine ⟨7099468762625669471598175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9465958350167559295464233 7099468762625669471598175)
          ·
            refine ⟨10649203143938504207397263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7099468762625669471598175 10649203143938504207397263)
            ·
              refine ⟨15973804715907756311095895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10649203143938504207397263 15973804715907756311095895)
              ·
                refine ⟨23960707073861634466643843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15973804715907756311095895 23960707073861634466643843)
                ·
                  refine ⟨35941060610792451699965765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23960707073861634466643843 35941060610792451699965765)
                  ·
                    refine ⟨6738948864523584693743581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35941060610792451699965765 6738948864523584693743581)
                    ·
                      refine ⟨2527105824196344260153843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6738948864523584693743581 2527105824196344260153843)
                      ·
                        rfl

theorem cell23_4921521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_4921521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921521 prefixEnd_4921521 := by exact prefixLift 4921521
  have htrace : WordTrace (prefixWord ++ tailWord_4921521) baseStart_4921521 baseEnd_4921521 := by
    simpa [prefixWord, tailWord_4921521, baseEnd_4921521] using wordTrace_append hprefix tailTrace_4921521
  have hstable : (prefixWord ++ tailWord_4921521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921521).length < 2 ^ (prefixWord ++ tailWord_4921521).sum := by decide
  have hdescent : baseEnd_4921521 < baseStart_4921521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921551 : List Nat := [1, 1, 2, 1, 1, 3, 6, 1, 3, 1, 3]
def baseStart_4921551 : Nat := 118140960795 + 4921551 * 2 ^ 59
def prefixEnd_4921551 : Nat := 4983230072969 + 3 ^ 40 * 4921551 * 2
def baseEnd_4921551 : Nat := 2527121228615979142778705

theorem tailTrace_4921551 : CollatzResearch.WordTrace tailWord_4921551 prefixEnd_4921551 2527121228615979142778705 := by
  unfold tailWord_4921551
  simp only [CollatzResearch.WordTrace]
  refine ⟨179503711793068735837580507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119669141195379157225053671 179503711793068735837580507)
  ·
    refine ⟨269255567689603103756370761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179503711793068735837580507 269255567689603103756370761)
    ·
      refine ⟨201941675767202327817278071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269255567689603103756370761 201941675767202327817278071)
      ·
        refine ⟨302912513650803491725917107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201941675767202327817278071 302912513650803491725917107)
        ·
          refine ⟨454368770476205237588875661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302912513650803491725917107 454368770476205237588875661)
          ·
            refine ⟨170388288928576964095828373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 454368770476205237588875661 170388288928576964095828373)
            ·
              refine ⟨7986951043527045191991955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 170388288928576964095828373 7986951043527045191991955)
              ·
                refine ⟨11980426565290567787987933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7986951043527045191991955 11980426565290567787987933)
                ·
                  refine ⟨4492659961983962920495475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11980426565290567787987933 4492659961983962920495475)
                  ·
                    refine ⟨6738989942975944380743213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4492659961983962920495475 6738989942975944380743213)
                    ·
                      refine ⟨2527121228615979142778705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6738989942975944380743213 2527121228615979142778705)
                      ·
                        rfl

theorem cell23_4921551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 1, 3].length) (baseStart_4921551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921551 prefixEnd_4921551 := by exact prefixLift 4921551
  have htrace : WordTrace (prefixWord ++ tailWord_4921551) baseStart_4921551 baseEnd_4921551 := by
    simpa [prefixWord, tailWord_4921551, baseEnd_4921551] using wordTrace_append hprefix tailTrace_4921551
  have hstable : (prefixWord ++ tailWord_4921551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921551).length < 2 ^ (prefixWord ++ tailWord_4921551).sum := by decide
  have hdescent : baseEnd_4921551 < baseStart_4921551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921594 : List Nat := [3, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5]
def baseStart_4921594 : Nat := 118140960795 + 4921594 * 2 ^ 59
def prefixEnd_4921594 : Nat := 4983230072969 + 3 ^ 40 * 4921594 * 2
def baseEnd_4921594 : Nat := 2527143308284122474541007

theorem tailTrace_4921594 : CollatzResearch.WordTrace tailWord_4921594 prefixEnd_4921594 2527143308284122474541007 := by
  unfold tailWord_4921594
  simp only [CollatzResearch.WordTrace]
  refine ⟨44876320032978238545348959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119670186754608636120930557 44876320032978238545348959)
  ·
    refine ⟨67314480049467357818023439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44876320032978238545348959 67314480049467357818023439)
    ·
      refine ⟨100971720074201036727035159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67314480049467357818023439 100971720074201036727035159)
      ·
        refine ⟨151457580111301555090552739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100971720074201036727035159 151457580111301555090552739)
        ·
          refine ⟨227186370166952332635829109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151457580111301555090552739 227186370166952332635829109)
          ·
            refine ⟨21298722203151781184608979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 227186370166952332635829109 21298722203151781184608979)
            ·
              refine ⟨31948083304727671776913469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21298722203151781184608979 31948083304727671776913469)
              ·
                refine ⟨11980531239272876916342551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31948083304727671776913469 11980531239272876916342551)
                ·
                  refine ⟨17970796858909315374513827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11980531239272876916342551 17970796858909315374513827)
                  ·
                    refine ⟨26956195288363973061770741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17970796858909315374513827 26956195288363973061770741)
                    ·
                      refine ⟨2527143308284122474541007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26956195288363973061770741 2527143308284122474541007)
                      ·
                        rfl

theorem cell23_4921594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_4921594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921594 prefixEnd_4921594 := by exact prefixLift 4921594
  have htrace : WordTrace (prefixWord ++ tailWord_4921594) baseStart_4921594 baseEnd_4921594 := by
    simpa [prefixWord, tailWord_4921594, baseEnd_4921594] using wordTrace_append hprefix tailTrace_4921594
  have hstable : (prefixWord ++ tailWord_4921594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921594).length < 2 ^ (prefixWord ++ tailWord_4921594).sum := by decide
  have hdescent : baseEnd_4921594 < baseStart_4921594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921601 : List Nat := [1, 2, 4, 1, 1, 2, 2, 4, 2, 4]
def baseStart_4921601 : Nat := 118140960795 + 4921601 * 2 ^ 59
def prefixEnd_4921601 : Nat := 4983230072969 + 3 ^ 40 * 4921601 * 2
def baseEnd_4921601 : Nat := 842382300882901315717825

theorem tailTrace_4921601 : CollatzResearch.WordTrace tailWord_4921601 prefixEnd_4921601 842382300882901315717825 := by
  unfold tailWord_4921601
  simp only [CollatzResearch.WordTrace]
  refine ⟨179505535442887594376900657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119670356961925062917933771 179505535442887594376900657)
  ·
    refine ⟨134629151582165695782675493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179505535442887594376900657 134629151582165695782675493)
    ·
      refine ⟨25242965921656067959251655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134629151582165695782675493 25242965921656067959251655)
      ·
        refine ⟨37864448882484101938877483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25242965921656067959251655 37864448882484101938877483)
        ·
          refine ⟨56796673323726152908316225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37864448882484101938877483 56796673323726152908316225)
          ·
            refine ⟨42597504992794614681237169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56796673323726152908316225 42597504992794614681237169)
            ·
              refine ⟨31948128744595961010927877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42597504992794614681237169 31948128744595961010927877)
              ·
                refine ⟨5990274139611742689548977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31948128744595961010927877 5990274139611742689548977)
                ·
                  refine ⟨4492705604708807017161733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5990274139611742689548977 4492705604708807017161733)
                  ·
                    refine ⟨842382300882901315717825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4492705604708807017161733 842382300882901315717825)
                    ·
                      rfl

theorem cell23_4921601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_4921601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921601 prefixEnd_4921601 := by exact prefixLift 4921601
  have htrace : WordTrace (prefixWord ++ tailWord_4921601) baseStart_4921601 baseEnd_4921601 := by
    simpa [prefixWord, tailWord_4921601, baseEnd_4921601] using wordTrace_append hprefix tailTrace_4921601
  have hstable : (prefixWord ++ tailWord_4921601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921601).length < 2 ^ (prefixWord ++ tailWord_4921601).sum := by decide
  have hdescent : baseEnd_4921601 < baseStart_4921601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921614 : List Nat := [4, 1, 1, 2, 1, 2, 4, 8]
def baseStart_4921614 : Nat := 118140960795 + 4921614 * 2 ^ 59
def prefixEnd_4921614 : Nat := 4983230072969 + 3 ^ 40 * 4921614 * 2
def baseEnd_4921614 : Nat := 93598280662859718381145

theorem tailTrace_4921614 : CollatzResearch.WordTrace tailWord_4921614 prefixEnd_4921614 93598280662859718381145 := by
  unfold tailWord_4921614
  simp only [CollatzResearch.WordTrace]
  refine ⟨22438251198980062199640487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119670673061226998398082597 22438251198980062199640487)
  ·
    refine ⟨33657376798470093299460731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22438251198980062199640487 33657376798470093299460731)
    ·
      refine ⟨50486065197705139949191097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33657376798470093299460731 50486065197705139949191097)
      ·
        refine ⟨37864548898278854961893323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50486065197705139949191097 37864548898278854961893323)
        ·
          refine ⟨56796823347418282442839985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37864548898278854961893323 56796823347418282442839985)
          ·
            refine ⟨42597617510563711832129989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56796823347418282442839985 42597617510563711832129989)
            ·
              refine ⟨7987053283230695968524373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42597617510563711832129989 7987053283230695968524373)
              ·
                refine ⟨93598280662859718381145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7987053283230695968524373 93598280662859718381145)
                ·
                  rfl

theorem cell23_4921614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 8].length) (baseStart_4921614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921614 prefixEnd_4921614 := by exact prefixLift 4921614
  have htrace : WordTrace (prefixWord ++ tailWord_4921614) baseStart_4921614 baseEnd_4921614 := by
    simpa [prefixWord, tailWord_4921614, baseEnd_4921614] using wordTrace_append hprefix tailTrace_4921614
  have hstable : (prefixWord ++ tailWord_4921614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921614).length < 2 ^ (prefixWord ++ tailWord_4921614).sum := by decide
  have hdescent : baseEnd_4921614 < baseStart_4921614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921645 : List Nat := [1, 5, 3, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_4921645 : Nat := 118140960795 + 4921645 * 2 ^ 59
def prefixEnd_4921645 : Nat := 4983230072969 + 3 ^ 40 * 4921645 * 2
def baseEnd_4921645 : Nat := 2527169495797501775003273

theorem tailTrace_4921645 : CollatzResearch.WordTrace tailWord_4921645 prefixEnd_4921645 2527169495797501775003273 := by
  unfold tailWord_4921645
  simp only [CollatzResearch.WordTrace]
  refine ⟨179507140254728189891502389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119671426836485459927668259 179507140254728189891502389)
  ·
    refine ⟨16828794398880767802328349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 179507140254728189891502389 16828794398880767802328349)
    ·
      refine ⟨6310797899580287925873131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16828794398880767802328349 6310797899580287925873131)
      ·
        refine ⟨9466196849370431888809697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6310797899580287925873131 9466196849370431888809697)
        ·
          refine ⟨7099647637027823916607273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9466196849370431888809697 7099647637027823916607273)
          ·
            refine ⟨5324735727770867937455455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7099647637027823916607273 5324735727770867937455455)
            ·
              refine ⟨7987103591656301906183183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5324735727770867937455455 7987103591656301906183183)
              ·
                refine ⟨11980655387484452859274775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7987103591656301906183183 11980655387484452859274775)
                ·
                  refine ⟨17970983081226679288912163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11980655387484452859274775 17970983081226679288912163)
                  ·
                    refine ⟨26956474621840018933368245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17970983081226679288912163 26956474621840018933368245)
                    ·
                      refine ⟨2527169495797501775003273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26956474621840018933368245 2527169495797501775003273)
                      ·
                        rfl

theorem cell23_4921645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_4921645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921645 prefixEnd_4921645 := by exact prefixLift 4921645
  have htrace : WordTrace (prefixWord ++ tailWord_4921645) baseStart_4921645 baseEnd_4921645 := by
    simpa [prefixWord, tailWord_4921645, baseEnd_4921645] using wordTrace_append hprefix tailTrace_4921645
  have hstable : (prefixWord ++ tailWord_4921645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921645).length < 2 ^ (prefixWord ++ tailWord_4921645).sum := by decide
  have hdescent : baseEnd_4921645 < baseStart_4921645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921658 : List Nat := [3, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3]
def baseStart_4921658 : Nat := 118140960795 + 4921658 * 2 ^ 59
def prefixEnd_4921658 : Nat := 4983230072969 + 3 ^ 40 * 4921658 * 2
def baseEnd_4921658 : Nat := 2527176171046010224140713

theorem tailTrace_4921658 : CollatzResearch.WordTrace tailWord_4921658 prefixEnd_4921658 2527176171046010224140713 := by
  unfold tailWord_4921658
  simp only [CollatzResearch.WordTrace]
  refine ⟨44876903600920273277931407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119671742935787395407817085 44876903600920273277931407)
  ·
    refine ⟨67315355401380409916897111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44876903600920273277931407 67315355401380409916897111)
    ·
      refine ⟨100973033102070614875345667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67315355401380409916897111 100973033102070614875345667)
      ·
        refine ⟨151459549653105922313018501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100973033102070614875345667 151459549653105922313018501)
        ·
          refine ⟨28398665559957360433690969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151459549653105922313018501 28398665559957360433690969)
          ·
            refine ⟨21298999169968020325268227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28398665559957360433690969 21298999169968020325268227)
            ·
              refine ⟨31948498754952030487902341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21298999169968020325268227 31948498754952030487902341)
              ·
                refine ⟨5990343516553505716481689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31948498754952030487902341 5990343516553505716481689)
                ·
                  refine ⟨4492757637415129287361267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5990343516553505716481689 4492757637415129287361267)
                  ·
                    refine ⟨6739136456122693931041901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4492757637415129287361267 6739136456122693931041901)
                    ·
                      refine ⟨2527176171046010224140713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6739136456122693931041901 2527176171046010224140713)
                      ·
                        rfl

theorem cell23_4921658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3].length) (baseStart_4921658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921658 prefixEnd_4921658 := by exact prefixLift 4921658
  have htrace : WordTrace (prefixWord ++ tailWord_4921658) baseStart_4921658 baseEnd_4921658 := by
    simpa [prefixWord, tailWord_4921658, baseEnd_4921658] using wordTrace_append hprefix tailTrace_4921658
  have hstable : (prefixWord ++ tailWord_4921658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921658).length < 2 ^ (prefixWord ++ tailWord_4921658).sum := by decide
  have hdescent : baseEnd_4921658 < baseStart_4921658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921732 : List Nat := [2, 3, 2, 1, 1, 2, 5, 1, 2, 2, 2]
def baseStart_4921732 : Nat := 118140960795 + 4921732 * 2 ^ 59
def prefixEnd_4921732 : Nat := 4983230072969 + 3 ^ 40 * 4921732 * 2
def baseEnd_4921732 : Nat := 2527214168614442934615373

theorem tailTrace_4921732 : CollatzResearch.WordTrace tailWord_4921732 prefixEnd_4921732 2527214168614442934615373 := by
  unfold tailWord_4921732
  simp only [CollatzResearch.WordTrace]
  refine ⟨89755156702706501874959725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119673542270275335833279633 89755156702706501874959725)
  ·
    refine ⟨33658183763514938203109897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89755156702706501874959725 33658183763514938203109897)
    ·
      refine ⟨25243637822636203652332423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33658183763514938203109897 25243637822636203652332423)
      ·
        refine ⟨37865456733954305478498635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25243637822636203652332423 37865456733954305478498635)
        ·
          refine ⟨56798185100931458217747953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37865456733954305478498635 56798185100931458217747953)
          ·
            refine ⟨42598638825698593663310965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56798185100931458217747953 42598638825698593663310965)
            ·
              refine ⟨3993622389909243155935403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42598638825698593663310965 3993622389909243155935403)
              ·
                refine ⟨5990433584863864733903105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3993622389909243155935403 5990433584863864733903105)
                ·
                  refine ⟨4492825188647898550427329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5990433584863864733903105 4492825188647898550427329)
                  ·
                    refine ⟨3369618891485923912820497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4492825188647898550427329 3369618891485923912820497)
                    ·
                      refine ⟨2527214168614442934615373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3369618891485923912820497 2527214168614442934615373)
                      ·
                        rfl

theorem cell23_4921732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_4921732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921732 prefixEnd_4921732 := by exact prefixLift 4921732
  have htrace : WordTrace (prefixWord ++ tailWord_4921732) baseStart_4921732 baseEnd_4921732 := by
    simpa [prefixWord, tailWord_4921732, baseEnd_4921732] using wordTrace_append hprefix tailTrace_4921732
  have hstable : (prefixWord ++ tailWord_4921732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921732).length < 2 ^ (prefixWord ++ tailWord_4921732).sum := by decide
  have hdescent : baseEnd_4921732 < baseStart_4921732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921768 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 4, 5]
def baseStart_4921768 : Nat := 118140960795 + 4921768 * 2 ^ 59
def prefixEnd_4921768 : Nat := 4983230072969 + 3 ^ 40 * 4921768 * 2
def baseEnd_4921768 : Nat := 842410884639334931255069

theorem tailTrace_4921768 : CollatzResearch.WordTrace tailWord_4921768 prefixEnd_4921768 842410884639334931255069 := by
  unfold tailWord_4921768
  simp only [CollatzResearch.WordTrace]
  refine ⟨89755813216641290949114979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119674417622188387932153305 89755813216641290949114979)
  ·
    refine ⟨134633719824961936423672469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89755813216641290949114979 134633719824961936423672469)
    ·
      refine ⟨6310955616795090769859647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 134633719824961936423672469 6310955616795090769859647)
      ·
        refine ⟨9466433425192636154789471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6310955616795090769859647 9466433425192636154789471)
        ·
          refine ⟨14199650137788954232184207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9466433425192636154789471 14199650137788954232184207)
          ·
            refine ⟨21299475206683431348276311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14199650137788954232184207 21299475206683431348276311)
            ·
              refine ⟨31949212810025147022414467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21299475206683431348276311 31949212810025147022414467)
              ·
                refine ⟨47923819215037720533621701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31949212810025147022414467 47923819215037720533621701)
                ·
                  refine ⟨8985716102819572600054069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47923819215037720533621701 8985716102819572600054069)
                  ·
                    refine ⟨842410884639334931255069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8985716102819572600054069 842410884639334931255069)
                    ·
                      rfl

theorem cell23_4921768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_4921768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921768 prefixEnd_4921768 := by exact prefixLift 4921768
  have htrace : WordTrace (prefixWord ++ tailWord_4921768) baseStart_4921768 baseEnd_4921768 := by
    simpa [prefixWord, tailWord_4921768, baseEnd_4921768] using wordTrace_append hprefix tailTrace_4921768
  have hstable : (prefixWord ++ tailWord_4921768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921768).length < 2 ^ (prefixWord ++ tailWord_4921768).sum := by decide
  have hdescent : baseEnd_4921768 < baseStart_4921768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921831 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_4921831 : Nat := 118140960795 + 4921831 * 2 ^ 59
def prefixEnd_4921831 : Nat := 4983230072969 + 3 ^ 40 * 4921831 * 2
def baseEnd_4921831 : Nat := 2527265003199238047277417

theorem tailTrace_4921831 : CollatzResearch.WordTrace tailWord_4921831 prefixEnd_4921831 2527265003199238047277417 := by
  unfold tailWord_4921831
  simp only [CollatzResearch.WordTrace]
  refine ⟨179513924232054343657773347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119675949488036229105182231 179513924232054343657773347)
  ·
    refine ⟨269270886348081515486660021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179513924232054343657773347 269270886348081515486660021)
    ·
      refine ⟨25244145595132642076874377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 269270886348081515486660021 25244145595132642076874377)
      ·
        refine ⟨18933109196349481557655783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25244145595132642076874377 18933109196349481557655783)
        ·
          refine ⟨28399663794524222336483675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18933109196349481557655783 28399663794524222336483675)
          ·
            refine ⟨42599495691786333504725513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28399663794524222336483675 42599495691786333504725513)
            ·
              refine ⟨31949621768839750128544135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42599495691786333504725513 31949621768839750128544135)
              ·
                refine ⟨47924432653259625192816203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31949621768839750128544135 47924432653259625192816203)
                ·
                  refine ⟨71886648979889437789224305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47924432653259625192816203 71886648979889437789224305)
                  ·
                    refine ⟨53914986734917078341918229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71886648979889437789224305 53914986734917078341918229)
                    ·
                      refine ⟨2527265003199238047277417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53914986734917078341918229 2527265003199238047277417)
                      ·
                        rfl

theorem cell23_4921831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_4921831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921831 prefixEnd_4921831 := by exact prefixLift 4921831
  have htrace : WordTrace (prefixWord ++ tailWord_4921831) baseStart_4921831 baseEnd_4921831 := by
    simpa [prefixWord, tailWord_4921831, baseEnd_4921831] using wordTrace_append hprefix tailTrace_4921831
  have hstable : (prefixWord ++ tailWord_4921831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921831).length < 2 ^ (prefixWord ++ tailWord_4921831).sum := by decide
  have hdescent : baseEnd_4921831 < baseStart_4921831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921832 : List Nat := [2, 1, 4, 1, 1, 3, 4, 2, 1, 4]
def baseStart_4921832 : Nat := 118140960795 + 4921832 * 2 ^ 59
def prefixEnd_4921832 : Nat := 4983230072969 + 3 ^ 40 * 4921832 * 2
def baseEnd_4921832 : Nat := 842421838893297514454971

theorem tailTrace_4921832 : CollatzResearch.WordTrace tailWord_4921832 prefixEnd_4921832 842421838893297514454971 := by
  unfold tailWord_4921832
  simp only [CollatzResearch.WordTrace]
  refine ⟨89756980352525360414279875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119675973803367147219039833 89756980352525360414279875)
  ·
    refine ⟨134635470528788040621419813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89756980352525360414279875 134635470528788040621419813)
    ·
      refine ⟨25244150724147757616516215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134635470528788040621419813 25244150724147757616516215)
      ·
        refine ⟨37866226086221636424774323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25244150724147757616516215 37866226086221636424774323)
        ·
          refine ⟨56799339129332454637161485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37866226086221636424774323 56799339129332454637161485)
          ·
            refine ⟨21299752173499670488935557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56799339129332454637161485 21299752173499670488935557)
            ·
              refine ⟨3993703532531188216675417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21299752173499670488935557 3993703532531188216675417)
              ·
                refine ⟨2995277649398391162506563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3993703532531188216675417 2995277649398391162506563)
                ·
                  refine ⟨4492916474097586743759845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2995277649398391162506563 4492916474097586743759845)
                  ·
                    refine ⟨842421838893297514454971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4492916474097586743759845 842421838893297514454971)
                    ·
                      rfl

theorem cell23_4921832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_4921832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921832 prefixEnd_4921832 := by exact prefixLift 4921832
  have htrace : WordTrace (prefixWord ++ tailWord_4921832) baseStart_4921832 baseEnd_4921832 := by
    simpa [prefixWord, tailWord_4921832, baseEnd_4921832] using wordTrace_append hprefix tailTrace_4921832
  have hstable : (prefixWord ++ tailWord_4921832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921832).length < 2 ^ (prefixWord ++ tailWord_4921832).sum := by decide
  have hdescent : baseEnd_4921832 < baseStart_4921832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921841 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 5, 5]
def baseStart_4921841 : Nat := 118140960795 + 4921841 * 2 ^ 59
def prefixEnd_4921841 : Nat := 4983230072969 + 3 ^ 40 * 4921841 * 2
def baseEnd_4921841 : Nat := 842423379335261002717457

theorem tailTrace_4921841 : CollatzResearch.WordTrace tailWord_4921841 prefixEnd_4921841 842423379335261002717457 := by
  unfold tailWord_4921841
  simp only [CollatzResearch.WordTrace]
  refine ⟨179514288962018115365637377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119676192641345410243758251 179514288962018115365637377)
  ·
    refine ⟨134635716721513586524228033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179514288962018115365637377 134635716721513586524228033)
    ·
      refine ⟨100976787541135189893171025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134635716721513586524228033 100976787541135189893171025)
      ·
        refine ⟨75732590655851392419878269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100976787541135189893171025 75732590655851392419878269)
        ·
          refine ⟨28399721495944272157454351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75732590655851392419878269 28399721495944272157454351)
          ·
            refine ⟨42599582243916408236181527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28399721495944272157454351 42599582243916408236181527)
            ·
              refine ⟨63899373365874612354272291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42599582243916408236181527 63899373365874612354272291)
              ·
                refine ⟨95849060048811918531408437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63899373365874612354272291 95849060048811918531408437)
                ·
                  refine ⟨8985849379576117362319541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95849060048811918531408437 8985849379576117362319541)
                  ·
                    refine ⟨842423379335261002717457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8985849379576117362319541 842423379335261002717457)
                    ·
                      rfl

theorem cell23_4921841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_4921841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921841 prefixEnd_4921841 := by exact prefixLift 4921841
  have htrace : WordTrace (prefixWord ++ tailWord_4921841) baseStart_4921841 baseEnd_4921841 := by
    simpa [prefixWord, tailWord_4921841, baseEnd_4921841] using wordTrace_append hprefix tailTrace_4921841
  have hstable : (prefixWord ++ tailWord_4921841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921841).length < 2 ^ (prefixWord ++ tailWord_4921841).sum := by decide
  have hdescent : baseEnd_4921841 < baseStart_4921841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921848 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 1, 5, 2]
def baseStart_4921848 : Nat := 118140960795 + 4921848 * 2 ^ 59
def prefixEnd_4921848 : Nat := 4983230072969 + 3 ^ 40 * 4921848 * 2
def baseEnd_4921848 : Nat := 2527273732370364480764839

theorem tailTrace_4921848 : CollatzResearch.WordTrace tailWord_4921848 prefixEnd_4921848 2527273732370364480764839 := by
  unfold tailWord_4921848
  simp only [CollatzResearch.WordTrace]
  refine ⟨89757272136496377780571099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119676362848661837040761465 89757272136496377780571099)
  ·
    refine ⟨134635908204744566670856649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89757272136496377780571099 134635908204744566670856649)
    ·
      refine ⟨100976931153558425003142487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134635908204744566670856649 100976931153558425003142487)
      ·
        refine ⟨151465396730337637504713731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100976931153558425003142487 151465396730337637504713731)
        ·
          refine ⟨227198095095506456257070597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151465396730337637504713731 227198095095506456257070597)
          ·
            refine ⟨42599642830407460548200737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 227198095095506456257070597 42599642830407460548200737)
            ·
              refine ⟨31949732122805595411150553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42599642830407460548200737 31949732122805595411150553)
              ·
                refine ⟨23962299092104196558362915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31949732122805595411150553 23962299092104196558362915)
                ·
                  refine ⟨35943448638156294837544373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23962299092104196558362915 35943448638156294837544373)
                  ·
                    refine ⟨3369698309827152641019785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35943448638156294837544373 3369698309827152641019785)
                    ·
                      refine ⟨2527273732370364480764839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3369698309827152641019785 2527273732370364480764839)
                      ·
                        rfl

theorem cell23_4921848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 1, 5, 2].length) (baseStart_4921848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921848 prefixEnd_4921848 := by exact prefixLift 4921848
  have htrace : WordTrace (prefixWord ++ tailWord_4921848) baseStart_4921848 baseEnd_4921848 := by
    simpa [prefixWord, tailWord_4921848, baseEnd_4921848] using wordTrace_append hprefix tailTrace_4921848
  have hstable : (prefixWord ++ tailWord_4921848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921848).length < 2 ^ (prefixWord ++ tailWord_4921848).sum := by decide
  have hdescent : baseEnd_4921848 < baseStart_4921848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921898 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_4921898 : Nat := 118140960795 + 4921898 * 2 ^ 59
def prefixEnd_4921898 : Nat := 4983230072969 + 3 ^ 40 * 4921898 * 2
def baseEnd_4921898 : Nat := 2527299406403089285139609

theorem tailTrace_4921898 : CollatzResearch.WordTrace tailWord_4921898 prefixEnd_4921898 2527299406403089285139609 := by
  unfold tailWord_4921898
  simp only [CollatzResearch.WordTrace]
  refine ⟨44879091980702903525115587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119677578615207742733641565 44879091980702903525115587)
  ·
    refine ⟨67318637971054355287673381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44879091980702903525115587 67318637971054355287673381)
    ·
      refine ⟨12622244619572691616438759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67318637971054355287673381 12622244619572691616438759)
      ·
        refine ⟨18933366929359037424658139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12622244619572691616438759 18933366929359037424658139)
        ·
          refine ⟨28400050394038556136987209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18933366929359037424658139 28400050394038556136987209)
          ·
            refine ⟨21300037795528917102740407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28400050394038556136987209 21300037795528917102740407)
            ·
              refine ⟨31950056693293375654110611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21300037795528917102740407 31950056693293375654110611)
              ·
                refine ⟨47925085039940063481165917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31950056693293375654110611 47925085039940063481165917)
                ·
                  refine ⟨17971906889977523805437219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47925085039940063481165917 17971906889977523805437219)
                  ·
                    refine ⟨26957860334966285708155829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17971906889977523805437219 26957860334966285708155829)
                    ·
                      refine ⟨2527299406403089285139609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26957860334966285708155829 2527299406403089285139609)
                      ·
                        rfl

theorem cell23_4921898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_4921898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921898 prefixEnd_4921898 := by exact prefixLift 4921898
  have htrace : WordTrace (prefixWord ++ tailWord_4921898) baseStart_4921898 baseEnd_4921898 := by
    simpa [prefixWord, tailWord_4921898, baseEnd_4921898] using wordTrace_append hprefix tailTrace_4921898
  have hstable : (prefixWord ++ tailWord_4921898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921898).length < 2 ^ (prefixWord ++ tailWord_4921898).sum := by decide
  have hdescent : baseEnd_4921898 < baseStart_4921898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921928 : List Nat := [2, 1, 3, 1, 1, 1, 1, 6, 1, 3, 3]
def baseStart_4921928 : Nat := 118140960795 + 4921928 * 2 ^ 59
def prefixEnd_4921928 : Nat := 4983230072969 + 3 ^ 40 * 4921928 * 2
def baseEnd_4921928 : Nat := 2527314810822724167764471

theorem tailTrace_4921928 : CollatzResearch.WordTrace tailWord_4921928 prefixEnd_4921928 2527314810822724167764471 := by
  unfold tailWord_4921928
  simp only [CollatzResearch.WordTrace]
  refine ⟨89758731056351464612027219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119678308075135286149369625 89758731056351464612027219)
  ·
    refine ⟨134638096584527196918040829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89758731056351464612027219 134638096584527196918040829)
    ·
      refine ⟨50489286219197698844265311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134638096584527196918040829 50489286219197698844265311)
      ·
        refine ⟨75733929328796548266397967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50489286219197698844265311 75733929328796548266397967)
        ·
          refine ⟨113600893993194822399596951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75733929328796548266397967 113600893993194822399596951)
          ·
            refine ⟨170401340989792233599395427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113600893993194822399596951 170401340989792233599395427)
            ·
              refine ⟨255602011484688350399093141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170401340989792233599395427 255602011484688350399093141)
              ·
                refine ⟨11981344288344766424957491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 255602011484688350399093141 11981344288344766424957491)
                ·
                  refine ⟨17972016432517149637436237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11981344288344766424957491 17972016432517149637436237)
                  ·
                    refine ⟨6739506162193931114038589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17972016432517149637436237 6739506162193931114038589)
                    ·
                      refine ⟨2527314810822724167764471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6739506162193931114038589 2527314810822724167764471)
                      ·
                        rfl

theorem cell23_4921928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_4921928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921928 prefixEnd_4921928 := by exact prefixLift 4921928
  have htrace : WordTrace (prefixWord ++ tailWord_4921928) baseStart_4921928 baseEnd_4921928 := by
    simpa [prefixWord, tailWord_4921928, baseEnd_4921928] using wordTrace_append hprefix tailTrace_4921928
  have hstable : (prefixWord ++ tailWord_4921928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921928).length < 2 ^ (prefixWord ++ tailWord_4921928).sum := by decide
  have hdescent : baseEnd_4921928 < baseStart_4921928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921955 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 3, 3, 2]
def baseStart_4921955 : Nat := 118140960795 + 4921955 * 2 ^ 59
def prefixEnd_4921955 : Nat := 4983230072969 + 3 ^ 40 * 4921955 * 2
def baseEnd_4921955 : Nat := 2527328674800395562126847

theorem tailTrace_4921955 : CollatzResearch.WordTrace tailWord_4921955 prefixEnd_4921955 2527328674800395562126847 := by
  unfold tailWord_4921955
  simp only [CollatzResearch.WordTrace]
  refine ⟨179518446883605112835287319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119678964589070075223524879 179518446883605112835287319)
  ·
    refine ⟨269277670325407669252930979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179518446883605112835287319 269277670325407669252930979)
    ·
      refine ⟨403916505488111503879396469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269277670325407669252930979 403916505488111503879396469)
      ·
        refine ⟨37867172389510453488693419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 403916505488111503879396469 37867172389510453488693419)
        ·
          refine ⟨56800758584265680233040129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37867172389510453488693419 56800758584265680233040129)
          ·
            refine ⟨42600568938199260174780097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56800758584265680233040129 42600568938199260174780097)
            ·
              refine ⟨31950426703649445131085073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42600568938199260174780097 31950426703649445131085073)
              ·
                refine ⟨23962820027737083848313805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31950426703649445131085073 23962820027737083848313805)
                ·
                  refine ⟨8986057510401406443117677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23962820027737083848313805 8986057510401406443117677)
                  ·
                    refine ⟨3369771566400527416169129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8986057510401406443117677 3369771566400527416169129)
                    ·
                      refine ⟨2527328674800395562126847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3369771566400527416169129 2527328674800395562126847)
                      ·
                        rfl

theorem cell23_4921955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_4921955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921955 prefixEnd_4921955 := by exact prefixLift 4921955
  have htrace : WordTrace (prefixWord ++ tailWord_4921955) baseStart_4921955 baseEnd_4921955 := by
    simpa [prefixWord, tailWord_4921955, baseEnd_4921955] using wordTrace_append hprefix tailTrace_4921955
  have hstable : (prefixWord ++ tailWord_4921955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921955).length < 2 ^ (prefixWord ++ tailWord_4921955).sum := by decide
  have hdescent : baseEnd_4921955 < baseStart_4921955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921961 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 1, 8]
def baseStart_4921961 : Nat := 118140960795 + 4921961 * 2 ^ 59
def prefixEnd_4921961 : Nat := 4983230072969 + 3 ^ 40 * 4921961 * 2
def baseEnd_4921961 : Nat := 842443918561440846217273

theorem tailTrace_4921961 : CollatzResearch.WordTrace tailWord_4921961 prefixEnd_4921961 842443918561440846217273 := by
  unfold tailWord_4921961
  simp only [CollatzResearch.WordTrace]
  refine ⟨179518665721583375860005737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119679110481055583906670491 179518665721583375860005737)
  ·
    refine ⟨134638999291187531895004303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179518665721583375860005737 134638999291187531895004303)
    ·
      refine ⟨201958498936781297842506455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134638999291187531895004303 201958498936781297842506455)
      ·
        refine ⟨302937748405171946763759683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201958498936781297842506455 302937748405171946763759683)
        ·
          refine ⟨454406622607757920145639525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302937748405171946763759683 454406622607757920145639525)
          ·
            refine ⟨85201241738954610027307411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 454406622607757920145639525 85201241738954610027307411)
            ·
              refine ⟨127801862608431915040961117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85201241738954610027307411 127801862608431915040961117)
              ·
                refine ⟨47925698478161968140360419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127801862608431915040961117 47925698478161968140360419)
                ·
                  refine ⟨71888547717242952210540629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47925698478161968140360419 71888547717242952210540629)
                  ·
                    refine ⟨842443918561440846217273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71888547717242952210540629 842443918561440846217273)
                    ·
                      rfl

theorem cell23_4921961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 8].length) (baseStart_4921961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921961 prefixEnd_4921961 := by exact prefixLift 4921961
  have htrace : WordTrace (prefixWord ++ tailWord_4921961) baseStart_4921961 baseEnd_4921961 := by
    simpa [prefixWord, tailWord_4921961, baseEnd_4921961] using wordTrace_append hprefix tailTrace_4921961
  have hstable : (prefixWord ++ tailWord_4921961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921961).length < 2 ^ (prefixWord ++ tailWord_4921961).sum := by decide
  have hdescent : baseEnd_4921961 < baseStart_4921961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921962 : List Nat := [3, 1, 3, 2, 1, 1, 3, 3, 2, 1, 3]
def baseStart_4921962 : Nat := 118140960795 + 4921962 * 2 ^ 59
def prefixEnd_4921962 : Nat := 4983230072969 + 3 ^ 40 * 4921962 * 2
def baseEnd_4921962 : Nat := 2527332269164977034739315

theorem tailTrace_4921962 : CollatzResearch.WordTrace tailWord_4921962 prefixEnd_4921962 2527332269164977034739315 := by
  unfold tailWord_4921962
  simp only [CollatzResearch.WordTrace]
  refine ⟨44879675548644938257698035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119679134796386502020528093 44879675548644938257698035)
  ·
    refine ⟨67319513322967407386547053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44879675548644938257698035 67319513322967407386547053)
    ·
      refine ⟨25244817496112777769955145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67319513322967407386547053 25244817496112777769955145)
      ·
        refine ⟨18933613122084583327466359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25244817496112777769955145 18933613122084583327466359)
        ·
          refine ⟨28400419683126874991199539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18933613122084583327466359 28400419683126874991199539)
          ·
            refine ⟨42600629524690312486799309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28400419683126874991199539 42600629524690312486799309)
            ·
              refine ⟨15975236071758867182549741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42600629524690312486799309 15975236071758867182549741)
              ·
                refine ⟨5990713526909575193456153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15975236071758867182549741 5990713526909575193456153)
                ·
                  refine ⟨4493035145182181395092115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5990713526909575193456153 4493035145182181395092115)
                  ·
                    refine ⟨6739552717773272092638173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4493035145182181395092115 6739552717773272092638173)
                    ·
                      refine ⟨2527332269164977034739315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6739552717773272092638173 2527332269164977034739315)
                      ·
                        rfl

theorem cell23_4921962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_4921962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921962 prefixEnd_4921962 := by exact prefixLift 4921962
  have htrace : WordTrace (prefixWord ++ tailWord_4921962) baseStart_4921962 baseEnd_4921962 := by
    simpa [prefixWord, tailWord_4921962, baseEnd_4921962] using wordTrace_append hprefix tailTrace_4921962
  have hstable : (prefixWord ++ tailWord_4921962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921962).length < 2 ^ (prefixWord ++ tailWord_4921962).sum := by decide
  have hdescent : baseEnd_4921962 < baseStart_4921962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4921989 : List Nat := [1, 3, 1, 1, 4, 3, 3, 1, 1, 3, 2]
def baseStart_4921989 : Nat := 118140960795 + 4921989 * 2 ^ 59
def prefixEnd_4921989 : Nat := 4983230072969 + 3 ^ 40 * 4921989 * 2
def baseEnd_4921989 : Nat := 2527346133142648429101691

theorem tailTrace_4921989 : CollatzResearch.WordTrace tailWord_4921989 prefixEnd_4921989 2527346133142648429101691 := by
  unfold tailWord_4921989
  simp only [CollatzResearch.WordTrace]
  refine ⟨179519686965481936642025021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119679791310321291094683347 179519686965481936642025021)
  ·
    refine ⟨67319882612055726240759383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179519686965481936642025021 67319882612055726240759383)
    ·
      refine ⟨100979823918083589361139075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67319882612055726240759383 100979823918083589361139075)
      ·
        refine ⟨151469735877125384041708613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100979823918083589361139075 151469735877125384041708613)
        ·
          refine ⟨28400575476961009507820365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151469735877125384041708613 28400575476961009507820365)
          ·
            refine ⟨10650215803860378565432637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28400575476961009507820365 10650215803860378565432637)
            ·
              refine ⟨3993830926447641962037239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10650215803860378565432637 3993830926447641962037239)
              ·
                refine ⟨5990746389671462943055859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3993830926447641962037239 5990746389671462943055859)
                ·
                  refine ⟨8986119584507194414583789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5990746389671462943055859 8986119584507194414583789)
                  ·
                    refine ⟨3369794844190197905468921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8986119584507194414583789 3369794844190197905468921)
                    ·
                      refine ⟨2527346133142648429101691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3369794844190197905468921 2527346133142648429101691)
                      ·
                        rfl

theorem cell23_4921989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 1, 3, 2].length) (baseStart_4921989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4921989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4921989 prefixEnd_4921989 := by exact prefixLift 4921989
  have htrace : WordTrace (prefixWord ++ tailWord_4921989) baseStart_4921989 baseEnd_4921989 := by
    simpa [prefixWord, tailWord_4921989, baseEnd_4921989] using wordTrace_append hprefix tailTrace_4921989
  have hstable : (prefixWord ++ tailWord_4921989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4921989).length < 2 ^ (prefixWord ++ tailWord_4921989).sum := by decide
  have hdescent : baseEnd_4921989 < baseStart_4921989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4921989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922008 : List Nat := [2, 1, 2, 4, 1, 1, 2, 3, 7]
def baseStart_4922008 : Nat := 118140960795 + 4922008 * 2 ^ 59
def prefixEnd_4922008 : Nat := 4983230072969 + 3 ^ 40 * 4922008 * 2
def baseEnd_4922008 : Nat := 280817321030564872751567

theorem tailTrace_4922008 : CollatzResearch.WordTrace tailWord_4922008 prefixEnd_4922008 280817321030564872751567 := by
  unfold tailWord_4922008
  simp only [CollatzResearch.WordTrace]
  refine ⟨89760189976206551443483339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119680253301608735257977785 89760189976206551443483339)
  ·
    refine ⟨134640284964309827165225009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89760189976206551443483339 134640284964309827165225009)
    ·
      refine ⟨100980213723232370373918757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134640284964309827165225009 100980213723232370373918757)
      ·
        refine ⟨18933790073106069445109767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100980213723232370373918757 18933790073106069445109767)
        ·
          refine ⟨28400685109659104167664651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18933790073106069445109767 28400685109659104167664651)
          ·
            refine ⟨42601027664488656251496977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28400685109659104167664651 42601027664488656251496977)
            ·
              refine ⟨31950770748366492188622733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42601027664488656251496977 31950770748366492188622733)
              ·
                refine ⟨11981539030637434570733525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31950770748366492188622733 11981539030637434570733525)
                ·
                  refine ⟨280817321030564872751567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11981539030637434570733525 280817321030564872751567)
                  ·
                    rfl

theorem cell23_4922008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 7].length) (baseStart_4922008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922008 prefixEnd_4922008 := by exact prefixLift 4922008
  have htrace : WordTrace (prefixWord ++ tailWord_4922008) baseStart_4922008 baseEnd_4922008 := by
    simpa [prefixWord, tailWord_4922008, baseEnd_4922008] using wordTrace_append hprefix tailTrace_4922008
  have hstable : (prefixWord ++ tailWord_4922008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922008).length < 2 ^ (prefixWord ++ tailWord_4922008).sum := by decide
  have hdescent : baseEnd_4922008 < baseStart_4922008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922095 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 3]
def baseStart_4922095 : Nat := 118140960795 + 4922095 * 2 ^ 59
def prefixEnd_4922095 : Nat := 4983230072969 + 3 ^ 40 * 4922095 * 2
def baseEnd_4922095 : Nat := 2527400562092025014376203

theorem tailTrace_4922095 : CollatzResearch.WordTrace tailWord_4922095 prefixEnd_4922095 2527400562092025014376203 := by
  unfold tailWord_4922095
  simp only [CollatzResearch.WordTrace]
  refine ⟨179523553103097916745383739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119682368735398611163589159 179523553103097916745383739)
  ·
    refine ⟨269285329654646875118075609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179523553103097916745383739 269285329654646875118075609)
    ·
      refine ⟨201963997240985156338556707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269285329654646875118075609 201963997240985156338556707)
      ·
        refine ⟨302945995861477734507835061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201963997240985156338556707 302945995861477734507835061)
        ·
          refine ⟨28401187112013537610109537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 302945995861477734507835061 28401187112013537610109537)
          ·
            refine ⟨21300890334010153207582153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28401187112013537610109537 21300890334010153207582153)
            ·
              refine ⟨15975667750507614905686615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21300890334010153207582153 15975667750507614905686615)
              ·
                refine ⟨23963501625761422358529923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15975667750507614905686615 23963501625761422358529923)
                ·
                  refine ⟨35945252438642133537794885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23963501625761422358529923 35945252438642133537794885)
                  ·
                    refine ⟨6739734832245400038336541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35945252438642133537794885 6739734832245400038336541)
                    ·
                      refine ⟨2527400562092025014376203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6739734832245400038336541 2527400562092025014376203)
                      ·
                        rfl

theorem cell23_4922095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 3].length) (baseStart_4922095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922095 prefixEnd_4922095 := by exact prefixLift 4922095
  have htrace : WordTrace (prefixWord ++ tailWord_4922095) baseStart_4922095 baseEnd_4922095 := by
    simpa [prefixWord, tailWord_4922095, baseEnd_4922095] using wordTrace_append hprefix tailTrace_4922095
  have hstable : (prefixWord ++ tailWord_4922095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922095).length < 2 ^ (prefixWord ++ tailWord_4922095).sum := by decide
  have hdescent : baseEnd_4922095 < baseStart_4922095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922119 : List Nat := [1, 1, 4, 4, 1, 3, 1, 1, 3, 4]
def baseStart_4922119 : Nat := 118140960795 + 4922119 * 2 ^ 59
def prefixEnd_4922119 : Nat := 4983230072969 + 3 ^ 40 * 4922119 * 2
def baseEnd_4922119 : Nat := 842470961875910973492031

theorem tailTrace_4922119 : CollatzResearch.WordTrace tailWord_4922119 prefixEnd_4922119 842470961875910973492031 := by
  unfold tailWord_4922119
  simp only [CollatzResearch.WordTrace]
  refine ⟨179524428455010968844257411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119682952303340645896171607 179524428455010968844257411)
  ·
    refine ⟨269286642682516453266386117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179524428455010968844257411 269286642682516453266386117)
    ·
      refine ⟨50491245502971834987447397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 269286642682516453266386117 50491245502971834987447397)
      ·
        refine ⟨9467108531807219060146387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50491245502971834987447397 9467108531807219060146387)
        ·
          refine ⟨14200662797710828590219581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9467108531807219060146387 14200662797710828590219581)
          ·
            refine ⟨5325248549141560721332343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14200662797710828590219581 5325248549141560721332343)
            ·
              refine ⟨7987872823712341081998515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5325248549141560721332343 7987872823712341081998515)
              ·
                refine ⟨11981809235568511622997773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7987872823712341081998515 11981809235568511622997773)
                ·
                  refine ⟨4493178463338191858624165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11981809235568511622997773 4493178463338191858624165)
                  ·
                    refine ⟨842470961875910973492031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4493178463338191858624165 842470961875910973492031)
                    ·
                      rfl

theorem cell23_4922119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_4922119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922119 prefixEnd_4922119 := by exact prefixLift 4922119
  have htrace : WordTrace (prefixWord ++ tailWord_4922119) baseStart_4922119 baseEnd_4922119 := by
    simpa [prefixWord, tailWord_4922119, baseEnd_4922119] using wordTrace_append hprefix tailTrace_4922119
  have hstable : (prefixWord ++ tailWord_4922119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922119).length < 2 ^ (prefixWord ++ tailWord_4922119).sum := by decide
  have hdescent : baseEnd_4922119 < baseStart_4922119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922145 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 3, 5]
def baseStart_4922145 : Nat := 118140960795 + 4922145 * 2 ^ 59
def prefixEnd_4922145 : Nat := 4983230072969 + 3 ^ 40 * 4922145 * 2
def baseEnd_4922145 : Nat := 842475412041583272916991

theorem tailTrace_4922145 : CollatzResearch.WordTrace tailWord_4922145 prefixEnd_4922145 842475412041583272916991 := by
  unfold tailWord_4922145
  simp only [CollatzResearch.WordTrace]
  refine ⟨179525376752916775284703889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119683584501944516856469259 179525376752916775284703889)
  ·
    refine ⟨134644032564687581463527917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179525376752916775284703889 134644032564687581463527917)
    ·
      refine ⟨50491512211757843048822969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134644032564687581463527917 50491512211757843048822969)
      ·
        refine ⟨37868634158818382286617227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50491512211757843048822969 37868634158818382286617227)
        ·
          refine ⟨56802951238227573429925841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37868634158818382286617227 56802951238227573429925841)
          ·
            refine ⟨42602213428670680072444381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56802951238227573429925841 42602213428670680072444381)
            ·
              refine ⟨15975830035751505027166643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42602213428670680072444381 15975830035751505027166643)
              ·
                refine ⟨23963745053627257540749965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15975830035751505027166643 23963745053627257540749965)
                ·
                  refine ⟨8986404395110221577781237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23963745053627257540749965 8986404395110221577781237)
                  ·
                    refine ⟨842475412041583272916991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8986404395110221577781237 842475412041583272916991)
                    ·
                      rfl

theorem cell23_4922145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_4922145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922145 prefixEnd_4922145 := by exact prefixLift 4922145
  have htrace : WordTrace (prefixWord ++ tailWord_4922145) baseStart_4922145 baseEnd_4922145 := by
    simpa [prefixWord, tailWord_4922145, baseEnd_4922145] using wordTrace_append hprefix tailTrace_4922145
  have hstable : (prefixWord ++ tailWord_4922145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922145).length < 2 ^ (prefixWord ++ tailWord_4922145).sum := by decide
  have hdescent : baseEnd_4922145 < baseStart_4922145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922192 : List Nat := [2, 1, 1, 1, 1, 4, 4, 3, 2, 4]
def baseStart_4922192 : Nat := 118140960795 + 4922192 * 2 ^ 59
def prefixEnd_4922192 : Nat := 4983230072969 + 3 ^ 40 * 4922192 * 2
def baseEnd_4922192 : Nat := 842483456571837044954419

theorem tailTrace_4922192 : CollatzResearch.WordTrace tailWord_4922192 prefixEnd_4922192 842483456571837044954419 := by
  unfold tailWord_4922192
  simp only [CollatzResearch.WordTrace]
  refine ⟨89763545491873251155832415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119684727322497668207776553 89763545491873251155832415)
  ·
    refine ⟨134645318237809876733748623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89763545491873251155832415 134645318237809876733748623)
    ·
      refine ⟨201967977356714815100622935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134645318237809876733748623 201967977356714815100622935)
      ·
        refine ⟨302951966035072222650934403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201967977356714815100622935 302951966035072222650934403)
        ·
          refine ⟨454427949052608333976401605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302951966035072222650934403 454427949052608333976401605)
          ·
            refine ⟨85205240447364062620575301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 454427949052608333976401605 85205240447364062620575301)
            ·
              refine ⟨15975982583880761741357869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85205240447364062620575301 15975982583880761741357869)
              ·
                refine ⟨5990993468955285653009201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15975982583880761741357869 5990993468955285653009201)
                ·
                  refine ⟨4493245101716464239756901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5990993468955285653009201 4493245101716464239756901)
                  ·
                    refine ⟨842483456571837044954419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4493245101716464239756901 842483456571837044954419)
                    ·
                      rfl

theorem cell23_4922192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 2, 4].length) (baseStart_4922192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922192 prefixEnd_4922192 := by exact prefixLift 4922192
  have htrace : WordTrace (prefixWord ++ tailWord_4922192) baseStart_4922192 baseEnd_4922192 := by
    simpa [prefixWord, tailWord_4922192, baseEnd_4922192] using wordTrace_append hprefix tailTrace_4922192
  have hstable : (prefixWord ++ tailWord_4922192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922192).length < 2 ^ (prefixWord ++ tailWord_4922192).sum := by decide
  have hdescent : baseEnd_4922192 < baseStart_4922192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922199 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 5, 2, 2]
def baseStart_4922199 : Nat := 118140960795 + 4922199 * 2 ^ 59
def prefixEnd_4922199 : Nat := 4983230072969 + 3 ^ 40 * 4922199 * 2
def baseEnd_4922199 : Nat := 2527453964080092607475725

theorem tailTrace_4922199 : CollatzResearch.WordTrace tailWord_4922199 prefixEnd_4922199 2527453964080092607475725 := by
  unfold tailWord_4922199
  simp only [CollatzResearch.WordTrace]
  refine ⟨179527346294721142507169651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119684897529814095004779767 179527346294721142507169651)
  ·
    refine ⟨269291019442081713760754477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179527346294721142507169651 269291019442081713760754477)
    ·
      refine ⟨100984132290780642660282929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269291019442081713760754477 100984132290780642660282929)
      ·
        refine ⟨75738099218085481995212197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100984132290780642660282929 75738099218085481995212197)
        ·
          refine ⟨14200893603391027874102287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75738099218085481995212197 14200893603391027874102287)
          ·
            refine ⟨21301340405086541811153431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14200893603391027874102287 21301340405086541811153431)
            ·
              refine ⟨31952010607629812716730147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21301340405086541811153431 31952010607629812716730147)
              ·
                refine ⟨47928015911444719075095221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31952010607629812716730147 47928015911444719075095221)
                ·
                  refine ⟨4493251491697942413290177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47928015911444719075095221 4493251491697942413290177)
                  ·
                    refine ⟨3369938618773456809967633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4493251491697942413290177 3369938618773456809967633)
                    ·
                      refine ⟨2527453964080092607475725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3369938618773456809967633 2527453964080092607475725)
                      ·
                        rfl

theorem cell23_4922199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 2, 2].length) (baseStart_4922199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922199 prefixEnd_4922199 := by exact prefixLift 4922199
  have htrace : WordTrace (prefixWord ++ tailWord_4922199) baseStart_4922199 baseEnd_4922199 := by
    simpa [prefixWord, tailWord_4922199, baseEnd_4922199] using wordTrace_append hprefix tailTrace_4922199
  have hstable : (prefixWord ++ tailWord_4922199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922199).length < 2 ^ (prefixWord ++ tailWord_4922199).sum := by decide
  have hdescent : baseEnd_4922199 < baseStart_4922199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922202 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3]
def baseStart_4922202 : Nat := 118140960795 + 4922202 * 2 ^ 59
def prefixEnd_4922202 : Nat := 4983230072969 + 3 ^ 40 * 4922202 * 2
def baseEnd_4922202 : Nat := 2527455504522056095738211

theorem tailTrace_4922202 : CollatzResearch.WordTrace tailWord_4922202 prefixEnd_4922202 2527455504522056095738211 := by
  unfold tailWord_4922202
  simp only [CollatzResearch.WordTrace]
  refine ⟨44881863928427568504882215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119684970475806849346352573 44881863928427568504882215)
  ·
    refine ⟨67322795892641352757323323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44881863928427568504882215 67322795892641352757323323)
    ·
      refine ⟨100984193838962029135984985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67322795892641352757323323 100984193838962029135984985)
      ·
        refine ⟨75738145379221521851988739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100984193838962029135984985 75738145379221521851988739)
        ·
          refine ⟨113607218068832282777983109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75738145379221521851988739 113607218068832282777983109)
          ·
            refine ⟨21301353387906053020871833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113607218068832282777983109 21301353387906053020871833)
            ·
              refine ⟨15976015040929539765653875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21301353387906053020871833 15976015040929539765653875)
              ·
                refine ⟨23964022561394309648480813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15976015040929539765653875 23964022561394309648480813)
                ·
                  refine ⟨8986508460522866118180305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23964022561394309648480813 8986508460522866118180305)
                  ·
                    refine ⟨6739881345392149588635229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8986508460522866118180305 6739881345392149588635229)
                    ·
                      refine ⟨2527455504522056095738211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6739881345392149588635229 2527455504522056095738211)
                      ·
                        rfl

theorem cell23_4922202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_4922202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922202 prefixEnd_4922202 := by exact prefixLift 4922202
  have htrace : WordTrace (prefixWord ++ tailWord_4922202) baseStart_4922202 baseEnd_4922202 := by
    simpa [prefixWord, tailWord_4922202, baseEnd_4922202] using wordTrace_append hprefix tailTrace_4922202
  have hstable : (prefixWord ++ tailWord_4922202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922202).length < 2 ^ (prefixWord ++ tailWord_4922202).sum := by decide
  have hdescent : baseEnd_4922202 < baseStart_4922202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922212 : List Nat := [2, 3, 1, 1, 4, 1, 2, 2, 1, 2, 4]
def baseStart_4922212 : Nat := 118140960795 + 4922212 * 2 ^ 59
def prefixEnd_4922212 : Nat := 4983230072969 + 3 ^ 40 * 4922212 * 2
def baseEnd_4922212 : Nat := 2527460639328601056613165

theorem tailTrace_4922212 : CollatzResearch.WordTrace tailWord_4922212 prefixEnd_4922212 2527460639328601056613165 := by
  unfold tailWord_4922212
  simp only [CollatzResearch.WordTrace]
  refine ⟨89763910221837022863696445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119685213629116030484928593 89763910221837022863696445)
  ·
    refine ⟨33661466333188883573886167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89763910221837022863696445 33661466333188883573886167)
    ·
      refine ⟨50492199499783325360829251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33661466333188883573886167 50492199499783325360829251)
      ·
        refine ⟨75738299249674988041243877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50492199499783325360829251 75738299249674988041243877)
        ·
          refine ⟨14200931109314060257733227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75738299249674988041243877 14200931109314060257733227)
          ·
            refine ⟨21301396663971090386599841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14200931109314060257733227 21301396663971090386599841)
            ·
              refine ⟨15976047497978317789949881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21301396663971090386599841 15976047497978317789949881)
              ·
                refine ⟨11982035623483738342462411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15976047497978317789949881 11982035623483738342462411)
                ·
                  refine ⟨17973053435225607513693617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11982035623483738342462411 17973053435225607513693617)
                  ·
                    refine ⟨13479790076419205635270213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17973053435225607513693617 13479790076419205635270213)
                    ·
                      refine ⟨2527460639328601056613165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13479790076419205635270213 2527460639328601056613165)
                      ·
                        rfl

theorem cell23_4922212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_4922212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922212 prefixEnd_4922212 := by exact prefixLift 4922212
  have htrace : WordTrace (prefixWord ++ tailWord_4922212) baseStart_4922212 baseEnd_4922212 := by
    simpa [prefixWord, tailWord_4922212, baseEnd_4922212] using wordTrace_append hprefix tailTrace_4922212
  have hstable : (prefixWord ++ tailWord_4922212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922212).length < 2 ^ (prefixWord ++ tailWord_4922212).sum := by decide
  have hdescent : baseEnd_4922212 < baseStart_4922212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922216 : List Nat := [2, 1, 4, 2, 1, 4, 2, 1, 1, 1, 4]
def baseStart_4922216 : Nat := 118140960795 + 4922216 * 2 ^ 59
def prefixEnd_4922216 : Nat := 4983230072969 + 3 ^ 40 * 4922216 * 2
def baseEnd_4922216 : Nat := 2527462693251219040963147

theorem tailTrace_4922216 : CollatzResearch.WordTrace tailWord_4922216 prefixEnd_4922216 2527462693251219040963147 := by
  unfold tailWord_4922216
  simp only [CollatzResearch.WordTrace]
  refine ⟨89763983167829777205269251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119685310890439702940359001 89763983167829777205269251)
  ·
    refine ⟨134645974751744665807903877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89763983167829777205269251 134645974751744665807903877)
    ·
      refine ⟨25246120265952124838981977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134645974751744665807903877 25246120265952124838981977)
      ·
        refine ⟨18934590199464093629236483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25246120265952124838981977 18934590199464093629236483)
        ·
          refine ⟨28401885299196140443854725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18934590199464093629236483 28401885299196140443854725)
          ·
            refine ⟨5325353493599276333222761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28401885299196140443854725 5325353493599276333222761)
            ·
              refine ⟨3994015120199457249917071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5325353493599276333222761 3994015120199457249917071)
              ·
                refine ⟨5991022680299185874875607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3994015120199457249917071 5991022680299185874875607)
                ·
                  refine ⟨8986534020448778812313411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5991022680299185874875607 8986534020448778812313411)
                  ·
                    refine ⟨13479801030673168218470117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8986534020448778812313411 13479801030673168218470117)
                    ·
                      refine ⟨2527462693251219040963147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13479801030673168218470117 2527462693251219040963147)
                      ·
                        rfl

theorem cell23_4922216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_4922216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922216 prefixEnd_4922216 := by exact prefixLift 4922216
  have htrace : WordTrace (prefixWord ++ tailWord_4922216) baseStart_4922216 baseEnd_4922216 := by
    simpa [prefixWord, tailWord_4922216, baseEnd_4922216] using wordTrace_append hprefix tailTrace_4922216
  have hstable : (prefixWord ++ tailWord_4922216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922216).length < 2 ^ (prefixWord ++ tailWord_4922216).sum := by decide
  have hdescent : baseEnd_4922216 < baseStart_4922216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922219 : List Nat := [1, 1, 1, 1, 2, 2, 8, 1, 1, 2, 3]
def baseStart_4922219 : Nat := 118140960795 + 4922219 * 2 ^ 59
def prefixEnd_4922219 : Nat := 4983230072969 + 3 ^ 40 * 4922219 * 2
def baseEnd_4922219 : Nat := 2527464233693182529225633

theorem tailTrace_4922219 : CollatzResearch.WordTrace tailWord_4922219 prefixEnd_4922219 2527464233693182529225633 := by
  unfold tailWord_4922219
  simp only [CollatzResearch.WordTrace]
  refine ⟨179528075754648685922897711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119685383836432457281931807 179528075754648685922897711)
  ·
    refine ⟨269292113631973028884346567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179528075754648685922897711 269292113631973028884346567)
    ·
      refine ⟨403938170447959543326519851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269292113631973028884346567 403938170447959543326519851)
      ·
        refine ⟨605907255671939314989779777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403938170447959543326519851 605907255671939314989779777)
        ·
          refine ⟨454430441753954486242334833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 605907255671939314989779777 454430441753954486242334833)
          ·
            refine ⟨340822831315465864681751125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 454430441753954486242334833 340822831315465864681751125)
            ·
              refine ⟨3994017554478115601739271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 340822831315465864681751125 3994017554478115601739271)
              ·
                refine ⟨5991026331717173402608907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3994017554478115601739271 5991026331717173402608907)
                ·
                  refine ⟨8986539497575760103913361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5991026331717173402608907 8986539497575760103913361)
                  ·
                    refine ⟨6739904623181820077935021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8986539497575760103913361 6739904623181820077935021)
                    ·
                      refine ⟨2527464233693182529225633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6739904623181820077935021 2527464233693182529225633)
                      ·
                        rfl

theorem cell23_4922219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 1, 2, 3].length) (baseStart_4922219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922219 prefixEnd_4922219 := by exact prefixLift 4922219
  have htrace : WordTrace (prefixWord ++ tailWord_4922219) baseStart_4922219 baseEnd_4922219 := by
    simpa [prefixWord, tailWord_4922219, baseEnd_4922219] using wordTrace_append hprefix tailTrace_4922219
  have hstable : (prefixWord ++ tailWord_4922219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922219).length < 2 ^ (prefixWord ++ tailWord_4922219).sum := by decide
  have hdescent : baseEnd_4922219 < baseStart_4922219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922222 : List Nat := [4, 1, 2, 3, 2, 1, 10]
def baseStart_4922222 : Nat := 118140960795 + 4922222 * 2 ^ 59
def prefixEnd_4922222 : Nat := 4983230072969 + 3 ^ 40 * 4922222 * 2
def baseEnd_4922222 : Nat := 31203281162162296512199

theorem tailTrace_4922222 : CollatzResearch.WordTrace tailWord_4922222 prefixEnd_4922222 31203281162162296512199 := by
  unfold tailWord_4922222
  simp only [CollatzResearch.WordTrace]
  refine ⟨22441023146704727179407115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119685456782425211623504613 22441023146704727179407115)
  ·
    refine ⟨33661534720057090769110673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22441023146704727179407115 33661534720057090769110673)
    ·
      refine ⟨25246151040042818076833005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33661534720057090769110673 25246151040042818076833005)
      ·
        refine ⟨9467306640016056778812377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25246151040042818076833005 9467306640016056778812377)
        ·
          refine ⟨7100479980012042584109283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9467306640016056778812377 7100479980012042584109283)
          ·
            refine ⟨10650719970018063876163925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7100479980012042584109283 10650719970018063876163925)
            ·
              refine ⟨31203281162162296512199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10650719970018063876163925 31203281162162296512199)
              ·
                rfl

theorem cell23_4922222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 10].length) (baseStart_4922222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922222 prefixEnd_4922222 := by exact prefixLift 4922222
  have htrace : WordTrace (prefixWord ++ tailWord_4922222) baseStart_4922222 baseEnd_4922222 := by
    simpa [prefixWord, tailWord_4922222, baseEnd_4922222] using wordTrace_append hprefix tailTrace_4922222
  have hstable : (prefixWord ++ tailWord_4922222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922222).length < 2 ^ (prefixWord ++ tailWord_4922222).sum := by decide
  have hdescent : baseEnd_4922222 < baseStart_4922222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922249 : List Nat := [1, 2, 1, 1, 5, 4, 1, 1, 1, 3, 3]
def baseStart_4922249 : Nat := 118140960795 + 4922249 * 2 ^ 59
def prefixEnd_4922249 : Nat := 4983230072969 + 3 ^ 40 * 4922249 * 2
def baseEnd_4922249 : Nat := 2527479638112817411850495

theorem tailTrace_4922249 : CollatzResearch.WordTrace tailWord_4922249 prefixEnd_4922249 2527479638112817411850495 := by
  unfold tailWord_4922249
  simp only [CollatzResearch.WordTrace]
  refine ⟨179529169944540001046489801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119686113296360000697659867 179529169944540001046489801)
  ·
    refine ⟨134646877458405000784867351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179529169944540001046489801 134646877458405000784867351)
    ·
      refine ⟨201970316187607501177301027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134646877458405000784867351 201970316187607501177301027)
      ·
        refine ⟨302955474281411251765951541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201970316187607501177301027 302955474281411251765951541)
        ·
          refine ⟨28402075713882304853057957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 302955474281411251765951541 28402075713882304853057957)
          ·
            refine ⟨5325389196352932159948367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28402075713882304853057957 5325389196352932159948367)
            ·
              refine ⟨7988083794529398239922551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5325389196352932159948367 7988083794529398239922551)
              ·
                refine ⟨11982125691794097359883827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7988083794529398239922551 11982125691794097359883827)
                ·
                  refine ⟨17973188537691146039825741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11982125691794097359883827 17973188537691146039825741)
                  ·
                    refine ⟨6739945701634179764934653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17973188537691146039825741 6739945701634179764934653)
                    ·
                      refine ⟨2527479638112817411850495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6739945701634179764934653 2527479638112817411850495)
                      ·
                        rfl

theorem cell23_4922249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 3, 3].length) (baseStart_4922249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922249 prefixEnd_4922249 := by exact prefixLift 4922249
  have htrace : WordTrace (prefixWord ++ tailWord_4922249) baseStart_4922249 baseEnd_4922249 := by
    simpa [prefixWord, tailWord_4922249, baseEnd_4922249] using wordTrace_append hprefix tailTrace_4922249
  have hstable : (prefixWord ++ tailWord_4922249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922249).length < 2 ^ (prefixWord ++ tailWord_4922249).sum := by decide
  have hdescent : baseEnd_4922249 < baseStart_4922249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922275 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 5]
def baseStart_4922275 : Nat := 118140960795 + 4922275 * 2 ^ 59
def prefixEnd_4922275 : Nat := 4983230072969 + 3 ^ 40 * 4922275 * 2
def baseEnd_4922275 : Nat := 2527492988609834310125375

theorem tailTrace_4922275 : CollatzResearch.WordTrace tailWord_4922275 prefixEnd_4922275 2527492988609834310125375 := by
  unfold tailWord_4922275
  simp only [CollatzResearch.WordTrace]
  refine ⟨179530118242445807486936279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119686745494963871657957519 179530118242445807486936279)
  ·
    refine ⟨269295177363668711230404419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179530118242445807486936279 269295177363668711230404419)
    ·
      refine ⟨403942766045503066845606629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269295177363668711230404419 403942766045503066845606629)
      ·
        refine ⟨75739268633531825033551243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 403942766045503066845606629 75739268633531825033551243)
        ·
          refine ⟨113608902950297737550326865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75739268633531825033551243 113608902950297737550326865)
          ·
            refine ⟨85206677212723303162745149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113608902950297737550326865 85206677212723303162745149)
            ·
              refine ⟨31952503954771238686029431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85206677212723303162745149 31952503954771238686029431)
              ·
                refine ⟨47928755932156858029044147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31952503954771238686029431 47928755932156858029044147)
                ·
                  refine ⟨71893133898235287043566221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47928755932156858029044147 71893133898235287043566221)
                  ·
                    refine ⟨26959925211838232641337333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71893133898235287043566221 26959925211838232641337333)
                    ·
                      refine ⟨2527492988609834310125375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26959925211838232641337333 2527492988609834310125375)
                      ·
                        rfl

theorem cell23_4922275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_4922275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922275 prefixEnd_4922275 := by exact prefixLift 4922275
  have htrace : WordTrace (prefixWord ++ tailWord_4922275) baseStart_4922275 baseEnd_4922275 := by
    simpa [prefixWord, tailWord_4922275, baseEnd_4922275] using wordTrace_append hprefix tailTrace_4922275
  have hstable : (prefixWord ++ tailWord_4922275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922275).length < 2 ^ (prefixWord ++ tailWord_4922275).sum := by decide
  have hdescent : baseEnd_4922275 < baseStart_4922275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922294 : List Nat := [5, 1, 4, 1, 2, 1, 2, 1, 2, 4]
def baseStart_4922294 : Nat := 118140960795 + 4922294 * 2 ^ 59
def prefixEnd_4922294 : Nat := 4983230072969 + 3 ^ 40 * 4922294 * 2
def baseEnd_4922294 : Nat := 842500914914089911929263

theorem tailTrace_4922294 : CollatzResearch.WordTrace tailWord_4922294 prefixEnd_4922294 842500914914089911929263 := by
  unfold tailWord_4922294
  simp only [CollatzResearch.WordTrace]
  refine ⟨11220675701836060858242371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119687207486251315821251957 11220675701836060858242371)
  ·
    refine ⟨16831013552754091287363557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11220675701836060858242371 16831013552754091287363557)
    ·
      refine ⟨3155815041141392116380667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16831013552754091287363557 3155815041141392116380667)
      ·
        refine ⟨4733722561712088174571001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3155815041141392116380667 4733722561712088174571001)
        ·
          refine ⟨3550291921284066130928251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4733722561712088174571001 3550291921284066130928251)
          ·
            refine ⟨5325437881926099196392377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3550291921284066130928251 5325437881926099196392377)
            ·
              refine ⟨3994078411444574397294283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5325437881926099196392377 3994078411444574397294283)
              ·
                refine ⟨5991117617166861595941425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3994078411444574397294283 5991117617166861595941425)
                ·
                  refine ⟨4493338212875146196956069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5991117617166861595941425 4493338212875146196956069)
                  ·
                    refine ⟨842500914914089911929263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4493338212875146196956069 842500914914089911929263)
                    ·
                      rfl

theorem cell23_4922294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_4922294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922294 prefixEnd_4922294 := by exact prefixLift 4922294
  have htrace : WordTrace (prefixWord ++ tailWord_4922294) baseStart_4922294 baseEnd_4922294 := by
    simpa [prefixWord, tailWord_4922294, baseEnd_4922294] using wordTrace_append hprefix tailTrace_4922294
  have hstable : (prefixWord ++ tailWord_4922294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922294).length < 2 ^ (prefixWord ++ tailWord_4922294).sum := by decide
  have hdescent : baseEnd_4922294 < baseStart_4922294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922302 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_4922302 : Nat := 118140960795 + 4922302 * 2 ^ 59
def prefixEnd_4922302 : Nat := 4983230072969 + 3 ^ 40 * 4922302 * 2
def baseEnd_4922302 : Nat := 2527506852587505704487751

theorem tailTrace_4922302 : CollatzResearch.WordTrace tailWord_4922302 prefixEnd_4922302 2527506852587505704487751 := by
  unfold tailWord_4922302
  simp only [CollatzResearch.WordTrace]
  refine ⟨22441387876668498887271145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119687402008898660732112773 22441387876668498887271145)
  ·
    refine ⟨16831040907501374165453359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22441387876668498887271145 16831040907501374165453359)
    ·
      refine ⟨25246561361252061248180039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16831040907501374165453359 25246561361252061248180039)
      ·
        refine ⟨37869842041878091872270059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25246561361252061248180039 37869842041878091872270059)
        ·
          refine ⟨56804763062817137808405089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37869842041878091872270059 56804763062817137808405089)
          ·
            refine ⟨42603572297112853356303817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56804763062817137808405089 42603572297112853356303817)
            ·
              refine ⟨31952679222834640017227863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42603572297112853356303817 31952679222834640017227863)
              ·
                refine ⟨47929018834251960025841795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31952679222834640017227863 47929018834251960025841795)
                ·
                  refine ⟨71893528251377940038762693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47929018834251960025841795 71893528251377940038762693)
                  ·
                    refine ⟨13480036547133363757268005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71893528251377940038762693 13480036547133363757268005)
                    ·
                      refine ⟨2527506852587505704487751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13480036547133363757268005 2527506852587505704487751)
                      ·
                        rfl

theorem cell23_4922302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_4922302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922302 prefixEnd_4922302 := by exact prefixLift 4922302
  have htrace : WordTrace (prefixWord ++ tailWord_4922302) baseStart_4922302 baseEnd_4922302 := by
    simpa [prefixWord, tailWord_4922302, baseEnd_4922302] using wordTrace_append hprefix tailTrace_4922302
  have hstable : (prefixWord ++ tailWord_4922302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922302).length < 2 ^ (prefixWord ++ tailWord_4922302).sum := by decide
  have hdescent : baseEnd_4922302 < baseStart_4922302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922346 : List Nat := [3, 1, 3, 1, 2, 2, 4, 2, 5]
def baseStart_4922346 : Nat := 118140960795 + 4922346 * 2 ^ 59
def prefixEnd_4922346 : Nat := 4983230072969 + 3 ^ 40 * 4922346 * 2
def baseEnd_4922346 : Nat := 280836605081811503593061

theorem tailTrace_4922346 : CollatzResearch.WordTrace tailWord_4922346 prefixEnd_4922346 280836605081811503593061 := by
  unfold tailWord_4922346
  simp only [CollatzResearch.WordTrace]
  refine ⟨44883176956297146653192723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119688471883459057741847261 44883176956297146653192723)
  ·
    refine ⟨67324765434445719979789085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44883176956297146653192723 67324765434445719979789085)
    ·
      refine ⟨25246787037917144992420907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67324765434445719979789085 25246787037917144992420907)
      ·
        refine ⟨37870180556875717488631361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25246787037917144992420907 37870180556875717488631361)
        ·
          refine ⟨28402635417656788116473521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37870180556875717488631361 28402635417656788116473521)
          ·
            refine ⟨21301976563242591087355141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28402635417656788116473521 21301976563242591087355141)
            ·
              refine ⟨3994120605607985828879089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21301976563242591087355141 3994120605607985828879089)
              ·
                refine ⟨2995590454205989371659317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3994120605607985828879089 2995590454205989371659317)
                ·
                  refine ⟨280836605081811503593061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2995590454205989371659317 280836605081811503593061)
                  ·
                    rfl

theorem cell23_4922346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 5].length) (baseStart_4922346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922346 prefixEnd_4922346 := by exact prefixLift 4922346
  have htrace : WordTrace (prefixWord ++ tailWord_4922346) baseStart_4922346 baseEnd_4922346 := by
    simpa [prefixWord, tailWord_4922346, baseEnd_4922346] using wordTrace_append hprefix tailTrace_4922346
  have hstable : (prefixWord ++ tailWord_4922346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922346).length < 2 ^ (prefixWord ++ tailWord_4922346).sum := by decide
  have hdescent : baseEnd_4922346 < baseStart_4922346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922355 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 4, 8]
def baseStart_4922355 : Nat := 118140960795 + 4922355 * 2 ^ 59
def prefixEnd_4922355 : Nat := 4983230072969 + 3 ^ 40 * 4922355 * 2
def baseEnd_4922355 : Nat := 842511355687397999041669

theorem tailTrace_4922355 : CollatzResearch.WordTrace tailWord_4922355 prefixEnd_4922355 842511355687397999041669 := by
  unfold tailWord_4922355
  simp only [CollatzResearch.WordTrace]
  refine ⟨179533036082155981149848519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119688690721437320766565679 179533036082155981149848519)
  ·
    refine ⟨269299554123233971724772779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179533036082155981149848519 269299554123233971724772779)
    ·
      refine ⟨403949331184850957587159169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269299554123233971724772779 403949331184850957587159169)
      ·
        refine ⟨302961998388638218190369377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 403949331184850957587159169 302961998388638218190369377)
        ·
          refine ⟨227221498791478663642777033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302961998388638218190369377 227221498791478663642777033)
          ·
            refine ⟨170416124093608997732082775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227221498791478663642777033 170416124093608997732082775)
            ·
              refine ⟨255624186140413496598124163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170416124093608997732082775 255624186140413496598124163)
              ·
                refine ⟨383436279210620244897186245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255624186140413496598124163 383436279210620244897186245)
                ·
                  refine ⟨71894302351991295918222421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 383436279210620244897186245 71894302351991295918222421)
                  ·
                    refine ⟨842511355687397999041669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71894302351991295918222421 842511355687397999041669)
                    ·
                      rfl

theorem cell23_4922355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 8].length) (baseStart_4922355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922355 prefixEnd_4922355 := by exact prefixLift 4922355
  have htrace : WordTrace (prefixWord ++ tailWord_4922355) baseStart_4922355 baseEnd_4922355 := by
    simpa [prefixWord, tailWord_4922355, baseEnd_4922355] using wordTrace_append hprefix tailTrace_4922355
  have hstable : (prefixWord ++ tailWord_4922355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922355).length < 2 ^ (prefixWord ++ tailWord_4922355).sum := by decide
  have hdescent : baseEnd_4922355 < baseStart_4922355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922362 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4]
def baseStart_4922362 : Nat := 118140960795 + 4922362 * 2 ^ 59
def prefixEnd_4922362 : Nat := 4983230072969 + 3 ^ 40 * 4922362 * 2
def baseEnd_4922362 : Nat := 2527537661426775469737475

theorem tailTrace_4922362 : CollatzResearch.WordTrace tailWord_4922362 prefixEnd_4922362 2527537661426775469737475 := by
  unfold tailWord_4922362
  simp only [CollatzResearch.WordTrace]
  refine ⟨44883322848282655336338335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119688860928753747563568893 44883322848282655336338335)
  ·
    refine ⟨67324984272423983004507503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44883322848282655336338335 67324984272423983004507503)
    ·
      refine ⟨100987476408635974506761255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67324984272423983004507503 100987476408635974506761255)
      ·
        refine ⟨151481214612953961760141883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100987476408635974506761255 151481214612953961760141883)
        ·
          refine ⟨227221821919430942640212825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151481214612953961760141883 227221821919430942640212825)
          ·
            refine ⟨170416366439573206980159619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227221821919430942640212825 170416366439573206980159619)
            ·
              refine ⟨255624549659359810470239429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170416366439573206980159619 255624549659359810470239429)
              ·
                refine ⟨47929603061129964463169893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 255624549659359810470239429 47929603061129964463169893)
                ·
                  refine ⟨8986800573961868336844355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47929603061129964463169893 8986800573961868336844355)
                  ·
                    refine ⟨13480200860942802505266533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8986800573961868336844355 13480200860942802505266533)
                    ·
                      refine ⟨2527537661426775469737475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13480200860942802505266533 2527537661426775469737475)
                      ·
                        rfl

theorem cell23_4922362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_4922362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922362 prefixEnd_4922362 := by exact prefixLift 4922362
  have htrace : WordTrace (prefixWord ++ tailWord_4922362) baseStart_4922362 baseEnd_4922362 := by
    simpa [prefixWord, tailWord_4922362, baseEnd_4922362] using wordTrace_append hprefix tailTrace_4922362
  have hstable : (prefixWord ++ tailWord_4922362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922362).length < 2 ^ (prefixWord ++ tailWord_4922362).sum := by decide
  have hdescent : baseEnd_4922362 < baseStart_4922362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922379 : List Nat := [1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 4]
def baseStart_4922379 : Nat := 118140960795 + 4922379 * 2 ^ 59
def prefixEnd_4922379 : Nat := 4983230072969 + 3 ^ 40 * 4922379 * 2
def baseEnd_4922379 : Nat := 2527546390597901903224897

theorem tailTrace_4922379 : CollatzResearch.WordTrace tailWord_4922379 prefixEnd_4922379 2527546390597901903224897 := by
  unfold tailWord_4922379
  simp only [CollatzResearch.WordTrace]
  refine ⟨179533911434069033248722191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119689274289379355499148127 179533911434069033248722191)
  ·
    refine ⟨269300867151103549873083287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179533911434069033248722191 269300867151103549873083287)
    ·
      refine ⟨403951300726655324809624931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269300867151103549873083287 403951300726655324809624931)
      ·
        refine ⟨605926951089982987214437397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403951300726655324809624931 605926951089982987214437397)
        ·
          refine ⟨28402825832342952525676753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 605926951089982987214437397 28402825832342952525676753)
          ·
            refine ⟨21302119374257214394257565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28402825832342952525676753 21302119374257214394257565)
            ·
              refine ⟨7988294765346455397846587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21302119374257214394257565 7988294765346455397846587)
              ·
                refine ⟨11982442148019683096769881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7988294765346455397846587 11982442148019683096769881)
                ·
                  refine ⟨8986831611014762322577411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11982442148019683096769881 8986831611014762322577411)
                  ·
                    refine ⟨13480247416522143483866117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8986831611014762322577411 13480247416522143483866117)
                    ·
                      refine ⟨2527546390597901903224897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13480247416522143483866117 2527546390597901903224897)
                      ·
                        rfl

theorem cell23_4922379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 4].length) (baseStart_4922379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922379 prefixEnd_4922379 := by exact prefixLift 4922379
  have htrace : WordTrace (prefixWord ++ tailWord_4922379) baseStart_4922379 baseEnd_4922379 := by
    simpa [prefixWord, tailWord_4922379, baseEnd_4922379] using wordTrace_append hprefix tailTrace_4922379
  have hstable : (prefixWord ++ tailWord_4922379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922379).length < 2 ^ (prefixWord ++ tailWord_4922379).sum := by decide
  have hdescent : baseEnd_4922379 < baseStart_4922379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922392 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 2, 1, 6]
def baseStart_4922392 : Nat := 118140960795 + 4922392 * 2 ^ 59
def prefixEnd_4922392 : Nat := 4983230072969 + 3 ^ 40 * 4922392 * 2
def baseEnd_4922392 : Nat := 2527553065846410352362337

theorem tailTrace_4922392 : CollatzResearch.WordTrace tailWord_4922392 prefixEnd_4922392 2527553065846410352362337 := by
  unfold tailWord_4922392
  simp only [CollatzResearch.WordTrace]
  refine ⟨89767192791510968234472715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119689590388681290979296953 89767192791510968234472715)
  ·
    refine ⟨134650789187266452351709073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89767192791510968234472715 134650789187266452351709073)
    ·
      refine ⟨100988091890449839263781805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134650789187266452351709073 100988091890449839263781805)
      ·
        refine ⟨37870534458918689723918177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100988091890449839263781805 37870534458918689723918177)
        ·
          refine ⟨28402900844189017292938633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37870534458918689723918177 28402900844189017292938633)
          ·
            refine ⟨21302175633141762969703975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28402900844189017292938633 21302175633141762969703975)
            ·
              refine ⟨31953263449712644454555963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21302175633141762969703975 31953263449712644454555963)
              ·
                refine ⟨47929895174568966681833945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31953263449712644454555963 47929895174568966681833945)
                ·
                  refine ⟨35947421380926725011375459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47929895174568966681833945 35947421380926725011375459)
                  ·
                    refine ⟨53921132071390087517063189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35947421380926725011375459 53921132071390087517063189)
                    ·
                      refine ⟨2527553065846410352362337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53921132071390087517063189 2527553065846410352362337)
                      ·
                        rfl

theorem cell23_4922392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_4922392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922392 prefixEnd_4922392 := by exact prefixLift 4922392
  have htrace : WordTrace (prefixWord ++ tailWord_4922392) baseStart_4922392 baseEnd_4922392 := by
    simpa [prefixWord, tailWord_4922392, baseEnd_4922392] using wordTrace_append hprefix tailTrace_4922392
  have hstable : (prefixWord ++ tailWord_4922392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922392).length < 2 ^ (prefixWord ++ tailWord_4922392).sum := by decide
  have hdescent : baseEnd_4922392 < baseStart_4922392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922449 : List Nat := [1, 2, 2, 1, 3, 1, 4, 3, 1, 5]
def baseStart_4922449 : Nat := 118140960795 + 4922449 * 2 ^ 59
def prefixEnd_4922449 : Nat := 4983230072969 + 3 ^ 40 * 4922449 * 2
def baseEnd_4922449 : Nat := 842527444747905543116525

theorem tailTrace_4922449 : CollatzResearch.WordTrace tailWord_4922449 prefixEnd_4922449 842527444747905543116525 := by
  unfold tailWord_4922449
  simp only [CollatzResearch.WordTrace]
  refine ⟨179536464543815435203770401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119690976362543623469180267 179536464543815435203770401)
  ·
    refine ⟨134652348407861576402827801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179536464543815435203770401 134652348407861576402827801)
    ·
      refine ⟨100989261305896182302120851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134652348407861576402827801 100989261305896182302120851)
      ·
        refine ⟨151483891958844273453181277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100989261305896182302120851 151483891958844273453181277)
        ·
          refine ⟨56806459484566602544942979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151483891958844273453181277 56806459484566602544942979)
          ·
            refine ⟨85209689226849903817414469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56806459484566602544942979 85209689226849903817414469)
            ·
              refine ⟨15976816730034356965765213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85209689226849903817414469 15976816730034356965765213)
              ·
                refine ⟨5991306273762883862161955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15976816730034356965765213 5991306273762883862161955)
                ·
                  refine ⟨8986959410644325793242933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5991306273762883862161955 8986959410644325793242933)
                  ·
                    refine ⟨842527444747905543116525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8986959410644325793242933 842527444747905543116525)
                    ·
                      rfl

theorem cell23_4922449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 5].length) (baseStart_4922449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922449 prefixEnd_4922449 := by exact prefixLift 4922449
  have htrace : WordTrace (prefixWord ++ tailWord_4922449) baseStart_4922449 baseEnd_4922449 := by
    simpa [prefixWord, tailWord_4922449, baseEnd_4922449] using wordTrace_append hprefix tailTrace_4922449
  have hstable : (prefixWord ++ tailWord_4922449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922449).length < 2 ^ (prefixWord ++ tailWord_4922449).sum := by decide
  have hdescent : baseEnd_4922449 < baseStart_4922449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922456 : List Nat := [2, 1, 2, 2, 1, 3, 3, 2, 2, 3, 2]
def baseStart_4922456 : Nat := 118140960795 + 4922456 * 2 ^ 59
def prefixEnd_4922456 : Nat := 4983230072969 + 3 ^ 40 * 4922456 * 2
def baseEnd_4922456 : Nat := 2527585928608298101962043

theorem tailTrace_4922456 : CollatzResearch.WordTrace tailWord_4922456 prefixEnd_4922456 2527585928608298101962043 := by
  unfold tailWord_4922456
  simp only [CollatzResearch.WordTrace]
  refine ⟨89768359927395037699637611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119691146569860050266183481 89768359927395037699637611)
  ·
    refine ⟨134652539891092556549456417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89768359927395037699637611 134652539891092556549456417)
    ·
      refine ⟨100989404918319417412092313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134652539891092556549456417 100989404918319417412092313)
      ·
        refine ⟨75742053688739563059069235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100989404918319417412092313 75742053688739563059069235)
        ·
          refine ⟨113613080533109344588603853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75742053688739563059069235 113613080533109344588603853)
          ·
            refine ⟨42604905199916004220726445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113613080533109344588603853 42604905199916004220726445)
            ·
              refine ⟨15976839449968501582772417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42604905199916004220726445 15976839449968501582772417)
              ·
                refine ⟨11982629587476376187079313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15976839449968501582772417 11982629587476376187079313)
                ·
                  refine ⟨8986972190607282140309485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11982629587476376187079313 8986972190607282140309485)
                  ·
                    refine ⟨3370114571477730802616057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8986972190607282140309485 3370114571477730802616057)
                    ·
                      refine ⟨2527585928608298101962043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3370114571477730802616057 2527585928608298101962043)
                      ·
                        rfl

theorem cell23_4922456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 2, 3, 2].length) (baseStart_4922456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922456 prefixEnd_4922456 := by exact prefixLift 4922456
  have htrace : WordTrace (prefixWord ++ tailWord_4922456) baseStart_4922456 baseEnd_4922456 := by
    simpa [prefixWord, tailWord_4922456, baseEnd_4922456] using wordTrace_append hprefix tailTrace_4922456
  have hstable : (prefixWord ++ tailWord_4922456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922456).length < 2 ^ (prefixWord ++ tailWord_4922456).sum := by decide
  have hdescent : baseEnd_4922456 < baseStart_4922456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922469 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 3, 1, 4]
def baseStart_4922469 : Nat := 118140960795 + 4922469 * 2 ^ 59
def prefixEnd_4922469 : Nat := 4983230072969 + 3 ^ 40 * 4922469 * 2
def baseEnd_4922469 : Nat := 2527592603856806551099483

theorem tailTrace_4922469 : CollatzResearch.WordTrace tailWord_4922469 prefixEnd_4922469 2527592603856806551099483 := by
  unfold tailWord_4922469
  simp only [CollatzResearch.WordTrace]
  refine ⟨179537194003742978619498461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119691462669161985746332307 179537194003742978619498461)
  ·
    refine ⟨67326447751403616982311923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179537194003742978619498461 67326447751403616982311923)
    ·
      refine ⟨100989671627105425473467885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67326447751403616982311923 100989671627105425473467885)
      ·
        refine ⟨37871126860164534552550457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100989671627105425473467885 37871126860164534552550457)
        ·
          refine ⟨28403345145123400914412843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37871126860164534552550457 28403345145123400914412843)
          ·
            refine ⟨42605017717685101371619265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28403345145123400914412843 42605017717685101371619265)
            ·
              refine ⟨31953763288263826028714449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42605017717685101371619265 31953763288263826028714449)
              ·
                refine ⟨23965322466197869521535837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31953763288263826028714449 23965322466197869521535837)
                ·
                  refine ⟨8986995924824201070575939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23965322466197869521535837 8986995924824201070575939)
                  ·
                    refine ⟨13480493887236301605863909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8986995924824201070575939 13480493887236301605863909)
                    ·
                      refine ⟨2527592603856806551099483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13480493887236301605863909 2527592603856806551099483)
                      ·
                        rfl

theorem cell23_4922469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_4922469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922469 prefixEnd_4922469 := by exact prefixLift 4922469
  have htrace : WordTrace (prefixWord ++ tailWord_4922469) baseStart_4922469 baseEnd_4922469 := by
    simpa [prefixWord, tailWord_4922469, baseEnd_4922469] using wordTrace_append hprefix tailTrace_4922469
  have hstable : (prefixWord ++ tailWord_4922469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922469).length < 2 ^ (prefixWord ++ tailWord_4922469).sum := by decide
  have hdescent : baseEnd_4922469 < baseStart_4922469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922486 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_4922486 : Nat := 118140960795 + 4922486 * 2 ^ 59
def prefixEnd_4922486 : Nat := 4983230072969 + 3 ^ 40 * 4922486 * 2
def baseEnd_4922486 : Nat := 2527601333027932984586905

theorem tailTrace_4922486 : CollatzResearch.WordTrace tailWord_4922486 prefixEnd_4922486 2527601333027932984586905 := by
  unfold tailWord_4922486
  simp only [CollatzResearch.WordTrace]
  refine ⟨11221113377792586907679207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119691876029787593681911541 11221113377792586907679207)
  ·
    refine ⟨16831670066688880361518811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11221113377792586907679207 16831670066688880361518811)
    ·
      refine ⟨25247505100033320542278217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16831670066688880361518811 25247505100033320542278217)
      ·
        refine ⟨18935628825024990406708663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25247505100033320542278217 18935628825024990406708663)
        ·
          refine ⟨28403443237537485610062995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18935628825024990406708663 28403443237537485610062995)
          ·
            refine ⟨42605164856306228415094493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28403443237537485610062995 42605164856306228415094493)
            ·
              refine ⟨15976936821114835655660435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42605164856306228415094493 15976936821114835655660435)
              ·
                refine ⟨23965405231672253483490653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15976936821114835655660435 23965405231672253483490653)
                ·
                  refine ⟨8987026961877095056308995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23965405231672253483490653 8987026961877095056308995)
                  ·
                    refine ⟨13480540442815642584463493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8987026961877095056308995 13480540442815642584463493)
                    ·
                      refine ⟨2527601333027932984586905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13480540442815642584463493 2527601333027932984586905)
                      ·
                        rfl

theorem cell23_4922486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_4922486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922486 prefixEnd_4922486 := by exact prefixLift 4922486
  have htrace : WordTrace (prefixWord ++ tailWord_4922486) baseStart_4922486 baseEnd_4922486 := by
    simpa [prefixWord, tailWord_4922486, baseEnd_4922486] using wordTrace_append hprefix tailTrace_4922486
  have hstable : (prefixWord ++ tailWord_4922486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922486).length < 2 ^ (prefixWord ++ tailWord_4922486).sum := by decide
  have hdescent : baseEnd_4922486 < baseStart_4922486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922492 : List Nat := [2, 2, 2, 1, 1, 3, 1, 11]
def baseStart_4922492 : Nat := 118140960795 + 4922492 * 2 ^ 59
def prefixEnd_4922492 : Nat := 4983230072969 + 3 ^ 40 * 4922492 * 2
def baseEnd_4922492 : Nat := 93614978293031850411551

theorem tailTrace_4922492 : CollatzResearch.WordTrace tailWord_4922492 prefixEnd_4922492 93614978293031850411551 := by
  unfold tailWord_4922492
  simp only [CollatzResearch.WordTrace]
  refine ⟨89769016441329826773792865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119692021921773102365057153 89769016441329826773792865)
  ·
    refine ⟨67326762330997370080344649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89769016441329826773792865 67326762330997370080344649)
    ·
      refine ⟨50495071748248027560258487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67326762330997370080344649 50495071748248027560258487)
      ·
        refine ⟨75742607622372041340387731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50495071748248027560258487 75742607622372041340387731)
        ·
          refine ⟨113613911433558062010581597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75742607622372041340387731 113613911433558062010581597)
          ·
            refine ⟨42605216787584273253968099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113613911433558062010581597 42605216787584273253968099)
            ·
              refine ⟨63907825181376409880952149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42605216787584273253968099 63907825181376409880952149)
              ·
                refine ⟨93614978293031850411551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 63907825181376409880952149 93614978293031850411551)
                ·
                  rfl

theorem cell23_4922492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 11].length) (baseStart_4922492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922492 prefixEnd_4922492 := by exact prefixLift 4922492
  have htrace : WordTrace (prefixWord ++ tailWord_4922492) baseStart_4922492 baseEnd_4922492 := by
    simpa [prefixWord, tailWord_4922492, baseEnd_4922492] using wordTrace_append hprefix tailTrace_4922492
  have hstable : (prefixWord ++ tailWord_4922492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922492).length < 2 ^ (prefixWord ++ tailWord_4922492).sum := by decide
  have hdescent : baseEnd_4922492 < baseStart_4922492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922499 : List Nat := [1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 4]
def baseStart_4922499 : Nat := 118140960795 + 4922499 * 2 ^ 59
def prefixEnd_4922499 : Nat := 4983230072969 + 3 ^ 40 * 4922499 * 2
def baseEnd_4922499 : Nat := 2527608008276441433724345

theorem tailTrace_4922499 : CollatzResearch.WordTrace tailWord_4922499 prefixEnd_4922499 2527608008276441433724345 := by
  unfold tailWord_4922499
  simp only [CollatzResearch.WordTrace]
  refine ⟨179538288193634293743090551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119692192129089529162060367 179538288193634293743090551)
  ·
    refine ⟨269307432290451440614635827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179538288193634293743090551 269307432290451440614635827)
    ·
      refine ⟨403961148435677160921953741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269307432290451440614635827 403961148435677160921953741)
      ·
        refine ⟨151485430663378935345732653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 403961148435677160921953741 151485430663378935345732653)
        ·
          refine ⟨56807036498767100754649745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151485430663378935345732653 56807036498767100754649745)
          ·
            refine ⟨42605277374075325565987309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56807036498767100754649745 42605277374075325565987309)
            ·
              refine ⟨15976979015278247087245241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42605277374075325565987309 15976979015278247087245241)
              ·
                refine ⟨11982734261458685315433931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15976979015278247087245241 11982734261458685315433931)
                ·
                  refine ⟨17974101392188027973150897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11982734261458685315433931 17974101392188027973150897)
                  ·
                    refine ⟨13480576044141020979863173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17974101392188027973150897 13480576044141020979863173)
                    ·
                      refine ⟨2527608008276441433724345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13480576044141020979863173 2527608008276441433724345)
                      ·
                        rfl

theorem cell23_4922499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_4922499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922499 prefixEnd_4922499 := by exact prefixLift 4922499
  have htrace : WordTrace (prefixWord ++ tailWord_4922499) baseStart_4922499 baseEnd_4922499 := by
    simpa [prefixWord, tailWord_4922499, baseEnd_4922499] using wordTrace_append hprefix tailTrace_4922499
  have hstable : (prefixWord ++ tailWord_4922499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922499).length < 2 ^ (prefixWord ++ tailWord_4922499).sum := by decide
  have hdescent : baseEnd_4922499 < baseStart_4922499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922512 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 6]
def baseStart_4922512 : Nat := 118140960795 + 4922512 * 2 ^ 59
def prefixEnd_4922512 : Nat := 4983230072969 + 3 ^ 40 * 4922512 * 2
def baseEnd_4922512 : Nat := 2527614683524949882861785

theorem tailTrace_4922512 : CollatzResearch.WordTrace tailWord_4922512 prefixEnd_4922512 2527614683524949882861785 := by
  unfold tailWord_4922512
  simp only [CollatzResearch.WordTrace]
  refine ⟨89769381171293598481656895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119692508228391464642209193 89769381171293598481656895)
  ·
    refine ⟨134654071756940397722485343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89769381171293598481656895 134654071756940397722485343)
    ·
      refine ⟨201981107635410596583728015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134654071756940397722485343 201981107635410596583728015)
      ·
        refine ⟨302971661453115894875592023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201981107635410596583728015 302971661453115894875592023)
        ·
          refine ⟨454457492179673842313388035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302971661453115894875592023 454457492179673842313388035)
          ·
            refine ⟨681686238269510763470082053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454457492179673842313388035 681686238269510763470082053)
            ·
              refine ⟨127816169675533268150640385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 681686238269510763470082053 127816169675533268150640385)
              ·
                refine ⟨95862127256649951112980289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127816169675533268150640385 95862127256649951112980289)
                ·
                  refine ⟨71896595442487463334735217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95862127256649951112980289 71896595442487463334735217)
                  ·
                    refine ⟨53922446581865597501051413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71896595442487463334735217 53922446581865597501051413)
                    ·
                      refine ⟨2527614683524949882861785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53922446581865597501051413 2527614683524949882861785)
                      ·
                        rfl

theorem cell23_4922512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_4922512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922512 prefixEnd_4922512 := by exact prefixLift 4922512
  have htrace : WordTrace (prefixWord ++ tailWord_4922512) baseStart_4922512 baseEnd_4922512 := by
    simpa [prefixWord, tailWord_4922512, baseEnd_4922512] using wordTrace_append hprefix tailTrace_4922512
  have hstable : (prefixWord ++ tailWord_4922512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922512).length < 2 ^ (prefixWord ++ tailWord_4922512).sum := by decide
  have hdescent : baseEnd_4922512 < baseStart_4922512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922526 : List Nat := [4, 3, 1, 1, 2, 1, 3, 8]
def baseStart_4922526 : Nat := 118140960795 + 4922526 * 2 ^ 59
def prefixEnd_4922526 : Nat := 4983230072969 + 3 ^ 40 * 4922526 * 2
def baseEnd_4922526 : Nat := 93615624898300475114323

theorem tailTrace_4922526 : CollatzResearch.WordTrace tailWord_4922526 prefixEnd_4922526 93615624898300475114323 := by
  unfold tailWord_4922526
  simp only [CollatzResearch.WordTrace]
  refine ⟨22442409120567059669290429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119692848643024318236215621 22442409120567059669290429)
  ·
    refine ⟨8415903420212647375983911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22442409120567059669290429 8415903420212647375983911)
    ·
      refine ⟨12623855130318971063975867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8415903420212647375983911 12623855130318971063975867)
      ·
        refine ⟨18935782695478456595963801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12623855130318971063975867 18935782695478456595963801)
        ·
          refine ⟨14201837021608842446972851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18935782695478456595963801 14201837021608842446972851)
          ·
            refine ⟨21302755532413263670459277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14201837021608842446972851 21302755532413263670459277)
            ·
              refine ⟨7988533324654973876422229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21302755532413263670459277 7988533324654973876422229)
              ·
                refine ⟨93615624898300475114323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7988533324654973876422229 93615624898300475114323)
                ·
                  rfl

theorem cell23_4922526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 8].length) (baseStart_4922526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922526 prefixEnd_4922526 := by exact prefixLift 4922526
  have htrace : WordTrace (prefixWord ++ tailWord_4922526) baseStart_4922526 baseEnd_4922526 := by
    simpa [prefixWord, tailWord_4922526, baseEnd_4922526] using wordTrace_append hprefix tailTrace_4922526
  have hstable : (prefixWord ++ tailWord_4922526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922526).length < 2 ^ (prefixWord ++ tailWord_4922526).sum := by decide
  have hdescent : baseEnd_4922526 < baseStart_4922526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922570 : List Nat := [3, 1, 2, 1, 3, 4, 1, 2, 2, 1, 3]
def baseStart_4922570 : Nat := 118140960795 + 4922570 * 2 ^ 59
def prefixEnd_4922570 : Nat := 4983230072969 + 3 ^ 40 * 4922570 * 2
def baseEnd_4922570 : Nat := 2527644465402910655936519

theorem tailTrace_4922570 : CollatzResearch.WordTrace tailWord_4922570 prefixEnd_4922570 2527644465402910655936519 := by
  unfold tailWord_4922570
  simp only [CollatzResearch.WordTrace]
  refine ⟨44885219444094268217231291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119693918517584715245950109 44885219444094268217231291)
  ·
    refine ⟨67327829166141402325846937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44885219444094268217231291 67327829166141402325846937)
    ·
      refine ⟨50495871874606051744385203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67327829166141402325846937 50495871874606051744385203)
      ·
        refine ⟨75743807811909077616577805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50495871874606051744385203 75743807811909077616577805)
        ·
          refine ⟨28403927929465904106216677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75743807811909077616577805 28403927929465904106216677)
          ·
            refine ⟨5325736486774857019915627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28403927929465904106216677 5325736486774857019915627)
            ·
              refine ⟨7988604730162285529873441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5325736486774857019915627 7988604730162285529873441)
              ·
                refine ⟨5991453547621714147405081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7988604730162285529873441 5991453547621714147405081)
                ·
                  refine ⟨4493590160716285610553811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5991453547621714147405081 4493590160716285610553811)
                  ·
                    refine ⟨6740385241074428415830717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4493590160716285610553811 6740385241074428415830717)
                    ·
                      refine ⟨2527644465402910655936519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6740385241074428415830717 2527644465402910655936519)
                      ·
                        rfl

theorem cell23_4922570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_4922570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922570 prefixEnd_4922570 := by exact prefixLift 4922570
  have htrace : WordTrace (prefixWord ++ tailWord_4922570) baseStart_4922570 baseEnd_4922570 := by
    simpa [prefixWord, tailWord_4922570, baseEnd_4922570] using wordTrace_append hprefix tailTrace_4922570
  have hstable : (prefixWord ++ tailWord_4922570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922570).length < 2 ^ (prefixWord ++ tailWord_4922570).sum := by decide
  have hdescent : baseEnd_4922570 < baseStart_4922570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922593 : List Nat := [1, 2, 3, 1, 3, 2, 3, 1, 1, 4, 2]
def baseStart_4922593 : Nat := 118140960795 + 4922593 * 2 ^ 59
def prefixEnd_4922593 : Nat := 4983230072969 + 3 ^ 40 * 4922593 * 2
def baseEnd_4922593 : Nat := 2527656275457964065948913

theorem tailTrace_4922593 : CollatzResearch.WordTrace tailWord_4922593 prefixEnd_4922593 2527656275457964065948913 := by
  unfold tailWord_4922593
  simp only [CollatzResearch.WordTrace]
  refine ⟨179541716655293747797012433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119694477770195831864674955 179541716655293747797012433)
  ·
    refine ⟨134656287491470310847759325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179541716655293747797012433 134656287491470310847759325)
    ·
      refine ⟨50496107809301366567909747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134656287491470310847759325 50496107809301366567909747)
      ·
        refine ⟨75744161713952049851864621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50496107809301366567909747 75744161713952049851864621)
        ·
          refine ⟨28404060642732018694449233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75744161713952049851864621 28404060642732018694449233)
          ·
            refine ⟨21303045482049014020836925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28404060642732018694449233 21303045482049014020836925)
            ·
              refine ⟨7988642055768380257813847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21303045482049014020836925 7988642055768380257813847)
              ·
                refine ⟨11982963083652570386720771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7988642055768380257813847 11982963083652570386720771)
                ·
                  refine ⟨17974444625478855580081157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11982963083652570386720771 17974444625478855580081157)
                  ·
                    refine ⟨3370208367277285421265217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17974444625478855580081157 3370208367277285421265217)
                    ·
                      refine ⟨2527656275457964065948913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3370208367277285421265217 2527656275457964065948913)
                      ·
                        rfl

theorem cell23_4922593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 4, 2].length) (baseStart_4922593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922593 prefixEnd_4922593 := by exact prefixLift 4922593
  have htrace : WordTrace (prefixWord ++ tailWord_4922593) baseStart_4922593 baseEnd_4922593 := by
    simpa [prefixWord, tailWord_4922593, baseEnd_4922593] using wordTrace_append hprefix tailTrace_4922593
  have hstable : (prefixWord ++ tailWord_4922593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922593).length < 2 ^ (prefixWord ++ tailWord_4922593).sum := by decide
  have hdescent : baseEnd_4922593 < baseStart_4922593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4922633 : List Nat := [1, 2, 1, 1, 3, 3, 5, 2, 5]
def baseStart_4922633 : Nat := 118140960795 + 4922633 * 2 ^ 59
def prefixEnd_4922633 : Nat := 4983230072969 + 3 ^ 40 * 4922633 * 2
def baseEnd_4922633 : Nat := 280852979409349323272081

theorem tailTrace_4922633 : CollatzResearch.WordTrace tailWord_4922633 prefixEnd_4922633 280852979409349323272081 := by
  unfold tailWord_4922633
  simp only [CollatzResearch.WordTrace]
  refine ⟨179543175575148834628468553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119695450383432556418979035 179543175575148834628468553)
  ·
    refine ⟨134657381681361625971351415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179543175575148834628468553 134657381681361625971351415)
    ·
      refine ⟨201986072522042438957027123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134657381681361625971351415 201986072522042438957027123)
      ·
        refine ⟨302979108783063658435540685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201986072522042438957027123 302979108783063658435540685)
        ·
          refine ⟨113617165793648871913327757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 302979108783063658435540685 113617165793648871913327757)
          ·
            refine ⟨42606437172618326967497909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113617165793648871913327757 42606437172618326967497909)
            ·
              refine ⟨3994353484932968153202929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42606437172618326967497909 3994353484932968153202929)
              ·
                refine ⟨2995765113699726114902197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3994353484932968153202929 2995765113699726114902197)
                ·
                  refine ⟨280852979409349323272081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2995765113699726114902197 280852979409349323272081)
                  ·
                    rfl

theorem cell23_4922633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 5].length) (baseStart_4922633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4922633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4922633 prefixEnd_4922633 := by exact prefixLift 4922633
  have htrace : WordTrace (prefixWord ++ tailWord_4922633) baseStart_4922633 baseEnd_4922633 := by
    simpa [prefixWord, tailWord_4922633, baseEnd_4922633] using wordTrace_append hprefix tailTrace_4922633
  have hstable : (prefixWord ++ tailWord_4922633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4922633).length < 2 ^ (prefixWord ++ tailWord_4922633).sum := by decide
  have hdescent : baseEnd_4922633 < baseStart_4922633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4922633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
