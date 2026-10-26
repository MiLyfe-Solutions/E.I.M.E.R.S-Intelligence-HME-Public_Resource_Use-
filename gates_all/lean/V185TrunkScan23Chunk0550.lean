import V185TrunkScan23Chunk0549

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3251211 : List Nat := [1, 1, 1, 1, 6, 2, 3, 2, 1, 3, 2]
def baseStart_3251211 : Nat := 118140960795 + 3251211 * 2 ^ 59
def prefixEnd_3251211 : Nat := 4983230072969 + 3 ^ 40 * 3251211 * 2
def baseEnd_3251211 : Nat := 1669433952184984355710459

theorem tailTrace_3251211 : CollatzResearch.WordTrace tailWord_3251211 prefixEnd_3251211 1669433952184984355710459 := by
  unfold tailWord_3251211
  simp only [CollatzResearch.WordTrace]
  refine ⟨118581407024425284477193487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79054271349616856318128991 118581407024425284477193487)
  ·
    refine ⟨177872110536637926715790231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118581407024425284477193487 177872110536637926715790231)
    ·
      refine ⟨266808165804956890073685347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177872110536637926715790231 266808165804956890073685347)
      ·
        refine ⟨400212248707435335110528021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266808165804956890073685347 400212248707435335110528021)
        ·
          refine ⟨18759949158161031333306001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 400212248707435335110528021 18759949158161031333306001)
          ·
            refine ⟨14069961868620773499979501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18759949158161031333306001 14069961868620773499979501)
            ·
              refine ⟨5276235700732790062492313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14069961868620773499979501 5276235700732790062492313)
              ·
                refine ⟨3957176775549592546869235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5276235700732790062492313 3957176775549592546869235)
                ·
                  refine ⟨5935765163324388820303853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3957176775549592546869235 5935765163324388820303853)
                  ·
                    refine ⟨2225911936246645807613945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5935765163324388820303853 2225911936246645807613945)
                    ·
                      refine ⟨1669433952184984355710459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2225911936246645807613945 1669433952184984355710459)
                      ·
                        rfl

theorem cell23_3251211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 3, 2].length) (baseStart_3251211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251211 prefixEnd_3251211 := by exact prefixLift 3251211
  have htrace : WordTrace (prefixWord ++ tailWord_3251211) baseStart_3251211 baseEnd_3251211 := by
    simpa [prefixWord, tailWord_3251211, baseEnd_3251211] using wordTrace_append hprefix tailTrace_3251211
  have hstable : (prefixWord ++ tailWord_3251211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251211).length < 2 ^ (prefixWord ++ tailWord_3251211).sum := by decide
  have hdescent : baseEnd_3251211 < baseStart_3251211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251224 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 3, 4, 2]
def baseStart_3251224 : Nat := 118140960795 + 3251224 * 2 ^ 59
def prefixEnd_3251224 : Nat := 4983230072969 + 3 ^ 40 * 3251224 * 2
def baseEnd_3251224 : Nat := 1669440627433492804847899

theorem tailTrace_3251224 : CollatzResearch.WordTrace tailWord_3251224 prefixEnd_3251224 1669440627433492804847899 := by
  unfold tailWord_3251224
  simp only [CollatzResearch.WordTrace]
  refine ⟨59290940586689093848708363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79054587448918791798277817 59290940586689093848708363)
  ·
    refine ⟨88936410880033640773062545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59290940586689093848708363 88936410880033640773062545)
    ·
      refine ⟨66702308160025230579796909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88936410880033640773062545 66702308160025230579796909)
      ·
        refine ⟨25013365560009461467423841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66702308160025230579796909 25013365560009461467423841)
        ·
          refine ⟨18760024170007096100567881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25013365560009461467423841 18760024170007096100567881)
          ·
            refine ⟨14070018127505322075425911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18760024170007096100567881 14070018127505322075425911)
            ·
              refine ⟨21105027191257983113138867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14070018127505322075425911 21105027191257983113138867)
              ·
                refine ⟨31657540786886974669708301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21105027191257983113138867 31657540786886974669708301)
                ·
                  refine ⟨11871577795082615501140613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31657540786886974669708301 11871577795082615501140613)
                  ·
                    refine ⟨2225920836577990406463865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11871577795082615501140613 2225920836577990406463865)
                    ·
                      refine ⟨1669440627433492804847899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2225920836577990406463865 1669440627433492804847899)
                      ·
                        rfl

theorem cell23_3251224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_3251224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251224 prefixEnd_3251224 := by exact prefixLift 3251224
  have htrace : WordTrace (prefixWord ++ tailWord_3251224) baseStart_3251224 baseEnd_3251224 := by
    simpa [prefixWord, tailWord_3251224, baseEnd_3251224] using wordTrace_append hprefix tailTrace_3251224
  have hstable : (prefixWord ++ tailWord_3251224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251224).length < 2 ^ (prefixWord ++ tailWord_3251224).sum := by decide
  have hdescent : baseEnd_3251224 < baseStart_3251224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251237 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 2, 2, 4]
def baseStart_3251237 : Nat := 118140960795 + 3251237 * 2 ^ 59
def prefixEnd_3251237 : Nat := 4983230072969 + 3 ^ 40 * 3251237 * 2
def baseEnd_3251237 : Nat := 1669447302682001253985339

theorem tailTrace_3251237 : CollatzResearch.WordTrace tailWord_3251237 prefixEnd_3251237 1669447302682001253985339 := by
  unfold tailWord_3251237
  simp only [CollatzResearch.WordTrace]
  refine ⟨118582355322331090917639965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79054903548220727278426643 118582355322331090917639965)
  ·
    refine ⟨44468383245874159094114987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118582355322331090917639965 44468383245874159094114987)
    ·
      refine ⟨66702574868811238641172481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44468383245874159094114987 66702574868811238641172481)
      ·
        refine ⟨50026931151608428980879361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66702574868811238641172481 50026931151608428980879361)
        ·
          refine ⟨37520198363706321735659521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50026931151608428980879361 37520198363706321735659521)
          ·
            refine ⟨28140148772779741301744641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37520198363706321735659521 28140148772779741301744641)
            ·
              refine ⟨21105111579584805976308481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28140148772779741301744641 21105111579584805976308481)
              ·
                refine ⟨15828833684688604482231361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21105111579584805976308481 15828833684688604482231361)
                ·
                  refine ⟨11871625263516453361673521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15828833684688604482231361 11871625263516453361673521)
                  ·
                    refine ⟨8903718947637340021255141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11871625263516453361673521 8903718947637340021255141)
                    ·
                      refine ⟨1669447302682001253985339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8903718947637340021255141 1669447302682001253985339)
                      ·
                        rfl

theorem cell23_3251237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_3251237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251237 prefixEnd_3251237 := by exact prefixLift 3251237
  have htrace : WordTrace (prefixWord ++ tailWord_3251237) baseStart_3251237 baseEnd_3251237 := by
    simpa [prefixWord, tailWord_3251237, baseEnd_3251237] using wordTrace_append hprefix tailTrace_3251237
  have hstable : (prefixWord ++ tailWord_3251237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251237).length < 2 ^ (prefixWord ++ tailWord_3251237).sum := by decide
  have hdescent : baseEnd_3251237 < baseStart_3251237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251254 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_3251254 : Nat := 118140960795 + 3251254 * 2 ^ 59
def prefixEnd_3251254 : Nat := 4983230072969 + 3 ^ 40 * 3251254 * 2
def baseEnd_3251254 : Nat := 1669456031853127687472761

theorem tailTrace_3251254 : CollatzResearch.WordTrace tailWord_3251254 prefixEnd_3251254 1669456031853127687472761 := by
  unfold tailWord_3251254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7411435960204343926313051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79055316908846335214005877 7411435960204343926313051)
  ·
    refine ⟨11117153940306515889469577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7411435960204343926313051 11117153940306515889469577)
    ·
      refine ⟨8337865455229886917102183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11117153940306515889469577 8337865455229886917102183)
      ·
        refine ⟨12506798182844830375653275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8337865455229886917102183 12506798182844830375653275)
        ·
          refine ⟨18760197274267245563479913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12506798182844830375653275 18760197274267245563479913)
          ·
            refine ⟨14070147955700434172609935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18760197274267245563479913 14070147955700434172609935)
            ·
              refine ⟨21105221933550651258914903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14070147955700434172609935 21105221933550651258914903)
              ·
                refine ⟨31657832900325976888372355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21105221933550651258914903 31657832900325976888372355)
                ·
                  refine ⟨47486749350488965332558533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31657832900325976888372355 47486749350488965332558533)
                  ·
                    refine ⟨8903765503216680999854725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47486749350488965332558533 8903765503216680999854725)
                    ·
                      refine ⟨1669456031853127687472761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8903765503216680999854725 1669456031853127687472761)
                      ·
                        rfl

theorem cell23_3251254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_3251254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251254 prefixEnd_3251254 := by exact prefixLift 3251254
  have htrace : WordTrace (prefixWord ++ tailWord_3251254) baseStart_3251254 baseEnd_3251254 := by
    simpa [prefixWord, tailWord_3251254, baseEnd_3251254] using wordTrace_append hprefix tailTrace_3251254
  have hstable : (prefixWord ++ tailWord_3251254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251254).length < 2 ^ (prefixWord ++ tailWord_3251254).sum := by decide
  have hdescent : baseEnd_3251254 < baseStart_3251254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251324 : List Nat := [2, 2, 2, 1, 1, 3, 1, 4, 3, 4]
def baseStart_3251324 : Nat := 118140960795 + 3251324 * 2 ^ 59
def prefixEnd_3251324 : Nat := 4983230072969 + 3 ^ 40 * 3251324 * 2
def baseEnd_3251324 : Nat := 556497325166314137865813

theorem tailTrace_3251324 : CollatzResearch.WordTrace tailWord_3251324 prefixEnd_3251324 556497325166314137865813 := by
  unfold tailWord_3251324
  simp only [CollatzResearch.WordTrace]
  refine ⟨59292764236507952388028513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79057018982010603184038017 59292764236507952388028513)
  ·
    refine ⟨44469573177380964291021385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59292764236507952388028513 44469573177380964291021385)
    ·
      refine ⟨33352179883035723218266039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44469573177380964291021385 33352179883035723218266039)
      ·
        refine ⟨50028269824553584827399059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33352179883035723218266039 50028269824553584827399059)
        ·
          refine ⟨75042404736830377241098589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50028269824553584827399059 75042404736830377241098589)
          ·
            refine ⟨28140901776311391465411971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75042404736830377241098589 28140901776311391465411971)
            ·
              refine ⟨42211352664467087198117957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28140901776311391465411971 42211352664467087198117957)
              ·
                refine ⟨7914628624587578849647117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42211352664467087198117957 7914628624587578849647117)
                ·
                  refine ⟨2967985734220342068617669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7914628624587578849647117 2967985734220342068617669)
                  ·
                    refine ⟨556497325166314137865813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2967985734220342068617669 556497325166314137865813)
                    ·
                      rfl

theorem cell23_3251324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_3251324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251324 prefixEnd_3251324 := by exact prefixLift 3251324
  have htrace : WordTrace (prefixWord ++ tailWord_3251324) baseStart_3251324 baseEnd_3251324 := by
    simpa [prefixWord, tailWord_3251324, baseEnd_3251324] using wordTrace_append hprefix tailTrace_3251324
  have hstable : (prefixWord ++ tailWord_3251324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251324).length < 2 ^ (prefixWord ++ tailWord_3251324).sum := by decide
  have hdescent : baseEnd_3251324 < baseStart_3251324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251337 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 8]
def baseStart_3251337 : Nat := 118140960795 + 3251337 * 2 ^ 59
def prefixEnd_3251337 : Nat := 4983230072969 + 3 ^ 40 * 3251337 * 2
def baseEnd_3251337 : Nat := 185499850083050095859431

theorem tailTrace_3251337 : CollatzResearch.WordTrace tailWord_3251337 prefixEnd_3251337 185499850083050095859431 := by
  unfold tailWord_3251337
  simp only [CollatzResearch.WordTrace]
  refine ⟨118586002621968807996280265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79057335081312538664186843 118586002621968807996280265)
  ·
    refine ⟨88939501966476605997210199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118586002621968807996280265 88939501966476605997210199)
    ·
      refine ⟨133409252949714908995815299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88939501966476605997210199 133409252949714908995815299)
      ·
        refine ⟨200113879424572363493722949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133409252949714908995815299 200113879424572363493722949)
        ·
          refine ⟨37521352392107318155073053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 200113879424572363493722949 37521352392107318155073053)
          ·
            refine ⟨14070507147040244308152395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37521352392107318155073053 14070507147040244308152395)
            ·
              refine ⟨21105760720560366462228593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14070507147040244308152395 21105760720560366462228593)
              ·
                refine ⟨15829320540420274846671445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21105760720560366462228593 15829320540420274846671445)
                ·
                  refine ⟨185499850083050095859431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15829320540420274846671445 185499850083050095859431)
                  ·
                    rfl

theorem cell23_3251337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 8].length) (baseStart_3251337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251337 prefixEnd_3251337 := by exact prefixLift 3251337
  have htrace : WordTrace (prefixWord ++ tailWord_3251337) baseStart_3251337 baseEnd_3251337 := by
    simpa [prefixWord, tailWord_3251337, baseEnd_3251337] using wordTrace_append hprefix tailTrace_3251337
  have hstable : (prefixWord ++ tailWord_3251337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251337).length < 2 ^ (prefixWord ++ tailWord_3251337).sum := by decide
  have hdescent : baseEnd_3251337 < baseStart_3251337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251351 : List Nat := [1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 3]
def baseStart_3251351 : Nat := 118140960795 + 3251351 * 2 ^ 59
def prefixEnd_3251351 : Nat := 4983230072969 + 3 ^ 40 * 3251351 * 2
def baseEnd_3251351 : Nat := 1669505839476613807959815

theorem tailTrace_3251351 : CollatzResearch.WordTrace tailWord_3251351 prefixEnd_3251351 1669505839476613807959815 := by
  unfold tailWord_3251351
  simp only [CollatzResearch.WordTrace]
  refine ⟨118586513243918088387289907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79057675495945392258193271 118586513243918088387289907)
  ·
    refine ⟨177879769865877132580934861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118586513243918088387289907 177879769865877132580934861)
    ·
      refine ⟨66704913699703924717850573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177879769865877132580934861 66704913699703924717850573)
      ·
        refine ⟨25014342637388971769193965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66704913699703924717850573 25014342637388971769193965)
        ·
          refine ⟨9380378489020864413447737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25014342637388971769193965 9380378489020864413447737)
          ·
            refine ⟨7035283866765648310085803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9380378489020864413447737 7035283866765648310085803)
            ·
              refine ⟨10552925800148472465128705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7035283866765648310085803 10552925800148472465128705)
              ·
                refine ⟨7914694350111354348846529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10552925800148472465128705 7914694350111354348846529)
                ·
                  refine ⟨5936020762583515761634897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7914694350111354348846529 5936020762583515761634897)
                  ·
                    refine ⟨4452015571937636821226173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5936020762583515761634897 4452015571937636821226173)
                    ·
                      refine ⟨1669505839476613807959815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4452015571937636821226173 1669505839476613807959815)
                      ·
                        rfl

theorem cell23_3251351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_3251351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251351 prefixEnd_3251351 := by exact prefixLift 3251351
  have htrace : WordTrace (prefixWord ++ tailWord_3251351) baseStart_3251351 baseEnd_3251351 := by
    simpa [prefixWord, tailWord_3251351, baseEnd_3251351] using wordTrace_append hprefix tailTrace_3251351
  have hstable : (prefixWord ++ tailWord_3251351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251351).length < 2 ^ (prefixWord ++ tailWord_3251351).sum := by decide
  have hdescent : baseEnd_3251351 < baseStart_3251351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251354 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 8]
def baseStart_3251354 : Nat := 118140960795 + 3251354 * 2 ^ 59
def prefixEnd_3251354 : Nat := 4983230072969 + 3 ^ 40 * 3251354 * 2
def baseEnd_3251354 : Nat := 185500819990953032913589

theorem tailTrace_3251354 : CollatzResearch.WordTrace tailWord_3251354 prefixEnd_3251354 185500819990953032913589 := by
  unfold tailWord_3251354
  simp only [CollatzResearch.WordTrace]
  refine ⟨29646655665726804974912279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79057748441938146599766077 29646655665726804974912279)
  ·
    refine ⟨44469983498590207462368419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29646655665726804974912279 44469983498590207462368419)
    ·
      refine ⟨66704975247885311193552629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44469983498590207462368419 66704975247885311193552629)
      ·
        refine ⟨6253591429489247924395559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66704975247885311193552629 6253591429489247924395559)
        ·
          refine ⟨9380387144233871886593339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6253591429489247924395559 9380387144233871886593339)
          ·
            refine ⟨14070580716350807829890009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9380387144233871886593339 14070580716350807829890009)
            ·
              refine ⟨10552935537263105872417507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14070580716350807829890009 10552935537263105872417507)
              ·
                refine ⟨15829403305894658808626261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10552935537263105872417507 15829403305894658808626261)
                ·
                  refine ⟨185500819990953032913589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15829403305894658808626261 185500819990953032913589)
                  ·
                    rfl

theorem cell23_3251354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 8].length) (baseStart_3251354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251354 prefixEnd_3251354 := by exact prefixLift 3251354
  have htrace : WordTrace (prefixWord ++ tailWord_3251354) baseStart_3251354 baseEnd_3251354 := by
    simpa [prefixWord, tailWord_3251354, baseEnd_3251354] using wordTrace_append hprefix tailTrace_3251354
  have hstable : (prefixWord ++ tailWord_3251354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251354).length < 2 ^ (prefixWord ++ tailWord_3251354).sum := by decide
  have hdescent : baseEnd_3251354 < baseStart_3251354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251358 : List Nat := [4, 3, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_3251358 : Nat := 118140960795 + 3251358 * 2 ^ 59
def prefixEnd_3251358 : Nat := 4983230072969 + 3 ^ 40 * 3251358 * 2
def baseEnd_3251358 : Nat := 556503144613731760190761

theorem tailTrace_3251358 : CollatzResearch.WordTrace tailWord_3251358 prefixEnd_3251358 556503144613731760190761 := by
  unfold tailWord_3251358
  simp only [CollatzResearch.WordTrace]
  refine ⟨14823346069361591072849341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79057845703261819055196485 14823346069361591072849341)
  ·
    refine ⟨5558754776010596652318503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14823346069361591072849341 5558754776010596652318503)
    ·
      refine ⟨8338132164015894978477755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5558754776010596652318503 8338132164015894978477755)
      ·
        refine ⟨12507198246023842467716633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8338132164015894978477755 12507198246023842467716633)
        ·
          refine ⟨9380398684517881850787475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12507198246023842467716633 9380398684517881850787475)
          ·
            refine ⟨14070598026776822776181213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9380398684517881850787475 14070598026776822776181213)
            ·
              refine ⟨5276474260041308541067955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14070598026776822776181213 5276474260041308541067955)
              ·
                refine ⟨7914711390061962811601933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5276474260041308541067955 7914711390061962811601933)
                ·
                  refine ⟨2968016771273236054350725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7914711390061962811601933 2968016771273236054350725)
                  ·
                    refine ⟨556503144613731760190761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2968016771273236054350725 556503144613731760190761)
                    ·
                      rfl

theorem cell23_3251358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_3251358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251358 prefixEnd_3251358 := by exact prefixLift 3251358
  have htrace : WordTrace (prefixWord ++ tailWord_3251358) baseStart_3251358 baseEnd_3251358 := by
    simpa [prefixWord, tailWord_3251358, baseEnd_3251358] using wordTrace_append hprefix tailTrace_3251358
  have hstable : (prefixWord ++ tailWord_3251358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251358).length < 2 ^ (prefixWord ++ tailWord_3251358).sum := by decide
  have hdescent : baseEnd_3251358 < baseStart_3251358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251384 : List Nat := [2, 1, 2, 1, 2, 1, 2, 6, 1, 5]
def baseStart_3251384 : Nat := 118140960795 + 3251384 * 2 ^ 59
def prefixEnd_3251384 : Nat := 4983230072969 + 3 ^ 40 * 3251384 * 2
def baseEnd_3251384 : Nat := 556507594779404059615721

theorem tailTrace_3251384 : CollatzResearch.WordTrace tailWord_3251384 prefixEnd_3251384 556507594779404059615721 := by
  unfold tailWord_3251384
  simp only [CollatzResearch.WordTrace]
  refine ⟨59293858426399267511620603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79058477901865690015494137 59293858426399267511620603)
  ·
    refine ⟨88940787639598901267430905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59293858426399267511620603 88940787639598901267430905)
    ·
      refine ⟨66705590729699175950573179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88940787639598901267430905 66705590729699175950573179)
      ·
        refine ⟨100058386094548763925859769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66705590729699175950573179 100058386094548763925859769)
        ·
          refine ⟨75043789570911572944394827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100058386094548763925859769 75043789570911572944394827)
          ·
            refine ⟨112565684356367359416592241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75043789570911572944394827 112565684356367359416592241)
            ·
              refine ⟨84424263267275519562444181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112565684356367359416592241 84424263267275519562444181)
              ·
                refine ⟨3957387340653539979489571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84424263267275519562444181 3957387340653539979489571)
                ·
                  refine ⟨5936081010980309969234357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3957387340653539979489571 5936081010980309969234357)
                  ·
                    refine ⟨556507594779404059615721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5936081010980309969234357 556507594779404059615721)
                    ·
                      rfl

theorem cell23_3251384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 1, 5].length) (baseStart_3251384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251384 prefixEnd_3251384 := by exact prefixLift 3251384
  have htrace : WordTrace (prefixWord ++ tailWord_3251384) baseStart_3251384 baseEnd_3251384 := by
    simpa [prefixWord, tailWord_3251384, baseEnd_3251384] using wordTrace_append hprefix tailTrace_3251384
  have hstable : (prefixWord ++ tailWord_3251384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251384).length < 2 ^ (prefixWord ++ tailWord_3251384).sum := by decide
  have hdescent : baseEnd_3251384 < baseStart_3251384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251391 : List Nat := [1, 1, 2, 2, 2, 2, 3, 3, 2, 3, 2]
def baseStart_3251391 : Nat := 118140960795 + 3251391 * 2 ^ 59
def prefixEnd_3251391 : Nat := 4983230072969 + 3 ^ 40 * 3251391 * 2
def baseEnd_3251391 : Nat := 1669526378702793651459631

theorem tailTrace_3251391 : CollatzResearch.WordTrace tailWord_3251391 prefixEnd_3251391 1669526378702793651459631 := by
  unfold tailWord_3251391
  simp only [CollatzResearch.WordTrace]
  refine ⟨118587972163773175218746027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79058648109182116812497351 118587972163773175218746027)
  ·
    refine ⟨177881958245659762828119041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118587972163773175218746027 177881958245659762828119041)
    ·
      refine ⟨133411468684244822121089281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177881958245659762828119041 133411468684244822121089281)
      ·
        refine ⟨100058601513183616590816961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133411468684244822121089281 100058601513183616590816961)
        ·
          refine ⟨75043951134887712443112721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100058601513183616590816961 75043951134887712443112721)
          ·
            refine ⟨56282963351165784332334541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75043951134887712443112721 56282963351165784332334541)
            ·
              refine ⟨21106111256687169124625453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56282963351165784332334541 21106111256687169124625453)
              ·
                refine ⟨7914791721257688421734545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21106111256687169124625453 7914791721257688421734545)
                ·
                  refine ⟨5936093790943266316300909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7914791721257688421734545 5936093790943266316300909)
                  ·
                    refine ⟨2226035171603724868612841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5936093790943266316300909 2226035171603724868612841)
                    ·
                      refine ⟨1669526378702793651459631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2226035171603724868612841 1669526378702793651459631)
                      ·
                        rfl

theorem cell23_3251391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 3, 2].length) (baseStart_3251391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251391 prefixEnd_3251391 := by exact prefixLift 3251391
  have htrace : WordTrace (prefixWord ++ tailWord_3251391) baseStart_3251391 baseEnd_3251391 := by
    simpa [prefixWord, tailWord_3251391, baseEnd_3251391] using wordTrace_append hprefix tailTrace_3251391
  have hstable : (prefixWord ++ tailWord_3251391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251391).length < 2 ^ (prefixWord ++ tailWord_3251391).sum := by decide
  have hdescent : baseEnd_3251391 < baseStart_3251391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251405 : List Nat := [1, 6, 2, 2, 1, 1, 2, 2, 6]
def baseStart_3251405 : Nat := 118140960795 + 3251405 * 2 ^ 59
def prefixEnd_3251405 : Nat := 4983230072969 + 3 ^ 40 * 3251405 * 2
def baseEnd_3251405 : Nat := 185503729714661844076063

theorem tailTrace_3251405 : CollatzResearch.WordTrace tailWord_3251405 prefixEnd_3251405 185503729714661844076063 := by
  unfold tailWord_3251405
  simp only [CollatzResearch.WordTrace]
  refine ⟨118588482785722455609755669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79058988523814970406503779 118588482785722455609755669)
  ·
    refine ⟨5558835130580740106707297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 118588482785722455609755669 5558835130580740106707297)
    ·
      refine ⟨4169126347935555080030473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5558835130580740106707297 4169126347935555080030473)
      ·
        refine ⟨3126844760951666310022855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4169126347935555080030473 3126844760951666310022855)
        ·
          refine ⟨4690267141427499465034283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3126844760951666310022855 4690267141427499465034283)
          ·
            refine ⟨7035400712141249197551425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4690267141427499465034283 7035400712141249197551425)
            ·
              refine ⟨5276550534105936898163569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7035400712141249197551425 5276550534105936898163569)
              ·
                refine ⟨3957412900579452673622677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5276550534105936898163569 3957412900579452673622677)
                ·
                  refine ⟨185503729714661844076063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3957412900579452673622677 185503729714661844076063)
                  ·
                    rfl

theorem cell23_3251405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_3251405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251405 prefixEnd_3251405 := by exact prefixLift 3251405
  have htrace : WordTrace (prefixWord ++ tailWord_3251405) baseStart_3251405 baseEnd_3251405 := by
    simpa [prefixWord, tailWord_3251405, baseEnd_3251405] using wordTrace_append hprefix tailTrace_3251405
  have hstable : (prefixWord ++ tailWord_3251405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251405).length < 2 ^ (prefixWord ++ tailWord_3251405).sum := by decide
  have hdescent : baseEnd_3251405 < baseStart_3251405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251415 : List Nat := [1, 1, 3, 2, 1, 2, 6, 2, 1, 1, 3]
def baseStart_3251415 : Nat := 118140960795 + 3251415 * 2 ^ 59
def prefixEnd_3251415 : Nat := 4983230072969 + 3 ^ 40 * 3251415 * 2
def baseEnd_3251415 : Nat := 1669538702238501557559521

theorem tailTrace_3251415 : CollatzResearch.WordTrace tailWord_3251415 prefixEnd_3251415 1669538702238501557559521 := by
  unfold tailWord_3251415
  simp only [CollatzResearch.WordTrace]
  refine ⟨118588847515686227317619699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79059231677124151545079799 118588847515686227317619699)
  ·
    refine ⟨177883271273529340976429549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118588847515686227317619699 177883271273529340976429549)
    ·
      refine ⟨66706226727573502866161081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177883271273529340976429549 66706226727573502866161081)
      ·
        refine ⟨50029670045680127149620811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66706226727573502866161081 50029670045680127149620811)
        ·
          refine ⟨75044505068520190724431217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50029670045680127149620811 75044505068520190724431217)
          ·
            refine ⟨56283378801390143043323413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75044505068520190724431217 56283378801390143043323413)
            ·
              refine ⟨2638283381315162955155785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56283378801390143043323413 2638283381315162955155785)
              ·
                refine ⟨1978712535986372216366839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2638283381315162955155785 1978712535986372216366839)
                ·
                  refine ⟨2968068803979558324550259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1978712535986372216366839 2968068803979558324550259)
                  ·
                    refine ⟨4452103205969337486825389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2968068803979558324550259 4452103205969337486825389)
                    ·
                      refine ⟨1669538702238501557559521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4452103205969337486825389 1669538702238501557559521)
                      ·
                        rfl

theorem cell23_3251415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 1, 1, 3].length) (baseStart_3251415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251415 prefixEnd_3251415 := by exact prefixLift 3251415
  have htrace : WordTrace (prefixWord ++ tailWord_3251415) baseStart_3251415 baseEnd_3251415 := by
    simpa [prefixWord, tailWord_3251415, baseEnd_3251415] using wordTrace_append hprefix tailTrace_3251415
  have hstable : (prefixWord ++ tailWord_3251415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251415).length < 2 ^ (prefixWord ++ tailWord_3251415).sum := by decide
  have hdescent : baseEnd_3251415 < baseStart_3251415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251438 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 5, 2, 2]
def baseStart_3251438 : Nat := 118140960795 + 3251438 * 2 ^ 59
def prefixEnd_3251438 : Nat := 4983230072969 + 3 ^ 40 * 3251438 * 2
def baseEnd_3251438 : Nat := 1669550512293554967571915

theorem tailTrace_3251438 : CollatzResearch.WordTrace tailWord_3251438 prefixEnd_3251438 1669550512293554967571915 := by
  unfold tailWord_3251438
  simp only [CollatzResearch.WordTrace]
  refine ⟨14823710799325362780713371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79059790929735268163804645 14823710799325362780713371)
  ·
    refine ⟨22235566198988044171070057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14823710799325362780713371 22235566198988044171070057)
    ·
      refine ⟨16676674649241033128302543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22235566198988044171070057 16676674649241033128302543)
      ·
        refine ⟨25015011973861549692453815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16676674649241033128302543 25015011973861549692453815)
        ·
          refine ⟨37522517960792324538680723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25015011973861549692453815 37522517960792324538680723)
          ·
            refine ⟨56283776941188486808021085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37522517960792324538680723 56283776941188486808021085)
            ·
              refine ⟨21106416352945682553007907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56283776941188486808021085 21106416352945682553007907)
              ·
                refine ⟨31659624529418523829511861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21106416352945682553007907 31659624529418523829511861)
                ·
                  refine ⟨2968089799632986609016737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31659624529418523829511861 2968089799632986609016737)
                  ·
                    refine ⟨2226067349724739956762553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2968089799632986609016737 2226067349724739956762553)
                    ·
                      refine ⟨1669550512293554967571915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2226067349724739956762553 1669550512293554967571915)
                      ·
                        rfl

theorem cell23_3251438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_3251438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251438 prefixEnd_3251438 := by exact prefixLift 3251438
  have htrace : WordTrace (prefixWord ++ tailWord_3251438) baseStart_3251438 baseEnd_3251438 := by
    simpa [prefixWord, tailWord_3251438, baseEnd_3251438] using wordTrace_append hprefix tailTrace_3251438
  have hstable : (prefixWord ++ tailWord_3251438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251438).length < 2 ^ (prefixWord ++ tailWord_3251438).sum := by decide
  have hdescent : baseEnd_3251438 < baseStart_3251438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251441 : List Nat := [1, 2, 2, 2, 2, 1, 1, 6, 1, 2, 3]
def baseStart_3251441 : Nat := 118140960795 + 3251441 * 2 ^ 59
def prefixEnd_3251441 : Nat := 4983230072969 + 3 ^ 40 * 3251441 * 2
def baseEnd_3251441 : Nat := 1669552052735518455834401

theorem tailTrace_3251441 : CollatzResearch.WordTrace tailWord_3251441 prefixEnd_3251441 1669552052735518455834401 := by
  unfold tailWord_3251441
  simp only [CollatzResearch.WordTrace]
  refine ⟨118589795813592033758066177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79059863875728022505377451 118589795813592033758066177)
  ·
    refine ⟨88942346860194025318549633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118589795813592033758066177 88942346860194025318549633)
    ·
      refine ⟨66706760145145518988912225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88942346860194025318549633 66706760145145518988912225)
      ·
        refine ⟨50030070108859139241684169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66706760145145518988912225 50030070108859139241684169)
        ·
          refine ⟨37522552581644354431263127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50030070108859139241684169 37522552581644354431263127)
          ·
            refine ⟨56283828872466531646894691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37522552581644354431263127 56283828872466531646894691)
            ·
              refine ⟨84425743308699797470342037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56283828872466531646894691 84425743308699797470342037)
              ·
                refine ⟨3957456717595303006422283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84425743308699797470342037 3957456717595303006422283)
                ·
                  refine ⟨5936185076392954509633425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3957456717595303006422283 5936185076392954509633425)
                  ·
                    refine ⟨4452138807294715882225069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5936185076392954509633425 4452138807294715882225069)
                    ·
                      refine ⟨1669552052735518455834401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4452138807294715882225069 1669552052735518455834401)
                      ·
                        rfl

theorem cell23_3251441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_3251441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251441 prefixEnd_3251441 := by exact prefixLift 3251441
  have htrace : WordTrace (prefixWord ++ tailWord_3251441) baseStart_3251441 baseEnd_3251441 := by
    simpa [prefixWord, tailWord_3251441, baseEnd_3251441] using wordTrace_append hprefix tailTrace_3251441
  have hstable : (prefixWord ++ tailWord_3251441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251441).length < 2 ^ (prefixWord ++ tailWord_3251441).sum := by decide
  have hdescent : baseEnd_3251441 < baseStart_3251441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251442 : List Nat := [3, 2, 1, 3, 4, 1, 1, 1, 2, 3, 2]
def baseStart_3251442 : Nat := 118140960795 + 3251442 * 2 ^ 59
def prefixEnd_3251442 : Nat := 4983230072969 + 3 ^ 40 * 3251442 * 2
def baseEnd_3251442 : Nat := 1669552566216172951921897

theorem tailTrace_3251442 : CollatzResearch.WordTrace tailWord_3251442 prefixEnd_3251442 1669552566216172951921897 := by
  unfold tailWord_3251442
  simp only [CollatzResearch.WordTrace]
  refine ⟨29647458071647102732213145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79059888191058940619235053 29647458071647102732213145)
  ·
    refine ⟨22235593553735327049159859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29647458071647102732213145 22235593553735327049159859)
    ·
      refine ⟨33353390330602990573739789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22235593553735327049159859 33353390330602990573739789)
      ·
        refine ⟨12507521373976121465152421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33353390330602990573739789 12507521373976121465152421)
        ·
          refine ⟨2345160257620522774716079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12507521373976121465152421 2345160257620522774716079)
          ·
            refine ⟨3517740386430784162074119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2345160257620522774716079 3517740386430784162074119)
            ·
              refine ⟨5276610579646176243111179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3517740386430784162074119 5276610579646176243111179)
              ·
                refine ⟨7914915869469264364666769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5276610579646176243111179 7914915869469264364666769)
                ·
                  refine ⟨5936186902101948273500077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7914915869469264364666769 5936186902101948273500077)
                  ·
                    refine ⟨2226070088288230602562529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5936186902101948273500077 2226070088288230602562529)
                    ·
                      refine ⟨1669552566216172951921897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2226070088288230602562529 1669552566216172951921897)
                      ·
                        rfl

theorem cell23_3251442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_3251442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251442 prefixEnd_3251442 := by exact prefixLift 3251442
  have htrace : WordTrace (prefixWord ++ tailWord_3251442) baseStart_3251442 baseEnd_3251442 := by
    simpa [prefixWord, tailWord_3251442, baseEnd_3251442] using wordTrace_append hprefix tailTrace_3251442
  have hstable : (prefixWord ++ tailWord_3251442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251442).length < 2 ^ (prefixWord ++ tailWord_3251442).sum := by decide
  have hdescent : baseEnd_3251442 < baseStart_3251442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251455 : List Nat := [1, 1, 2, 2, 1, 5, 1, 5, 1, 2, 2]
def baseStart_3251455 : Nat := 118140960795 + 3251455 * 2 ^ 59
def prefixEnd_3251455 : Nat := 4983230072969 + 3 ^ 40 * 3251455 * 2
def baseEnd_3251455 : Nat := 1669559241464681401059337

theorem tailTrace_3251455 : CollatzResearch.WordTrace tailWord_3251455 prefixEnd_3251455 1669559241464681401059337 := by
  unfold tailWord_3251455
  simp only [CollatzResearch.WordTrace]
  refine ⟨118590306435541314149075819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79060204290360876099383879 118590306435541314149075819)
  ·
    refine ⟨177885459653311971223613729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118590306435541314149075819 177885459653311971223613729)
    ·
      refine ⟨133414094739983978417710297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177885459653311971223613729 133414094739983978417710297)
      ·
        refine ⟨100060571054987983813282723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133414094739983978417710297 100060571054987983813282723)
        ·
          refine ⟨150090856582481975719924085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100060571054987983813282723 150090856582481975719924085)
          ·
            refine ⟨14071017804607685223742883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150090856582481975719924085 14071017804607685223742883)
            ·
              refine ⟨21106526706911527835614325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14071017804607685223742883 21106526706911527835614325)
              ·
                refine ⟨1978736878772955734588843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21106526706911527835614325 1978736878772955734588843)
                ·
                  refine ⟨2968105318159433601883265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1978736878772955734588843 2968105318159433601883265)
                  ·
                    refine ⟨2226078988619575201412449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2968105318159433601883265 2226078988619575201412449)
                    ·
                      refine ⟨1669559241464681401059337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2226078988619575201412449 1669559241464681401059337)
                      ·
                        rfl

theorem cell23_3251455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 1, 2, 2].length) (baseStart_3251455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251455 prefixEnd_3251455 := by exact prefixLift 3251455
  have htrace : WordTrace (prefixWord ++ tailWord_3251455) baseStart_3251455 baseEnd_3251455 := by
    simpa [prefixWord, tailWord_3251455, baseEnd_3251455] using wordTrace_append hprefix tailTrace_3251455
  have hstable : (prefixWord ++ tailWord_3251455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251455).length < 2 ^ (prefixWord ++ tailWord_3251455).sum := by decide
  have hdescent : baseEnd_3251455 < baseStart_3251455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251549 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_3251549 : Nat := 118140960795 + 3251549 * 2 ^ 59
def prefixEnd_3251549 : Nat := 4983230072969 + 3 ^ 40 * 3251549 * 2
def baseEnd_3251549 : Nat := 1669607508646204033283905

theorem tailTrace_3251549 : CollatzResearch.WordTrace tailWord_3251549 prefixEnd_3251549 1669607508646204033283905 := by
  unfold tailWord_3251549
  simp only [CollatzResearch.WordTrace]
  refine ⟨118593734897200768202997701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79062489931467178801998467 118593734897200768202997701)
  ·
    refine ⟨22236325293225144038062069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118593734897200768202997701 22236325293225144038062069)
    ·
      refine ⟨2084655496239857253568319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22236325293225144038062069 2084655496239857253568319)
      ·
        refine ⟨3126983244359785880352479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2084655496239857253568319 3126983244359785880352479)
        ·
          refine ⟨4690474866539678820528719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3126983244359785880352479 4690474866539678820528719)
          ·
            refine ⟨7035712299809518230793079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4690474866539678820528719 7035712299809518230793079)
            ·
              refine ⟨10553568449714277346189619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7035712299809518230793079 10553568449714277346189619)
              ·
                refine ⟨15830352674571416019284429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10553568449714277346189619 15830352674571416019284429)
                ·
                  refine ⟨5936382252964281007231661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15830352674571416019284429 5936382252964281007231661)
                  ·
                    refine ⟨2226143344861605377711873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5936382252964281007231661 2226143344861605377711873)
                    ·
                      refine ⟨1669607508646204033283905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2226143344861605377711873 1669607508646204033283905)
                      ·
                        rfl

theorem cell23_3251549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_3251549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251549 prefixEnd_3251549 := by exact prefixLift 3251549
  have htrace : WordTrace (prefixWord ++ tailWord_3251549) baseStart_3251549 baseEnd_3251549 := by
    simpa [prefixWord, tailWord_3251549, baseEnd_3251549] using wordTrace_append hprefix tailTrace_3251549
  have hstable : (prefixWord ++ tailWord_3251549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251549).length < 2 ^ (prefixWord ++ tailWord_3251549).sum := by decide
  have hdescent : baseEnd_3251549 < baseStart_3251549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251571 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 3, 7, 2]
def baseStart_3251571 : Nat := 118140960795 + 3251571 * 2 ^ 59
def prefixEnd_3251571 : Nat := 4983230072969 + 3 ^ 40 * 3251571 * 2
def baseEnd_3251571 : Nat := 1669618805220602947208803

theorem tailTrace_3251571 : CollatzResearch.WordTrace tailWord_3251571 prefixEnd_3251571 1669618805220602947208803 := by
  unfold tailWord_3251571
  simp only [CollatzResearch.WordTrace]
  refine ⟨118594537303121065960298567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79063024868747377306865711 118594537303121065960298567)
  ·
    refine ⟨177891805954681598940447851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118594537303121065960298567 177891805954681598940447851)
    ·
      refine ⟨266837708932022398410671777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177891805954681598940447851 266837708932022398410671777)
      ·
        refine ⟨200128281699016798808003833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266837708932022398410671777 200128281699016798808003833)
        ·
          refine ⟨150096211274262599106002875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200128281699016798808003833 150096211274262599106002875)
          ·
            refine ⟨225144316911393898659004313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150096211274262599106002875 225144316911393898659004313)
            ·
              refine ⟨168858237683545423994253235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225144316911393898659004313 168858237683545423994253235)
              ·
                refine ⟨253287356525318135991379853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168858237683545423994253235 253287356525318135991379853)
                ·
                  refine ⟨94982758696994300996767445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 253287356525318135991379853 94982758696994300996767445)
                  ·
                    refine ⟨2226158406960803929611737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 94982758696994300996767445 2226158406960803929611737)
                    ·
                      refine ⟨1669618805220602947208803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2226158406960803929611737 1669618805220602947208803)
                      ·
                        rfl

theorem cell23_3251571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 7, 2].length) (baseStart_3251571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251571 prefixEnd_3251571 := by exact prefixLift 3251571
  have htrace : WordTrace (prefixWord ++ tailWord_3251571) baseStart_3251571 baseEnd_3251571 := by
    simpa [prefixWord, tailWord_3251571, baseEnd_3251571] using wordTrace_append hprefix tailTrace_3251571
  have hstable : (prefixWord ++ tailWord_3251571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251571).length < 2 ^ (prefixWord ++ tailWord_3251571).sum := by decide
  have hdescent : baseEnd_3251571 < baseStart_3251571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251581 : List Nat := [1, 4, 1, 1, 2, 2, 1, 4, 2, 5]
def baseStart_3251581 : Nat := 118140960795 + 3251581 * 2 ^ 59
def prefixEnd_3251581 : Nat := 4983230072969 + 3 ^ 40 * 3251581 * 2
def baseEnd_3251581 : Nat := 556541313342382636027919

theorem tailTrace_3251581 : CollatzResearch.WordTrace tailWord_3251581 prefixEnd_3251581 556541313342382636027919 := by
  unfold tailWord_3251581
  simp only [CollatzResearch.WordTrace]
  refine ⟨118594902033084837668162597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79063268022056558445441731 118594902033084837668162597)
  ·
    refine ⟨22236544131203407062780487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118594902033084837668162597 22236544131203407062780487)
    ·
      refine ⟨33354816196805110594170731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22236544131203407062780487 33354816196805110594170731)
      ·
        refine ⟨50032224295207665891256097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33354816196805110594170731 50032224295207665891256097)
        ·
          refine ⟨37524168221405749418442073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50032224295207665891256097 37524168221405749418442073)
          ·
            refine ⟨28143126166054312063831555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37524168221405749418442073 28143126166054312063831555)
            ·
              refine ⟨42214689249081468095747333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28143126166054312063831555 42214689249081468095747333)
              ·
                refine ⟨7915254234202775267952625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42214689249081468095747333 7915254234202775267952625)
                ·
                  refine ⟨5936440675652081450964469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7915254234202775267952625 5936440675652081450964469)
                  ·
                    refine ⟨556541313342382636027919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5936440675652081450964469 556541313342382636027919)
                    ·
                      rfl

theorem cell23_3251581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_3251581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251581 prefixEnd_3251581 := by exact prefixLift 3251581
  have htrace : WordTrace (prefixWord ++ tailWord_3251581) baseStart_3251581 baseEnd_3251581 := by
    simpa [prefixWord, tailWord_3251581, baseEnd_3251581] using wordTrace_append hprefix tailTrace_3251581
  have hstable : (prefixWord ++ tailWord_3251581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251581).length < 2 ^ (prefixWord ++ tailWord_3251581).sum := by decide
  have hdescent : baseEnd_3251581 < baseStart_3251581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251585 : List Nat := [1, 2, 4, 3, 2, 1, 1, 4, 5]
def baseStart_3251585 : Nat := 118140960795 + 3251585 * 2 ^ 59
def prefixEnd_3251585 : Nat := 4983230072969 + 3 ^ 40 * 3251585 * 2
def baseEnd_3251585 : Nat := 185513999327751765825971

theorem tailTrace_3251585 : CollatzResearch.WordTrace tailWord_3251585 prefixEnd_3251585 185513999327751765825971 := by
  unfold tailWord_3251585
  simp only [CollatzResearch.WordTrace]
  refine ⟨118595047925070346351308209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79063365283380230900872139 118595047925070346351308209)
  ·
    refine ⟨88946285943802759763481157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118595047925070346351308209 88946285943802759763481157)
    ·
      refine ⟨16677428614463017455652717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88946285943802759763481157 16677428614463017455652717)
      ·
        refine ⟨6254035730423631545869769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16677428614463017455652717 6254035730423631545869769)
        ·
          refine ⟨4690526797817723659402327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6254035730423631545869769 4690526797817723659402327)
          ·
            refine ⟨7035790196726585489103491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4690526797817723659402327 7035790196726585489103491)
            ·
              refine ⟨10553685295089878233655237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7035790196726585489103491 10553685295089878233655237)
              ·
                refine ⟨1978815992829352168810357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10553685295089878233655237 1978815992829352168810357)
                ·
                  refine ⟨185513999327751765825971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1978815992829352168810357 185513999327751765825971)
                  ·
                    rfl

theorem cell23_3251585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 5].length) (baseStart_3251585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251585 prefixEnd_3251585 := by exact prefixLift 3251585
  have htrace : WordTrace (prefixWord ++ tailWord_3251585) baseStart_3251585 baseEnd_3251585 := by
    simpa [prefixWord, tailWord_3251585, baseEnd_3251585] using wordTrace_append hprefix tailTrace_3251585
  have hstable : (prefixWord ++ tailWord_3251585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251585).length < 2 ^ (prefixWord ++ tailWord_3251585).sum := by decide
  have hdescent : baseEnd_3251585 < baseStart_3251585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251588 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 2, 5, 2]
def baseStart_3251588 : Nat := 118140960795 + 3251588 * 2 ^ 59
def prefixEnd_3251588 : Nat := 4983230072969 + 3 ^ 40 * 3251588 * 2
def baseEnd_3251588 : Nat := 1669627534391729380696225

theorem tailTrace_3251588 : CollatzResearch.WordTrace tailWord_3251588 prefixEnd_3251588 1669627534391729380696225 := by
  unfold tailWord_3251588
  simp only [CollatzResearch.WordTrace]
  refine ⟨59297578672029738931833709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79063438229372985242444945 59297578672029738931833709)
  ·
    refine ⟨22236592002011152099437641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59297578672029738931833709 22236592002011152099437641)
    ·
      refine ⟨16677444001508364074578231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22236592002011152099437641 16677444001508364074578231)
      ·
        refine ⟨25016166002262546111867347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16677444001508364074578231 25016166002262546111867347)
        ·
          refine ⟨37524249003393819167801021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25016166002262546111867347 37524249003393819167801021)
          ·
            refine ⟨14071593376272682187925383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37524249003393819167801021 14071593376272682187925383)
            ·
              refine ⟨21107390064409023281888075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14071593376272682187925383 21107390064409023281888075)
              ·
                refine ⟨31661085096613534922832113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21107390064409023281888075 31661085096613534922832113)
                ·
                  refine ⟨23745813822460151192124085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31661085096613534922832113 23745813822460151192124085)
                  ·
                    refine ⟨2226170045855639174261633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23745813822460151192124085 2226170045855639174261633)
                    ·
                      refine ⟨1669627534391729380696225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2226170045855639174261633 1669627534391729380696225)
                      ·
                        rfl

theorem cell23_3251588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_3251588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251588 prefixEnd_3251588 := by exact prefixLift 3251588
  have htrace : WordTrace (prefixWord ++ tailWord_3251588) baseStart_3251588 baseEnd_3251588 := by
    simpa [prefixWord, tailWord_3251588, baseEnd_3251588] using wordTrace_append hprefix tailTrace_3251588
  have hstable : (prefixWord ++ tailWord_3251588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251588).length < 2 ^ (prefixWord ++ tailWord_3251588).sum := by decide
  have hdescent : baseEnd_3251588 < baseStart_3251588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251591 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 5]
def baseStart_3251591 : Nat := 118140960795 + 3251591 * 2 ^ 59
def prefixEnd_3251591 : Nat := 4983230072969 + 3 ^ 40 * 3251591 * 2
def baseEnd_3251591 : Nat := 1669629074833692868958711

theorem tailTrace_3251591 : CollatzResearch.WordTrace tailWord_3251591 prefixEnd_3251591 1669629074833692868958711 := by
  unfold tailWord_3251591
  simp only [CollatzResearch.WordTrace]
  refine ⟨118595266763048609376026627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79063511175365739584017751 118595266763048609376026627)
  ·
    refine ⟨177892900144572914064039941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118595266763048609376026627 177892900144572914064039941)
    ·
      refine ⟨33354918777107421387007489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177892900144572914064039941 33354918777107421387007489)
      ·
        refine ⟨25016189082830566040255617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33354918777107421387007489 25016189082830566040255617)
        ·
          refine ⟨18762141812122924530191713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25016189082830566040255617 18762141812122924530191713)
          ·
            refine ⟨14071606359092193397643785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18762141812122924530191713 14071606359092193397643785)
            ·
              refine ⟨10553704769319145048232839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14071606359092193397643785 10553704769319145048232839)
              ·
                refine ⟨15830557153978717572349259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10553704769319145048232839 15830557153978717572349259)
                ·
                  refine ⟨23745835730968076358523889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15830557153978717572349259 23745835730968076358523889)
                  ·
                    refine ⟨17809376798226057268892917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23745835730968076358523889 17809376798226057268892917)
                    ·
                      refine ⟨1669629074833692868958711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17809376798226057268892917 1669629074833692868958711)
                      ·
                        rfl

theorem cell23_3251591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_3251591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251591 prefixEnd_3251591 := by exact prefixLift 3251591
  have htrace : WordTrace (prefixWord ++ tailWord_3251591) baseStart_3251591 baseEnd_3251591 := by
    simpa [prefixWord, tailWord_3251591, baseEnd_3251591] using wordTrace_append hprefix tailTrace_3251591
  have hstable : (prefixWord ++ tailWord_3251591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251591).length < 2 ^ (prefixWord ++ tailWord_3251591).sum := by decide
  have hdescent : baseEnd_3251591 < baseStart_3251591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251618 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_3251618 : Nat := 118140960795 + 3251618 * 2 ^ 59
def prefixEnd_3251618 : Nat := 4983230072969 + 3 ^ 40 * 3251618 * 2
def baseEnd_3251618 : Nat := 1669642938811364263321087

theorem tailTrace_3251618 : CollatzResearch.WordTrace tailWord_3251618 prefixEnd_3251618 1669642938811364263321087 := by
  unfold tailWord_3251618
  simp only [CollatzResearch.WordTrace]
  refine ⟨29649062883487698246814877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79064167689300528658173005 29649062883487698246814877)
  ·
    refine ⟨11118398581307886842555579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29649062883487698246814877 11118398581307886842555579)
    ·
      refine ⟨16677597871961830263833369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11118398581307886842555579 16677597871961830263833369)
      ·
        refine ⟨12508198403971372697875027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16677597871961830263833369 12508198403971372697875027)
        ·
          refine ⟨18762297605957059046812541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12508198403971372697875027 18762297605957059046812541)
          ·
            refine ⟨7035861602233897142554703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18762297605957059046812541 7035861602233897142554703)
            ·
              refine ⟨10553792403350845713832055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7035861602233897142554703 10553792403350845713832055)
              ·
                refine ⟨15830688605026268570748083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10553792403350845713832055 15830688605026268570748083)
                ·
                  refine ⟨23746032907539402856122125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15830688605026268570748083 23746032907539402856122125)
                  ·
                    refine ⟨8904762340327276071045797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23746032907539402856122125 8904762340327276071045797)
                    ·
                      refine ⟨1669642938811364263321087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8904762340327276071045797 1669642938811364263321087)
                      ·
                        rfl

theorem cell23_3251618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_3251618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251618 prefixEnd_3251618 := by exact prefixLift 3251618
  have htrace : WordTrace (prefixWord ++ tailWord_3251618) baseStart_3251618 baseEnd_3251618 := by
    simpa [prefixWord, tailWord_3251618, baseEnd_3251618] using wordTrace_append hprefix tailTrace_3251618
  have hstable : (prefixWord ++ tailWord_3251618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251618).length < 2 ^ (prefixWord ++ tailWord_3251618).sum := by decide
  have hdescent : baseEnd_3251618 < baseStart_3251618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251645 : List Nat := [1, 4, 1, 2, 2, 1, 1, 6, 1, 4]
def baseStart_3251645 : Nat := 118140960795 + 3251645 * 2 ^ 59
def prefixEnd_3251645 : Nat := 4983230072969 + 3 ^ 40 * 3251645 * 2
def baseEnd_3251645 : Nat := 556552267596345219227821

theorem tailTrace_3251645 : CollatzResearch.WordTrace tailWord_3251645 prefixEnd_3251645 556552267596345219227821 := by
  unfold tailWord_3251645
  simp only [CollatzResearch.WordTrace]
  refine ⟨118597236304852976598492389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79064824203235317732328259 118597236304852976598492389)
  ·
    refine ⟨22236981807159933112217323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118597236304852976598492389 22236981807159933112217323)
    ·
      refine ⟨33355472710739899668325985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22236981807159933112217323 33355472710739899668325985)
      ·
        refine ⟨25016604533054924751244489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33355472710739899668325985 25016604533054924751244489)
        ·
          refine ⟨18762453399791193563433367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25016604533054924751244489 18762453399791193563433367)
          ·
            refine ⟨28143680099686790345150051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18762453399791193563433367 28143680099686790345150051)
            ·
              refine ⟨42215520149530185517725077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28143680099686790345150051 42215520149530185517725077)
              ·
                refine ⟨1978852507009227446143363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42215520149530185517725077 1978852507009227446143363)
                ·
                  refine ⟨2968278760513841169215045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1978852507009227446143363 2968278760513841169215045)
                  ·
                    refine ⟨556552267596345219227821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2968278760513841169215045 556552267596345219227821)
                    ·
                      rfl

theorem cell23_3251645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_3251645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251645 prefixEnd_3251645 := by exact prefixLift 3251645
  have htrace : WordTrace (prefixWord ++ tailWord_3251645) baseStart_3251645 baseEnd_3251645 := by
    simpa [prefixWord, tailWord_3251645, baseEnd_3251645] using wordTrace_append hprefix tailTrace_3251645
  have hstable : (prefixWord ++ tailWord_3251645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251645).length < 2 ^ (prefixWord ++ tailWord_3251645).sum := by decide
  have hdescent : baseEnd_3251645 < baseStart_3251645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251671 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 3, 5]
def baseStart_3251671 : Nat := 118140960795 + 3251671 * 2 ^ 59
def prefixEnd_3251671 : Nat := 4983230072969 + 3 ^ 40 * 3251671 * 2
def baseEnd_3251671 : Nat := 556556717762017518652781

theorem tailTrace_3251671 : CollatzResearch.WordTrace tailWord_3251671 prefixEnd_3251671 556556717762017518652781 := by
  unfold tailWord_3251671
  simp only [CollatzResearch.WordTrace]
  refine ⟨118598184602758783038938867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79065456401839188692625911 118598184602758783038938867)
  ·
    refine ⟨177897276904138174558408301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118598184602758783038938867 177897276904138174558408301)
    ·
      refine ⟨66711478839051815459403113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177897276904138174558408301 66711478839051815459403113)
      ·
        refine ⟨50033609129288861594552335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66711478839051815459403113 50033609129288861594552335)
        ·
          refine ⟨75050413693933292391828503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50033609129288861594552335 75050413693933292391828503)
          ·
            refine ⟨112575620540899938587742755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75050413693933292391828503 112575620540899938587742755)
            ·
              refine ⟨168863430811349907881614133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112575620540899938587742755 168863430811349907881614133)
              ·
                refine ⟨15830946638564053863901325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168863430811349907881614133 15830946638564053863901325)
                ·
                  refine ⟨5936604989461520198962997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15830946638564053863901325 5936604989461520198962997)
                  ·
                    refine ⟨556556717762017518652781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5936604989461520198962997 556556717762017518652781)
                    ·
                      rfl

theorem cell23_3251671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_3251671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251671 prefixEnd_3251671 := by exact prefixLift 3251671
  have htrace : WordTrace (prefixWord ++ tailWord_3251671) baseStart_3251671 baseEnd_3251671 := by
    simpa [prefixWord, tailWord_3251671, baseEnd_3251671] using wordTrace_append hprefix tailTrace_3251671
  have hstable : (prefixWord ++ tailWord_3251671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251671).length < 2 ^ (prefixWord ++ tailWord_3251671).sum := by decide
  have hdescent : baseEnd_3251671 < baseStart_3251671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251688 : List Nat := [2, 1, 4, 1, 1, 2, 1, 5, 1, 5]
def baseStart_3251688 : Nat := 118140960795 + 3251688 * 2 ^ 59
def prefixEnd_3251688 : Nat := 4983230072969 + 3 ^ 40 * 3251688 * 2
def baseEnd_3251688 : Nat := 556559627485726329815255

theorem tailTrace_3251688 : CollatzResearch.WordTrace tailWord_3251688 prefixEnd_3251688 556559627485726329815255 := by
  unfold tailWord_3251688
  simp only [CollatzResearch.WordTrace]
  refine ⟨59299402321848597471153859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79065869762464796628205145 59299402321848597471153859)
  ·
    refine ⟨88949103482772896206730789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59299402321848597471153859 88949103482772896206730789)
    ·
      refine ⟨16677956903019918038762023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88949103482772896206730789 16677956903019918038762023)
      ·
        refine ⟨25016935354529877058143035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16677956903019918038762023 25016935354529877058143035)
        ·
          refine ⟨37525403031794815587214553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25016935354529877058143035 37525403031794815587214553)
          ·
            refine ⟨28144052273846111690410915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37525403031794815587214553 28144052273846111690410915)
            ·
              refine ⟨42216078410769167535616373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28144052273846111690410915 42216078410769167535616373)
              ·
                refine ⟨3957757351009609456464035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42216078410769167535616373 3957757351009609456464035)
                ·
                  refine ⟨5936636026514414184696053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3957757351009609456464035 5936636026514414184696053)
                  ·
                    refine ⟨556559627485726329815255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5936636026514414184696053 556559627485726329815255)
                    ·
                      rfl

theorem cell23_3251688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_3251688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251688 prefixEnd_3251688 := by exact prefixLift 3251688
  have htrace : WordTrace (prefixWord ++ tailWord_3251688) baseStart_3251688 baseEnd_3251688 := by
    simpa [prefixWord, tailWord_3251688, baseEnd_3251688] using wordTrace_append hprefix tailTrace_3251688
  have hstable : (prefixWord ++ tailWord_3251688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251688).length < 2 ^ (prefixWord ++ tailWord_3251688).sum := by decide
  have hdescent : baseEnd_3251688 < baseStart_3251688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251702 : List Nat := [5, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3]
def baseStart_3251702 : Nat := 118140960795 + 3251702 * 2 ^ 59
def prefixEnd_3251702 : Nat := 4983230072969 + 3 ^ 40 * 3251702 * 2
def baseEnd_3251702 : Nat := 1669686071186341934670701

theorem tailTrace_3251702 : CollatzResearch.WordTrace tailWord_3251702 prefixEnd_3251702 1669686071186341934670701 := by
  unfold tailWord_3251702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7412457204102904708332335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79066210177097650222211573 7412457204102904708332335)
  ·
    refine ⟨11118685806154357062498503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7412457204102904708332335 11118685806154357062498503)
    ·
      refine ⟨16678028709231535593747755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11118685806154357062498503 16678028709231535593747755)
      ·
        refine ⟨25017043063847303390621633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16678028709231535593747755 25017043063847303390621633)
        ·
          refine ⟨18762782297885477542966225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25017043063847303390621633 18762782297885477542966225)
          ·
            refine ⟨14072086723414108157224669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18762782297885477542966225 14072086723414108157224669)
            ·
              refine ⟨5277032521280290558959251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14072086723414108157224669 5277032521280290558959251)
              ·
                refine ⟨7915548781920435838438877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5277032521280290558959251 7915548781920435838438877)
                ·
                  refine ⟨2968330793220163439414579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7915548781920435838438877 2968330793220163439414579)
                  ·
                    refine ⟨4452496189830245159121869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2968330793220163439414579 4452496189830245159121869)
                    ·
                      refine ⟨1669686071186341934670701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4452496189830245159121869 1669686071186341934670701)
                      ·
                        rfl

theorem cell23_3251702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_3251702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251702 prefixEnd_3251702 := by exact prefixLift 3251702
  have htrace : WordTrace (prefixWord ++ tailWord_3251702) baseStart_3251702 baseEnd_3251702 := by
    simpa [prefixWord, tailWord_3251702, baseEnd_3251702] using wordTrace_append hprefix tailTrace_3251702
  have hstable : (prefixWord ++ tailWord_3251702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251702).length < 2 ^ (prefixWord ++ tailWord_3251702).sum := by decide
  have hdescent : baseEnd_3251702 < baseStart_3251702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251711 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 5]
def baseStart_3251711 : Nat := 118140960795 + 3251711 * 2 ^ 59
def prefixEnd_3251711 : Nat := 4983230072969 + 3 ^ 40 * 3251711 * 2
def baseEnd_3251711 : Nat := 1669690692512232399458159

theorem tailTrace_3251711 : CollatzResearch.WordTrace tailWord_3251711 prefixEnd_3251711 1669690692512232399458159 := by
  unfold tailWord_3251711
  simp only [CollatzResearch.WordTrace]
  refine ⟨118599643522613869870394987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79066429015075913246929991 118599643522613869870394987)
  ·
    refine ⟨177899465283920804805592481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118599643522613869870394987 177899465283920804805592481)
    ·
      refine ⟨133424598962940603604194361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177899465283920804805592481 133424598962940603604194361)
      ·
        refine ⟨100068449222205452703145771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133424598962940603604194361 100068449222205452703145771)
        ·
          refine ⟨150102673833308179054718657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100068449222205452703145771 150102673833308179054718657)
          ·
            refine ⟨112577005374981134291038993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150102673833308179054718657 112577005374981134291038993)
            ·
              refine ⟨84432754031235850718279245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112577005374981134291038993 84432754031235850718279245)
              ·
                refine ⟨31662282761713444019354717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84432754031235850718279245 31662282761713444019354717)
                ·
                  refine ⟨11873356035642541507258019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31662282761713444019354717 11873356035642541507258019)
                  ·
                    refine ⟨17810034053463812260887029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11873356035642541507258019 17810034053463812260887029)
                    ·
                      refine ⟨1669690692512232399458159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17810034053463812260887029 1669690692512232399458159)
                      ·
                        rfl

theorem cell23_3251711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_3251711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251711 prefixEnd_3251711 := by exact prefixLift 3251711
  have htrace : WordTrace (prefixWord ++ tailWord_3251711) baseStart_3251711 baseEnd_3251711 := by
    simpa [prefixWord, tailWord_3251711, baseEnd_3251711] using wordTrace_append hprefix tailTrace_3251711
  have hstable : (prefixWord ++ tailWord_3251711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251711).length < 2 ^ (prefixWord ++ tailWord_3251711).sum := by decide
  have hdescent : baseEnd_3251711 < baseStart_3251711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251721 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 1, 1, 6]
def baseStart_3251721 : Nat := 118140960795 + 3251721 * 2 ^ 59
def prefixEnd_3251721 : Nat := 4983230072969 + 3 ^ 40 * 3251721 * 2
def baseEnd_3251721 : Nat := 1669695827318777360333113

theorem tailTrace_3251721 : CollatzResearch.WordTrace tailWord_3251721 prefixEnd_3251721 1669695827318777360333113 := by
  unfold tailWord_3251721
  simp only [CollatzResearch.WordTrace]
  refine ⟨118600008252577641578259017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79066672168385094385506011 118600008252577641578259017)
  ·
    refine ⟨88950006189433231183694263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118600008252577641578259017 88950006189433231183694263)
    ·
      refine ⟨133425009284149846775541395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88950006189433231183694263 133425009284149846775541395)
      ·
        refine ⟨200137513926224770163312093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133425009284149846775541395 200137513926224770163312093)
        ·
          refine ⟨75051567722334288811242035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200137513926224770163312093 75051567722334288811242035)
          ·
            refine ⟨112577351583501433216863053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75051567722334288811242035 112577351583501433216863053)
            ·
              refine ⟨42216506843813037456323645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112577351583501433216863053 42216506843813037456323645)
              ·
                refine ⟨15831190066429889046121367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42216506843813037456323645 15831190066429889046121367)
                ·
                  refine ⟨23746785099644833569182051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15831190066429889046121367 23746785099644833569182051)
                  ·
                    refine ⟨35620177649467250353773077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23746785099644833569182051 35620177649467250353773077)
                    ·
                      refine ⟨1669695827318777360333113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35620177649467250353773077 1669695827318777360333113)
                      ·
                        rfl

theorem cell23_3251721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 1, 6].length) (baseStart_3251721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251721 prefixEnd_3251721 := by exact prefixLift 3251721
  have htrace : WordTrace (prefixWord ++ tailWord_3251721) baseStart_3251721 baseEnd_3251721 := by
    simpa [prefixWord, tailWord_3251721, baseEnd_3251721] using wordTrace_append hprefix tailTrace_3251721
  have hstable : (prefixWord ++ tailWord_3251721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251721).length < 2 ^ (prefixWord ++ tailWord_3251721).sum := by decide
  have hdescent : baseEnd_3251721 < baseStart_3251721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251731 : List Nat := [1, 1, 1, 2, 1, 6, 2, 9]
def baseStart_3251731 : Nat := 118140960795 + 3251731 * 2 ^ 59
def prefixEnd_3251731 : Nat := 4983230072969 + 3 ^ 40 * 3251731 * 2
def baseEnd_3251731 : Nat := 61840776375011937822521

theorem tailTrace_3251731 : CollatzResearch.WordTrace tailWord_3251731 prefixEnd_3251731 61840776375011937822521 := by
  unfold tailWord_3251731
  simp only [CollatzResearch.WordTrace]
  refine ⟨118600372982541413286123047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79066915321694275524082031 118600372982541413286123047)
  ·
    refine ⟨177900559473812119929184571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118600372982541413286123047 177900559473812119929184571)
    ·
      refine ⟨266850839210718179893776857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177900559473812119929184571 266850839210718179893776857)
      ·
        refine ⟨200138129408038634920332643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266850839210718179893776857 200138129408038634920332643)
        ·
          refine ⟨300207194112057952380498965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200138129408038634920332643 300207194112057952380498965)
          ·
            refine ⟨14072212224002716517835889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 300207194112057952380498965 14072212224002716517835889)
            ·
              refine ⟨10554159168002037388376917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14072212224002716517835889 10554159168002037388376917)
              ·
                refine ⟨61840776375011937822521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10554159168002037388376917 61840776375011937822521)
                ·
                  rfl

theorem cell23_3251731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 9].length) (baseStart_3251731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251731 prefixEnd_3251731 := by exact prefixLift 3251731
  have htrace : WordTrace (prefixWord ++ tailWord_3251731) baseStart_3251731 baseEnd_3251731 := by
    simpa [prefixWord, tailWord_3251731, baseEnd_3251731] using wordTrace_append hprefix tailTrace_3251731
  have hstable : (prefixWord ++ tailWord_3251731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251731).length < 2 ^ (prefixWord ++ tailWord_3251731).sum := by decide
  have hdescent : baseEnd_3251731 < baseStart_3251731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251745 : List Nat := [1, 2, 3, 2, 2, 4, 1, 1, 1, 1, 5]
def baseStart_3251745 : Nat := 118140960795 + 3251745 * 2 ^ 59
def prefixEnd_3251745 : Nat := 4983230072969 + 3 ^ 40 * 3251745 * 2
def baseEnd_3251745 : Nat := 1669708150854485266433003

theorem tailTrace_3251745 : CollatzResearch.WordTrace tailWord_3251745 prefixEnd_3251745 1669708150854485266433003 := by
  unfold tailWord_3251745
  simp only [CollatzResearch.WordTrace]
  refine ⟨118600883604490693677132689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79067255736327129118088459 118600883604490693677132689)
  ·
    refine ⟨88950662703368020257849517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118600883604490693677132689 88950662703368020257849517)
    ·
      refine ⟨33356498513763007596693569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88950662703368020257849517 33356498513763007596693569)
      ·
        refine ⟨25017373885322255697520177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33356498513763007596693569 25017373885322255697520177)
        ·
          refine ⟨18763030413991691773140133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25017373885322255697520177 18763030413991691773140133)
          ·
            refine ⟨3518068202623442207463775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18763030413991691773140133 3518068202623442207463775)
            ·
              refine ⟨5277102303935163311195663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3518068202623442207463775 5277102303935163311195663)
              ·
                refine ⟨7915653455902744966793495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5277102303935163311195663 7915653455902744966793495)
                ·
                  refine ⟨11873480183854117450190243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7915653455902744966793495 11873480183854117450190243)
                  ·
                    refine ⟨17810220275781176175285365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11873480183854117450190243 17810220275781176175285365)
                    ·
                      refine ⟨1669708150854485266433003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17810220275781176175285365 1669708150854485266433003)
                      ·
                        rfl

theorem cell23_3251745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_3251745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251745 prefixEnd_3251745 := by exact prefixLift 3251745
  have htrace : WordTrace (prefixWord ++ tailWord_3251745) baseStart_3251745 baseEnd_3251745 := by
    simpa [prefixWord, tailWord_3251745, baseEnd_3251745] using wordTrace_append hprefix tailTrace_3251745
  have hstable : (prefixWord ++ tailWord_3251745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251745).length < 2 ^ (prefixWord ++ tailWord_3251745).sum := by decide
  have hdescent : baseEnd_3251745 < baseStart_3251745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251775 : List Nat := [1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 3]
def baseStart_3251775 : Nat := 118140960795 + 3251775 * 2 ^ 59
def prefixEnd_3251775 : Nat := 4983230072969 + 3 ^ 40 * 3251775 * 2
def baseEnd_3251775 : Nat := 1669723555274120149057865

theorem tailTrace_3251775 : CollatzResearch.WordTrace tailWord_3251775 prefixEnd_3251775 1669723555274120149057865 := by
  unfold tailWord_3251775
  simp only [CollatzResearch.WordTrace]
  refine ⟨118601977794382008800724779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79067985196254672533816519 118601977794382008800724779)
  ·
    refine ⟨177902966691573013201087169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118601977794382008800724779 177902966691573013201087169)
    ·
      refine ⟨133427225018679759900815377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177902966691573013201087169 133427225018679759900815377)
      ·
        refine ⟨100070418764009819925611533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133427225018679759900815377 100070418764009819925611533)
        ·
          refine ⟨37526407036503682472104325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100070418764009819925611533 37526407036503682472104325)
          ·
            refine ⟨7036201319344440463519561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37526407036503682472104325 7036201319344440463519561)
            ·
              refine ⟨5277150989508330347639671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7036201319344440463519561 5277150989508330347639671)
              ·
                refine ⟨7915726484262495521459507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5277150989508330347639671 7915726484262495521459507)
                ·
                  refine ⟨11873589726393743282189261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7915726484262495521459507 11873589726393743282189261)
                  ·
                    refine ⟨4452596147397653730820973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11873589726393743282189261 4452596147397653730820973)
                    ·
                      refine ⟨1669723555274120149057865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4452596147397653730820973 1669723555274120149057865)
                      ·
                        rfl

theorem cell23_3251775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 3].length) (baseStart_3251775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251775 prefixEnd_3251775 := by exact prefixLift 3251775
  have htrace : WordTrace (prefixWord ++ tailWord_3251775) baseStart_3251775 baseEnd_3251775 := by
    simpa [prefixWord, tailWord_3251775, baseEnd_3251775] using wordTrace_append hprefix tailTrace_3251775
  have hstable : (prefixWord ++ tailWord_3251775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251775).length < 2 ^ (prefixWord ++ tailWord_3251775).sum := by decide
  have hdescent : baseEnd_3251775 < baseStart_3251775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251791 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 3, 8]
def baseStart_3251791 : Nat := 118140960795 + 3251791 * 2 ^ 59
def prefixEnd_3251791 : Nat := 4983230072969 + 3 ^ 40 * 3251791 * 2
def baseEnd_3251791 : Nat := 556577256988197362152597

theorem tailTrace_3251791 : CollatzResearch.WordTrace tailWord_3251791 prefixEnd_3251791 556577256988197362152597 := by
  unfold tailWord_3251791
  simp only [CollatzResearch.WordTrace]
  refine ⟨118602561362324043533307227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79068374241549362355538151 118602561362324043533307227)
  ·
    refine ⟨177903842043486065299960841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118602561362324043533307227 177903842043486065299960841)
    ·
      refine ⟨133427881532614548974970631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177903842043486065299960841 133427881532614548974970631)
      ·
        refine ⟨200141822298921823462455947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133427881532614548974970631 200141822298921823462455947)
        ·
          refine ⟨300212733448382735193683921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200141822298921823462455947 300212733448382735193683921)
          ·
            refine ⟨225159550086287051395262941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300212733448382735193683921 225159550086287051395262941)
            ·
              refine ⟨84434831282357644273223603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225159550086287051395262941 84434831282357644273223603)
              ·
                refine ⟨126652246923536466409835405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84434831282357644273223603 126652246923536466409835405)
                ·
                  refine ⟨47494592596326174903688277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126652246923536466409835405 47494592596326174903688277)
                  ·
                    refine ⟨556577256988197362152597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47494592596326174903688277 556577256988197362152597)
                    ·
                      rfl

theorem cell23_3251791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 8].length) (baseStart_3251791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251791 prefixEnd_3251791 := by exact prefixLift 3251791
  have htrace : WordTrace (prefixWord ++ tailWord_3251791) baseStart_3251791 baseEnd_3251791 := by
    simpa [prefixWord, tailWord_3251791, baseEnd_3251791] using wordTrace_append hprefix tailTrace_3251791
  have hstable : (prefixWord ++ tailWord_3251791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251791).length < 2 ^ (prefixWord ++ tailWord_3251791).sum := by decide
  have hdescent : baseEnd_3251791 < baseStart_3251791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251815 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 3, 4, 2]
def baseStart_3251815 : Nat := 118140960795 + 3251815 * 2 ^ 59
def prefixEnd_3251815 : Nat := 4983230072969 + 3 ^ 40 * 3251815 * 2
def baseEnd_3251815 : Nat := 1669744094500299992557681

theorem tailTrace_3251815 : CollatzResearch.WordTrace tailWord_3251815 prefixEnd_3251815 1669744094500299992557681 := by
  unfold tailWord_3251815
  simp only [CollatzResearch.WordTrace]
  refine ⟨118603436714237095632180899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79068957809491397088120599 118603436714237095632180899)
  ·
    refine ⟨177905155071355643448271349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118603436714237095632180899 177905155071355643448271349)
    ·
      refine ⟨16678608287939591573275439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177905155071355643448271349 16678608287939591573275439)
      ·
        refine ⟨25017912431909387359913159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16678608287939591573275439 25017912431909387359913159)
        ·
          refine ⟨37526868647864081039869739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25017912431909387359913159 37526868647864081039869739)
          ·
            refine ⟨56290302971796121559804609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37526868647864081039869739 56290302971796121559804609)
            ·
              refine ⟨42217727228847091169853457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56290302971796121559804609 42217727228847091169853457)
              ·
                refine ⟨31663295421635318377390093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42217727228847091169853457 31663295421635318377390093)
                ·
                  refine ⟨11873735783113244391521285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31663295421635318377390093 11873735783113244391521285)
                  ·
                    refine ⟨2226325459333733323410241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11873735783113244391521285 2226325459333733323410241)
                    ·
                      refine ⟨1669744094500299992557681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2226325459333733323410241 1669744094500299992557681)
                      ·
                        rfl

theorem cell23_3251815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_3251815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251815 prefixEnd_3251815 := by exact prefixLift 3251815
  have htrace : WordTrace (prefixWord ++ tailWord_3251815) baseStart_3251815 baseEnd_3251815 := by
    simpa [prefixWord, tailWord_3251815, baseEnd_3251815] using wordTrace_append hprefix tailTrace_3251815
  have hstable : (prefixWord ++ tailWord_3251815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251815).length < 2 ^ (prefixWord ++ tailWord_3251815).sum := by decide
  have hdescent : baseEnd_3251815 < baseStart_3251815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251875 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 2, 5, 2]
def baseStart_3251875 : Nat := 118140960795 + 3251875 * 2 ^ 59
def prefixEnd_3251875 : Nat := 4983230072969 + 3 ^ 40 * 3251875 * 2
def baseEnd_3251875 : Nat := 1669774903339569757807405

theorem tailTrace_3251875 : CollatzResearch.WordTrace tailWord_3251875 prefixEnd_3251875 1669774903339569757807405 := by
  unfold tailWord_3251875
  simp only [CollatzResearch.WordTrace]
  refine ⟨118605625094019725879365079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79070416729346483919576719 118605625094019725879365079)
  ·
    refine ⟨177908437641029588819047619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118605625094019725879365079 177908437641029588819047619)
    ·
      refine ⟨266862656461544383228571429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177908437641029588819047619 266862656461544383228571429)
      ·
        refine ⟨50036748086539571855357143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 266862656461544383228571429 50036748086539571855357143)
        ·
          refine ⟨75055122129809357783035715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50036748086539571855357143 75055122129809357783035715)
          ·
            refine ⟨112582683194714036674553573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75055122129809357783035715 112582683194714036674553573)
            ·
              refine ⟨21109253099008881876478795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112582683194714036674553573 21109253099008881876478795)
              ·
                refine ⟨31663879648513322814718193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21109253099008881876478795 31663879648513322814718193)
                ·
                  refine ⟨23747909736384992111038645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31663879648513322814718193 23747909736384992111038645)
                  ·
                    refine ⟨2226366537786093010409873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23747909736384992111038645 2226366537786093010409873)
                    ·
                      refine ⟨1669774903339569757807405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2226366537786093010409873 1669774903339569757807405)
                      ·
                        rfl

theorem cell23_3251875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 5, 2].length) (baseStart_3251875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251875 prefixEnd_3251875 := by exact prefixLift 3251875
  have htrace : WordTrace (prefixWord ++ tailWord_3251875) baseStart_3251875 baseEnd_3251875 := by
    simpa [prefixWord, tailWord_3251875, baseEnd_3251875] using wordTrace_append hprefix tailTrace_3251875
  have hstable : (prefixWord ++ tailWord_3251875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251875).length < 2 ^ (prefixWord ++ tailWord_3251875).sum := by decide
  have hdescent : baseEnd_3251875 < baseStart_3251875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251885 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 4, 5]
def baseStart_3251885 : Nat := 118140960795 + 3251885 * 2 ^ 59
def prefixEnd_3251885 : Nat := 4983230072969 + 3 ^ 40 * 3251885 * 2
def baseEnd_3251885 : Nat := 556593346048704906227453

theorem tailTrace_3251885 : CollatzResearch.WordTrace tailWord_3251885 prefixEnd_3251885 556593346048704906227453 := by
  unfold tailWord_3251885
  simp only [CollatzResearch.WordTrace]
  refine ⟨118605989823983497587229109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79070659882655665058152739 118605989823983497587229109)
  ·
    refine ⟨11119311545998452898802729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118605989823983497587229109 11119311545998452898802729)
    ·
      refine ⟨8339483659498839674102047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11119311545998452898802729 8339483659498839674102047)
      ·
        refine ⟨12509225489248259511153071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8339483659498839674102047 12509225489248259511153071)
        ·
          refine ⟨18763838233872389266729607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12509225489248259511153071 18763838233872389266729607)
          ·
            refine ⟨28145757350808583900094411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18763838233872389266729607 28145757350808583900094411)
            ·
              refine ⟨42218636026212875850141617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28145757350808583900094411 42218636026212875850141617)
              ·
                refine ⟨31663977019659656887606213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42218636026212875850141617 31663977019659656887606213)
                ·
                  refine ⟨5936995691186185666426165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31663977019659656887606213 5936995691186185666426165)
                  ·
                    refine ⟨556593346048704906227453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5936995691186185666426165 556593346048704906227453)
                    ·
                      rfl

theorem cell23_3251885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_3251885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251885 prefixEnd_3251885 := by exact prefixLift 3251885
  have htrace : WordTrace (prefixWord ++ tailWord_3251885) baseStart_3251885 baseEnd_3251885 := by
    simpa [prefixWord, tailWord_3251885, baseEnd_3251885] using wordTrace_append hprefix tailTrace_3251885
  have hstable : (prefixWord ++ tailWord_3251885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251885).length < 2 ^ (prefixWord ++ tailWord_3251885).sum := by decide
  have hdescent : baseEnd_3251885 < baseStart_3251885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251888 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 4]
def baseStart_3251888 : Nat := 118140960795 + 3251888 * 2 ^ 59
def prefixEnd_3251888 : Nat := 4983230072969 + 3 ^ 40 * 3251888 * 2
def baseEnd_3251888 : Nat := 1669781578588078206944845

theorem tailTrace_3251888 : CollatzResearch.WordTrace tailWord_3251888 prefixEnd_3251888 1669781578588078206944845 := by
  unfold tailWord_3251888
  simp only [CollatzResearch.WordTrace]
  refine ⟨59303049621486314549794159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79070732828648419399725545 59303049621486314549794159)
  ·
    refine ⟨88954574432229471824691239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59303049621486314549794159 88954574432229471824691239)
    ·
      refine ⟨133431861648344207737036859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88954574432229471824691239 133431861648344207737036859)
      ·
        refine ⟨200147792472516311605555289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133431861648344207737036859 200147792472516311605555289)
        ·
          refine ⟨150110844354387233704166467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200147792472516311605555289 150110844354387233704166467)
          ·
            refine ⟨225166266531580850556249701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150110844354387233704166467 225166266531580850556249701)
            ·
              refine ⟨42218674974671409479296819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225166266531580850556249701 42218674974671409479296819)
              ·
                refine ⟨63328012462007114218945229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42218674974671409479296819 63328012462007114218945229)
                ·
                  refine ⟨23748004673252667832104461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63328012462007114218945229 23748004673252667832104461)
                  ·
                    refine ⟨8905501752469750437039173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23748004673252667832104461 8905501752469750437039173)
                    ·
                      refine ⟨1669781578588078206944845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8905501752469750437039173 1669781578588078206944845)
                      ·
                        rfl

theorem cell23_3251888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 4].length) (baseStart_3251888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251888 prefixEnd_3251888 := by exact prefixLift 3251888
  have htrace : WordTrace (prefixWord ++ tailWord_3251888) baseStart_3251888 baseEnd_3251888 := by
    simpa [prefixWord, tailWord_3251888, baseEnd_3251888] using wordTrace_append hprefix tailTrace_3251888
  have hstable : (prefixWord ++ tailWord_3251888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251888).length < 2 ^ (prefixWord ++ tailWord_3251888).sum := by decide
  have hdescent : baseEnd_3251888 < baseStart_3251888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251902 : List Nat := [4, 2, 1, 1, 2, 3, 2, 1, 2, 5]
def baseStart_3251902 : Nat := 118140960795 + 3251902 * 2 ^ 59
def prefixEnd_3251902 : Nat := 4983230072969 + 3 ^ 40 * 3251902 * 2
def baseEnd_3251902 : Nat := 556596255772413717389927

theorem tailTrace_3251902 : CollatzResearch.WordTrace tailWord_3251902 prefixEnd_3251902 556596255772413717389927 := by
  unfold tailWord_3251902
  simp only [CollatzResearch.WordTrace]
  refine ⟨14825826233115238686324745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79071073243281272993731973 14825826233115238686324745)
  ·
    refine ⟨11119369674836429014743559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14825826233115238686324745 11119369674836429014743559)
    ·
      refine ⟨16679054512254643522115339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11119369674836429014743559 16679054512254643522115339)
      ·
        refine ⟨25018581768381965283173009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16679054512254643522115339 25018581768381965283173009)
        ·
          refine ⟨18763936326286473962379757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25018581768381965283173009 18763936326286473962379757)
          ·
            refine ⟨7036476122357427735892409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18763936326286473962379757 7036476122357427735892409)
            ·
              refine ⟨5277357091768070801919307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7036476122357427735892409 5277357091768070801919307)
              ·
                refine ⟨7916035637652106202878961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5277357091768070801919307 7916035637652106202878961)
                ·
                  refine ⟨5937026728239079652159221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7916035637652106202878961 5937026728239079652159221)
                  ·
                    refine ⟨556596255772413717389927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5937026728239079652159221 556596255772413717389927)
                    ·
                      rfl

theorem cell23_3251902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_3251902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251902 prefixEnd_3251902 := by exact prefixLift 3251902
  have htrace : WordTrace (prefixWord ++ tailWord_3251902) baseStart_3251902 baseEnd_3251902 := by
    simpa [prefixWord, tailWord_3251902, baseEnd_3251902] using wordTrace_append hprefix tailTrace_3251902
  have hstable : (prefixWord ++ tailWord_3251902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251902).length < 2 ^ (prefixWord ++ tailWord_3251902).sum := by decide
  have hdescent : baseEnd_3251902 < baseStart_3251902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251922 : List Nat := [3, 2, 2, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_3251922 : Nat := 118140960795 + 3251922 * 2 ^ 59
def prefixEnd_3251922 : Nat := 4983230072969 + 3 ^ 40 * 3251922 * 2
def baseEnd_3251922 : Nat := 1669799036930331073919689

theorem tailTrace_3251922 : CollatzResearch.WordTrace tailWord_3251922 prefixEnd_3251922 1669799036930331073919689 := by
  unfold tailWord_3251922
  simp only [CollatzResearch.WordTrace]
  refine ⟨29651834831212363226581505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79071559549899635270884013 29651834831212363226581505)
  ·
    refine ⟨22238876123409272419936129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29651834831212363226581505 22238876123409272419936129)
    ·
      refine ⟨16679157092556954314952097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22238876123409272419936129 16679157092556954314952097)
      ·
        refine ⟨12509367819417715736214073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16679157092556954314952097 12509367819417715736214073)
        ·
          refine ⟨9382025864563286802160555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12509367819417715736214073 9382025864563286802160555)
          ·
            refine ⟨14073038796844930203240833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9382025864563286802160555 14073038796844930203240833)
            ·
              refine ⟨10554779097633697652430625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14073038796844930203240833 10554779097633697652430625)
              ·
                refine ⟨7916084323225273239322969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10554779097633697652430625 7916084323225273239322969)
                ·
                  refine ⟨5937063242418954929492227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7916084323225273239322969 5937063242418954929492227)
                  ·
                    refine ⟨8905594863628432394238341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5937063242418954929492227 8905594863628432394238341)
                    ·
                      refine ⟨1669799036930331073919689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8905594863628432394238341 1669799036930331073919689)
                      ·
                        rfl

theorem cell23_3251922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_3251922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251922 prefixEnd_3251922 := by exact prefixLift 3251922
  have htrace : WordTrace (prefixWord ++ tailWord_3251922) baseStart_3251922 baseEnd_3251922 := by
    simpa [prefixWord, tailWord_3251922, baseEnd_3251922] using wordTrace_append hprefix tailTrace_3251922
  have hstable : (prefixWord ++ tailWord_3251922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251922).length < 2 ^ (prefixWord ++ tailWord_3251922).sum := by decide
  have hdescent : baseEnd_3251922 < baseStart_3251922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251939 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 2, 4, 2]
def baseStart_3251939 : Nat := 118140960795 + 3251939 * 2 ^ 59
def prefixEnd_3251939 : Nat := 4983230072969 + 3 ^ 40 * 3251939 * 2
def baseEnd_3251939 : Nat := 1669807766101457507407111

theorem tailTrace_3251939 : CollatzResearch.WordTrace tailWord_3251939 prefixEnd_3251939 1669807766101457507407111 := by
  unfold tailWord_3251939
  simp only [CollatzResearch.WordTrace]
  refine ⟨118607959365787864809694871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79071972910525243206463247 118607959365787864809694871)
  ·
    refine ⟨177911939048681797214542307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118607959365787864809694871 177911939048681797214542307)
    ·
      refine ⟨266867908573022695821813461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177911939048681797214542307 266867908573022695821813461)
      ·
        refine ⟨6254716607180219433323753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 266867908573022695821813461 6254716607180219433323753)
        ·
          refine ⟨4691037455385164574992815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6254716607180219433323753 4691037455385164574992815)
          ·
            refine ⟨7036556183077746862489223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4691037455385164574992815 7036556183077746862489223)
            ·
              refine ⟨10554834274616620293733835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7036556183077746862489223 10554834274616620293733835)
              ·
                refine ⟨15832251411924930440600753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10554834274616620293733835 15832251411924930440600753)
                ·
                  refine ⟨11874188558943697830450565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15832251411924930440600753 11874188558943697830450565)
                  ·
                    refine ⟨2226410354801943343209481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11874188558943697830450565 2226410354801943343209481)
                    ·
                      refine ⟨1669807766101457507407111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2226410354801943343209481 1669807766101457507407111)
                      ·
                        rfl

theorem cell23_3251939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_3251939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251939 prefixEnd_3251939 := by exact prefixLift 3251939
  have htrace : WordTrace (prefixWord ++ tailWord_3251939) baseStart_3251939 baseEnd_3251939 := by
    simpa [prefixWord, tailWord_3251939, baseEnd_3251939] using wordTrace_append hprefix tailTrace_3251939
  have hstable : (prefixWord ++ tailWord_3251939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251939).length < 2 ^ (prefixWord ++ tailWord_3251939).sum := by decide
  have hdescent : baseEnd_3251939 < baseStart_3251939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251956 : List Nat := [2, 6, 1, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_3251956 : Nat := 118140960795 + 3251956 * 2 ^ 59
def prefixEnd_3251956 : Nat := 4983230072969 + 3 ^ 40 * 3251956 * 2
def baseEnd_3251956 : Nat := 1669816495272583940894533

theorem tailTrace_3251956 : CollatzResearch.WordTrace tailWord_3251956 prefixEnd_3251956 1669816495272583940894533 := by
  unfold tailWord_3251956
  simp only [CollatzResearch.WordTrace]
  refine ⟨59304289703363138356531861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79072386271150851142042481 59304289703363138356531861)
  ·
    refine ⟨2779888579845147110462431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 59304289703363138356531861 2779888579845147110462431)
    ·
      refine ⟨4169832869767720665693647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2779888579845147110462431 4169832869767720665693647)
      ·
        refine ⟨6254749304651580998540471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4169832869767720665693647 6254749304651580998540471)
        ·
          refine ⟨9382123956977371497810707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6254749304651580998540471 9382123956977371497810707)
          ·
            refine ⟨14073185935466057246716061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9382123956977371497810707 14073185935466057246716061)
            ·
              refine ⟨5277444725799771467518523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14073185935466057246716061 5277444725799771467518523)
              ·
                refine ⟨7916167088699657201277785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5277444725799771467518523 7916167088699657201277785)
                ·
                  refine ⟨5937125316524742900958339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7916167088699657201277785 5937125316524742900958339)
                  ·
                    refine ⟨8905687974787114351437509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5937125316524742900958339 8905687974787114351437509)
                    ·
                      refine ⟨1669816495272583940894533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8905687974787114351437509 1669816495272583940894533)
                      ·
                        rfl

theorem cell23_3251956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_3251956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251956 prefixEnd_3251956 := by exact prefixLift 3251956
  have htrace : WordTrace (prefixWord ++ tailWord_3251956) baseStart_3251956 baseEnd_3251956 := by
    simpa [prefixWord, tailWord_3251956, baseEnd_3251956] using wordTrace_append hprefix tailTrace_3251956
  have hstable : (prefixWord ++ tailWord_3251956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251956).length < 2 ^ (prefixWord ++ tailWord_3251956).sum := by decide
  have hdescent : baseEnd_3251956 < baseStart_3251956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251968 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 7]
def baseStart_3251968 : Nat := 118140960795 + 3251968 * 2 ^ 59
def prefixEnd_3251968 : Nat := 4983230072969 + 3 ^ 40 * 3251968 * 2
def baseEnd_3251968 : Nat := 1669822657040437893944477

theorem tailTrace_3251968 : CollatzResearch.WordTrace tailWord_3251968 prefixEnd_3251968 1669822657040437893944477 := by
  unfold tailWord_3251968
  simp only [CollatzResearch.WordTrace]
  refine ⟨59304508541341401381250279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79072678055121868508333705 59304508541341401381250279)
  ·
    refine ⟨88956762812012102071875419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59304508541341401381250279 88956762812012102071875419)
    ·
      refine ⟨133435144218018153107813129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88956762812012102071875419 133435144218018153107813129)
      ·
        refine ⟨100076358163513614830859847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133435144218018153107813129 100076358163513614830859847)
        ·
          refine ⟨150114537245270422246289771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100076358163513614830859847 150114537245270422246289771)
          ·
            refine ⟨225171805867905633369434657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150114537245270422246289771 225171805867905633369434657)
            ·
              refine ⟨168878854400929225027075993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225171805867905633369434657 168878854400929225027075993)
              ·
                refine ⟨126659140800696918770306995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168878854400929225027075993 126659140800696918770306995)
                ·
                  refine ⟨189988711201045378155460493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126659140800696918770306995 189988711201045378155460493)
                  ·
                    refine ⟨71245766700392016808297685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 189988711201045378155460493 71245766700392016808297685)
                    ·
                      refine ⟨1669822657040437893944477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 71245766700392016808297685 1669822657040437893944477)
                      ·
                        rfl

theorem cell23_3251968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_3251968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251968 prefixEnd_3251968 := by exact prefixLift 3251968
  have htrace : WordTrace (prefixWord ++ tailWord_3251968) baseStart_3251968 baseEnd_3251968 := by
    simpa [prefixWord, tailWord_3251968, baseEnd_3251968] using wordTrace_append hprefix tailTrace_3251968
  have hstable : (prefixWord ++ tailWord_3251968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251968).length < 2 ^ (prefixWord ++ tailWord_3251968).sum := by decide
  have hdescent : baseEnd_3251968 < baseStart_3251968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251989 : List Nat := [1, 3, 2, 1, 2, 4, 2, 1, 3, 1, 3]
def baseStart_3251989 : Nat := 118140960795 + 3251989 * 2 ^ 59
def prefixEnd_3251989 : Nat := 4983230072969 + 3 ^ 40 * 3251989 * 2
def baseEnd_3251989 : Nat := 1669833440134182311781881

theorem tailTrace_3251989 : CollatzResearch.WordTrace tailWord_3251989 prefixEnd_3251989 1669833440134182311781881 := by
  unfold tailWord_3251989
  simp only [CollatzResearch.WordTrace]
  refine ⟨118609783015606723349015021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79073188677071148899343347 118609783015606723349015021)
  ·
    refine ⟨44478668630852521255880633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118609783015606723349015021 44478668630852521255880633)
    ·
      refine ⟨33359001473139390941910475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44478668630852521255880633 33359001473139390941910475)
      ·
        refine ⟨50038502209709086412865713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33359001473139390941910475 50038502209709086412865713)
        ·
          refine ⟨37528876657281814809649285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50038502209709086412865713 37528876657281814809649285)
          ·
            refine ⟨7036664373240340276809241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37528876657281814809649285 7036664373240340276809241)
            ·
              refine ⟨5277498279930255207606931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7036664373240340276809241 5277498279930255207606931)
              ·
                refine ⟨7916247419895382811410397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5277498279930255207606931 7916247419895382811410397)
                ·
                  refine ⟨2968592782460768554278899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7916247419895382811410397 2968592782460768554278899)
                  ·
                    refine ⟨4452889173691152831418349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2968592782460768554278899 4452889173691152831418349)
                    ·
                      refine ⟨1669833440134182311781881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4452889173691152831418349 1669833440134182311781881)
                      ·
                        rfl

theorem cell23_3251989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_3251989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251989 prefixEnd_3251989 := by exact prefixLift 3251989
  have htrace : WordTrace (prefixWord ++ tailWord_3251989) baseStart_3251989 baseEnd_3251989 := by
    simpa [prefixWord, tailWord_3251989, baseEnd_3251989] using wordTrace_append hprefix tailTrace_3251989
  have hstable : (prefixWord ++ tailWord_3251989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251989).length < 2 ^ (prefixWord ++ tailWord_3251989).sum := by decide
  have hdescent : baseEnd_3251989 < baseStart_3251989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252012 : List Nat := [2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 4]
def baseStart_3252012 : Nat := 118140960795 + 3252012 * 2 ^ 59
def prefixEnd_3252012 : Nat := 4983230072969 + 3 ^ 40 * 3252012 * 2
def baseEnd_3252012 : Nat := 1669845250189235721794275

theorem tailTrace_3252012 : CollatzResearch.WordTrace tailWord_3252012 prefixEnd_3252012 1669845250189235721794275 := by
  unfold tailWord_3252012
  simp only [CollatzResearch.WordTrace]
  refine ⟨59305310947261699138551145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79073747929682265518068193 59305310947261699138551145)
  ·
    refine ⟨44478983210446274353913359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59305310947261699138551145 44478983210446274353913359)
    ·
      refine ⟨66718474815669411530870039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44478983210446274353913359 66718474815669411530870039)
      ·
        refine ⟨100077712223504117296305059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66718474815669411530870039 100077712223504117296305059)
        ·
          refine ⟨150116568335256175944457589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100077712223504117296305059 150116568335256175944457589)
          ·
            refine ⟨14073428281430266494792899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150116568335256175944457589 14073428281430266494792899)
            ·
              refine ⟨21110142422145399742189349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14073428281430266494792899 21110142422145399742189349)
              ·
                refine ⟨3958151704152262451660503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21110142422145399742189349 3958151704152262451660503)
                ·
                  refine ⟨5937227556228393677490755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3958151704152262451660503 5937227556228393677490755)
                  ·
                    refine ⟨8905841334342590516236133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5937227556228393677490755 8905841334342590516236133)
                    ·
                      refine ⟨1669845250189235721794275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8905841334342590516236133 1669845250189235721794275)
                      ·
                        rfl

theorem cell23_3252012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 4].length) (baseStart_3252012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252012 prefixEnd_3252012 := by exact prefixLift 3252012
  have htrace : WordTrace (prefixWord ++ tailWord_3252012) baseStart_3252012 baseEnd_3252012 := by
    simpa [prefixWord, tailWord_3252012, baseEnd_3252012] using wordTrace_append hprefix tailTrace_3252012
  have hstable : (prefixWord ++ tailWord_3252012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252012).length < 2 ^ (prefixWord ++ tailWord_3252012).sum := by decide
  have hdescent : baseEnd_3252012 < baseStart_3252012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252029 : List Nat := [1, 4, 1, 4, 1, 1, 2, 3, 1, 1, 4]
def baseStart_3252029 : Nat := 118140960795 + 3252029 * 2 ^ 59
def prefixEnd_3252029 : Nat := 4983230072969 + 3 ^ 40 * 3252029 * 2
def baseEnd_3252029 : Nat := 1669853979360362155281697

theorem tailTrace_3252029 : CollatzResearch.WordTrace tailWord_3252029 prefixEnd_3252029 1669853979360362155281697 := by
  unfold tailWord_3252029
  simp only [CollatzResearch.WordTrace]
  refine ⟨118611241935461810180471141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79074161290307873453647427 118611241935461810180471141)
  ·
    refine ⟨22239607862899089408838339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118611241935461810180471141 22239607862899089408838339)
    ·
      refine ⟨33359411794348634113257509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22239607862899089408838339 33359411794348634113257509)
      ·
        refine ⟨6254889711440368896235783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33359411794348634113257509 6254889711440368896235783)
        ·
          refine ⟨9382334567160553344353675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6254889711440368896235783 9382334567160553344353675)
          ·
            refine ⟨14073501850740830016530513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9382334567160553344353675 14073501850740830016530513)
            ·
              refine ⟨10555126388055622512397885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14073501850740830016530513 10555126388055622512397885)
              ·
                refine ⟨3958172395520858442149207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10555126388055622512397885 3958172395520858442149207)
                ·
                  refine ⟨5937258593281287663223811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3958172395520858442149207 5937258593281287663223811)
                  ·
                    refine ⟨8905887889921931494835717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5937258593281287663223811 8905887889921931494835717)
                    ·
                      refine ⟨1669853979360362155281697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8905887889921931494835717 1669853979360362155281697)
                      ·
                        rfl

theorem cell23_3252029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_3252029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252029 prefixEnd_3252029 := by exact prefixLift 3252029
  have htrace : WordTrace (prefixWord ++ tailWord_3252029) baseStart_3252029 baseEnd_3252029 := by
    simpa [prefixWord, tailWord_3252029, baseEnd_3252029] using wordTrace_append hprefix tailTrace_3252029
  have hstable : (prefixWord ++ tailWord_3252029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252029).length < 2 ^ (prefixWord ++ tailWord_3252029).sum := by decide
  have hdescent : baseEnd_3252029 < baseStart_3252029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252035 : List Nat := [1, 1, 1, 3, 1, 7, 9]
def baseStart_3252035 : Nat := 118140960795 + 3252035 * 2 ^ 59
def prefixEnd_3252035 : Nat := 4983230072969 + 3 ^ 40 * 3252035 * 2
def baseEnd_3252035 : Nat := 20615519262275174466749

theorem tailTrace_3252035 : CollatzResearch.WordTrace tailWord_3252035 prefixEnd_3252035 20615519262275174466749 := by
  unfold tailWord_3252035
  simp only [CollatzResearch.WordTrace]
  refine ⟨118611460773440073205189559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79074307182293382136793039 118611460773440073205189559)
  ·
    refine ⟨177917191160160109807784339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118611460773440073205189559 177917191160160109807784339)
    ·
      refine ⟨266875786740240164711676509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177917191160160109807784339 266875786740240164711676509)
      ·
        refine ⟨100078420027590061766878691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266875786740240164711676509 100078420027590061766878691)
        ·
          refine ⟨150117630041385092650318037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100078420027590061766878691 150117630041385092650318037)
          ·
            refine ⟨3518381954094963108991829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 150117630041385092650318037 3518381954094963108991829)
            ·
              refine ⟨20615519262275174466749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3518381954094963108991829 20615519262275174466749)
              ·
                rfl

theorem cell23_3252035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 9].length) (baseStart_3252035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252035 prefixEnd_3252035 := by exact prefixLift 3252035
  have htrace : WordTrace (prefixWord ++ tailWord_3252035) baseStart_3252035 baseEnd_3252035 := by
    simpa [prefixWord, tailWord_3252035, baseEnd_3252035] using wordTrace_append hprefix tailTrace_3252035
  have hstable : (prefixWord ++ tailWord_3252035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252035).length < 2 ^ (prefixWord ++ tailWord_3252035).sum := by decide
  have hdescent : baseEnd_3252035 < baseStart_3252035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252052 : List Nat := [2, 4, 1, 1, 3, 2, 2, 8]
def baseStart_3252052 : Nat := 118140960795 + 3252052 * 2 ^ 59
def prefixEnd_3252052 : Nat := 4983230072969 + 3 ^ 40 * 3252052 * 2
def baseEnd_3252052 : Nat := 61846881089459835751633

theorem tailTrace_3252052 : CollatzResearch.WordTrace tailWord_3252052 prefixEnd_3252052 61846881089459835751633 := by
  unfold tailWord_3252052
  simp only [CollatzResearch.WordTrace]
  refine ⟨59306040407189242554279205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79074720542918990072372273 59306040407189242554279205)
  ·
    refine ⟨11119882576347982978927351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59306040407189242554279205 11119882576347982978927351)
    ·
      refine ⟨16679823864521974468391027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11119882576347982978927351 16679823864521974468391027)
      ·
        refine ⟨25019735796782961702586541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16679823864521974468391027 25019735796782961702586541)
        ·
          refine ⟨9382400923793610638469953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25019735796782961702586541 9382400923793610638469953)
          ·
            refine ⟨7036800692845207978852465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9382400923793610638469953 7036800692845207978852465)
            ·
              refine ⟨5277600519633905984139349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7036800692845207978852465 5277600519633905984139349)
              ·
                refine ⟨61846881089459835751633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5277600519633905984139349 61846881089459835751633)
                ·
                  rfl

theorem cell23_3252052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 8].length) (baseStart_3252052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252052 prefixEnd_3252052 := by exact prefixLift 3252052
  have htrace : WordTrace (prefixWord ++ tailWord_3252052) baseStart_3252052 baseEnd_3252052 := by
    simpa [prefixWord, tailWord_3252052, baseEnd_3252052] using wordTrace_append hprefix tailTrace_3252052
  have hstable : (prefixWord ++ tailWord_3252052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252052).length < 2 ^ (prefixWord ++ tailWord_3252052).sum := by decide
  have hdescent : baseEnd_3252052 < baseStart_3252052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252066 : List Nat := [3, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_3252066 : Nat := 118140960795 + 3252066 * 2 ^ 59
def prefixEnd_3252066 : Nat := 4983230072969 + 3 ^ 40 * 3252066 * 2
def baseEnd_3252066 : Nat := 1669872978144578510519027

theorem tailTrace_3252066 : CollatzResearch.WordTrace tailWord_3252066 prefixEnd_3252066 1669872978144578510519027 := by
  unfold tailWord_3252066
  simp only [CollatzResearch.WordTrace]
  refine ⟨29653147859081941374892013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79075060957551843666378701 29653147859081941374892013)
  ·
    refine ⟨11119930447155728015584505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29653147859081941374892013 11119930447155728015584505)
    ·
      refine ⟨8339947835366796011688379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11119930447155728015584505 8339947835366796011688379)
      ·
        refine ⟨12509921753050194017532569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8339947835366796011688379 12509921753050194017532569)
        ·
          refine ⟨9382441314787645513149427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12509921753050194017532569 9382441314787645513149427)
          ·
            refine ⟨14073661972181468269724141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9382441314787645513149427 14073661972181468269724141)
            ·
              refine ⟨5277623239568050601146553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14073661972181468269724141 5277623239568050601146553)
              ·
                refine ⟨3958217429676037950859915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5277623239568050601146553 3958217429676037950859915)
                ·
                  refine ⟨5937326144514056926289873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3958217429676037950859915 5937326144514056926289873)
                  ·
                    refine ⟨4452994608385542694717405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5937326144514056926289873 4452994608385542694717405)
                    ·
                      refine ⟨1669872978144578510519027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4452994608385542694717405 1669872978144578510519027)
                      ·
                        rfl

theorem cell23_3252066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_3252066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252066 prefixEnd_3252066 := by exact prefixLift 3252066
  have htrace : WordTrace (prefixWord ++ tailWord_3252066) baseStart_3252066 baseEnd_3252066 := by
    simpa [prefixWord, tailWord_3252066, baseEnd_3252066] using wordTrace_append hprefix tailTrace_3252066
  have hstable : (prefixWord ++ tailWord_3252066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252066).length < 2 ^ (prefixWord ++ tailWord_3252066).sum := by decide
  have hdescent : baseEnd_3252066 < baseStart_3252066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252095 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 2, 6]
def baseStart_3252095 : Nat := 118140960795 + 3252095 * 2 ^ 59
def prefixEnd_3252095 : Nat := 4983230072969 + 3 ^ 40 * 3252095 * 2
def baseEnd_3252095 : Nat := 556629289694519632352131

theorem tailTrace_3252095 : CollatzResearch.WordTrace tailWord_3252095 prefixEnd_3252095 556629289694519632352131 := by
  unfold tailWord_3252095
  simp only [CollatzResearch.WordTrace]
  refine ⟨118613649153222703452373739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79075766102148468968249159 118613649153222703452373739)
  ·
    refine ⟨177920473729834055178560609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118613649153222703452373739 177920473729834055178560609)
    ·
      refine ⟨133440355297375541383920457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177920473729834055178560609 133440355297375541383920457)
      ·
        refine ⟨100080266473031656037940343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133440355297375541383920457 100080266473031656037940343)
        ·
          refine ⟨150120399709547484056910515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100080266473031656037940343 150120399709547484056910515)
          ·
            refine ⟨225180599564321226085365773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150120399709547484056910515 225180599564321226085365773)
            ·
              refine ⟨84442724836620459782012165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225180599564321226085365773 84442724836620459782012165)
              ·
                refine ⟨15833010906866336209127281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84442724836620459782012165 15833010906866336209127281)
                ·
                  refine ⟨11874758180149752156845461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15833010906866336209127281 11874758180149752156845461)
                  ·
                    refine ⟨556629289694519632352131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11874758180149752156845461 556629289694519632352131)
                    ·
                      rfl

theorem cell23_3252095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 6].length) (baseStart_3252095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252095 prefixEnd_3252095 := by exact prefixLift 3252095
  have htrace : WordTrace (prefixWord ++ tailWord_3252095) baseStart_3252095 baseEnd_3252095 := by
    simpa [prefixWord, tailWord_3252095, baseEnd_3252095] using wordTrace_append hprefix tailTrace_3252095
  have hstable : (prefixWord ++ tailWord_3252095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252095).length < 2 ^ (prefixWord ++ tailWord_3252095).sum := by decide
  have hdescent : baseEnd_3252095 < baseStart_3252095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252119 : List Nat := [1, 1, 3, 3, 1, 3, 1, 3, 1, 4, 2]
def baseStart_3252119 : Nat := 118140960795 + 3252119 * 2 ^ 59
def prefixEnd_3252119 : Nat := 4983230072969 + 3 ^ 40 * 3252119 * 2
def baseEnd_3252119 : Nat := 1669900192619266803156283

theorem tailTrace_3252119 : CollatzResearch.WordTrace tailWord_3252119 prefixEnd_3252119 1669900192619266803156283 := by
  unfold tailWord_3252119
  simp only [CollatzResearch.WordTrace]
  refine ⟨118614524505135755551247411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79076349670090503700831607 118614524505135755551247411)
  ·
    refine ⟨177921786757703633326871117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118614524505135755551247411 177921786757703633326871117)
    ·
      refine ⟨66720670034138862497576669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177921786757703633326871117 66720670034138862497576669)
      ·
        refine ⟨25020251262802073436591251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66720670034138862497576669 25020251262802073436591251)
        ·
          refine ⟨37530376894203110154886877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25020251262802073436591251 37530376894203110154886877)
          ·
            refine ⟨14073891335326166308082579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37530376894203110154886877 14073891335326166308082579)
            ·
              refine ⟨21110837002989249462123869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14073891335326166308082579 21110837002989249462123869)
              ·
                refine ⟨7916563876120968548296451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21110837002989249462123869 7916563876120968548296451)
                ·
                  refine ⟨11874845814181452822444677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7916563876120968548296451 11874845814181452822444677)
                  ·
                    refine ⟨2226533590159022404208377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11874845814181452822444677 2226533590159022404208377)
                    ·
                      refine ⟨1669900192619266803156283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2226533590159022404208377 1669900192619266803156283)
                      ·
                        rfl

theorem cell23_3252119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_3252119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252119 prefixEnd_3252119 := by exact prefixLift 3252119
  have htrace : WordTrace (prefixWord ++ tailWord_3252119) baseStart_3252119 baseEnd_3252119 := by
    simpa [prefixWord, tailWord_3252119, baseEnd_3252119] using wordTrace_append hprefix tailTrace_3252119
  have hstable : (prefixWord ++ tailWord_3252119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252119).length < 2 ^ (prefixWord ++ tailWord_3252119).sum := by decide
  have hdescent : baseEnd_3252119 < baseStart_3252119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252152 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 4, 3, 3]
def baseStart_3252152 : Nat := 118140960795 + 3252152 * 2 ^ 59
def prefixEnd_3252152 : Nat := 4983230072969 + 3 ^ 40 * 3252152 * 2
def baseEnd_3252152 : Nat := 1669917137480865174043631

theorem tailTrace_3252152 : CollatzResearch.WordTrace tailWord_3252152 prefixEnd_3252152 1669917137480865174043631 := by
  unfold tailWord_3252152
  simp only [CollatzResearch.WordTrace]
  refine ⟨59307864057008101093599355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79077152076010801458132473 59307864057008101093599355)
  ·
    refine ⟨88961796085512151640399033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59307864057008101093599355 88961796085512151640399033)
    ·
      refine ⟨66721347064134113730299275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88961796085512151640399033 66721347064134113730299275)
      ·
        refine ⟨100082020596201170595448913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66721347064134113730299275 100082020596201170595448913)
        ·
          refine ⟨75061515447150877946586685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100082020596201170595448913 75061515447150877946586685)
          ·
            refine ⟨28148068292681579229970007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75061515447150877946586685 28148068292681579229970007)
            ·
              refine ⟨42222102439022368844955011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28148068292681579229970007 42222102439022368844955011)
              ·
                refine ⟨63333153658533553267432517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42222102439022368844955011 63333153658533553267432517)
                ·
                  refine ⟨11874966310975041237643597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63333153658533553267432517 11874966310975041237643597)
                  ·
                    refine ⟨4453112366615640464116349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11874966310975041237643597 4453112366615640464116349)
                    ·
                      refine ⟨1669917137480865174043631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4453112366615640464116349 1669917137480865174043631)
                      ·
                        rfl

theorem cell23_3252152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 4, 3, 3].length) (baseStart_3252152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252152 prefixEnd_3252152 := by exact prefixLift 3252152
  have htrace : WordTrace (prefixWord ++ tailWord_3252152) baseStart_3252152 baseEnd_3252152 := by
    simpa [prefixWord, tailWord_3252152, baseEnd_3252152] using wordTrace_append hprefix tailTrace_3252152
  have hstable : (prefixWord ++ tailWord_3252152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252152).length < 2 ^ (prefixWord ++ tailWord_3252152).sum := by decide
  have hdescent : baseEnd_3252152 < baseStart_3252152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252155 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 3, 7]
def baseStart_3252155 : Nat := 118140960795 + 3252155 * 2 ^ 59
def prefixEnd_3252155 : Nat := 4983230072969 + 3 ^ 40 * 3252155 * 2
def baseEnd_3252155 : Nat := 556639559307609554102039

theorem tailTrace_3252155 : CollatzResearch.WordTrace tailWord_3252155 prefixEnd_3252155 556639559307609554102039 := by
  unfold tailWord_3252155
  simp only [CollatzResearch.WordTrace]
  refine ⟨118615837533005333699557919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79077225022003555799705279 118615837533005333699557919)
  ·
    refine ⟨177923756299508000549336879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118615837533005333699557919 177923756299508000549336879)
    ·
      refine ⟨266885634449262000824005319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177923756299508000549336879 266885634449262000824005319)
      ·
        refine ⟨400328451673893001236007979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266885634449262000824005319 400328451673893001236007979)
        ·
          refine ⟨600492677510839501854011969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400328451673893001236007979 600492677510839501854011969)
          ·
            refine ⟨450369508133129626390508977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 600492677510839501854011969 450369508133129626390508977)
            ·
              refine ⟨337777131099847219792881733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450369508133129626390508977 337777131099847219792881733)
              ·
                refine ⟨63333212081221353711165325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 337777131099847219792881733 63333212081221353711165325)
                ·
                  refine ⟨23749954530458007641686997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63333212081221353711165325 23749954530458007641686997)
                  ·
                    refine ⟨556639559307609554102039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23749954530458007641686997 556639559307609554102039)
                    ·
                      rfl

theorem cell23_3252155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 7].length) (baseStart_3252155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252155 prefixEnd_3252155 := by exact prefixLift 3252155
  have htrace : WordTrace (prefixWord ++ tailWord_3252155) baseStart_3252155 baseEnd_3252155 := by
    simpa [prefixWord, tailWord_3252155, baseEnd_3252155] using wordTrace_append hprefix tailTrace_3252155
  have hstable : (prefixWord ++ tailWord_3252155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252155).length < 2 ^ (prefixWord ++ tailWord_3252155).sum := by decide
  have hdescent : baseEnd_3252155 < baseStart_3252155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252172 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 1, 7]
def baseStart_3252172 : Nat := 118140960795 + 3252172 * 2 ^ 59
def prefixEnd_3252172 : Nat := 4983230072969 + 3 ^ 40 * 3252172 * 2
def baseEnd_3252172 : Nat := 556642469031318365264513

theorem tailTrace_3252172 : CollatzResearch.WordTrace tailWord_3252172 prefixEnd_3252172 556642469031318365264513 := by
  unfold tailWord_3252172
  simp only [CollatzResearch.WordTrace]
  refine ⟨59308228786971872801463385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79077638382629163735284513 59308228786971872801463385)
  ·
    refine ⟨44481171590228904601097539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59308228786971872801463385 44481171590228904601097539)
    ·
      refine ⟨66721757385343356901646309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44481171590228904601097539 66721757385343356901646309)
      ·
        refine ⟨12510329509751879419058683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66721757385343356901646309 12510329509751879419058683)
        ·
          refine ⟨18765494264627819128588025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12510329509751879419058683 18765494264627819128588025)
          ·
            refine ⟨14074120698470864346441019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18765494264627819128588025 14074120698470864346441019)
            ·
              refine ⟨21111181047706296519661529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14074120698470864346441019 21111181047706296519661529)
              ·
                refine ⟨15833385785779722389746147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21111181047706296519661529 15833385785779722389746147)
                ·
                  refine ⟨23750078678669583584619221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15833385785779722389746147 23750078678669583584619221)
                  ·
                    refine ⟨556642469031318365264513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23750078678669583584619221 556642469031318365264513)
                    ·
                      rfl

theorem cell23_3252172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_3252172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252172 prefixEnd_3252172 := by exact prefixLift 3252172
  have htrace : WordTrace (prefixWord ++ tailWord_3252172) baseStart_3252172 baseEnd_3252172 := by
    simpa [prefixWord, tailWord_3252172, baseEnd_3252172] using wordTrace_append hprefix tailTrace_3252172
  have hstable : (prefixWord ++ tailWord_3252172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252172).length < 2 ^ (prefixWord ++ tailWord_3252172).sum := by decide
  have hdescent : baseEnd_3252172 < baseStart_3252172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252192 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 4]
def baseStart_3252192 : Nat := 118140960795 + 3252192 * 2 ^ 59
def prefixEnd_3252192 : Nat := 4983230072969 + 3 ^ 40 * 3252192 * 2
def baseEnd_3252192 : Nat := 1669937676707045017543447

theorem tailTrace_3252192 : CollatzResearch.WordTrace tailWord_3252192 prefixEnd_3252192 1669937676707045017543447 := by
  unfold tailWord_3252192
  simp only [CollatzResearch.WordTrace]
  refine ⟨59308593516935644509327415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79078124689247526012436553 59308593516935644509327415)
  ·
    refine ⟨88962890275403466763991123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59308593516935644509327415 88962890275403466763991123)
    ·
      refine ⟨133444335413105200145986685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88962890275403466763991123 133444335413105200145986685)
      ·
        refine ⟨50041625779914450054745007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133444335413105200145986685 50041625779914450054745007)
        ·
          refine ⟨75062438669871675082117511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50041625779914450054745007 75062438669871675082117511)
          ·
            refine ⟨112593658004807512623176267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75062438669871675082117511 112593658004807512623176267)
            ·
              refine ⟨168890487007211268934764401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112593658004807512623176267 168890487007211268934764401)
              ·
                refine ⟨126667865255408451701073301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168890487007211268934764401 126667865255408451701073301)
                ·
                  refine ⟨5937556183847271173487811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 126667865255408451701073301 5937556183847271173487811)
                  ·
                    refine ⟨8906334275770906760231717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5937556183847271173487811 8906334275770906760231717)
                    ·
                      refine ⟨1669937676707045017543447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8906334275770906760231717 1669937676707045017543447)
                      ·
                        rfl

theorem cell23_3252192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_3252192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252192 prefixEnd_3252192 := by exact prefixLift 3252192
  have htrace : WordTrace (prefixWord ++ tailWord_3252192) baseStart_3252192 baseEnd_3252192 := by
    simpa [prefixWord, tailWord_3252192, baseEnd_3252192] using wordTrace_append hprefix tailTrace_3252192
  have hstable : (prefixWord ++ tailWord_3252192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252192).length < 2 ^ (prefixWord ++ tailWord_3252192).sum := by decide
  have hdescent : baseEnd_3252192 < baseStart_3252192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252219 : List Nat := [1, 1, 1, 1, 1, 3, 7, 1, 3, 4]
def baseStart_3252219 : Nat := 118140960795 + 3252219 * 2 ^ 59
def prefixEnd_3252219 : Nat := 4983230072969 + 3 ^ 40 * 3252219 * 2
def baseEnd_3252219 : Nat := 556650513561572137301941

theorem tailTrace_3252219 : CollatzResearch.WordTrace tailWord_3252219 prefixEnd_3252219 556650513561572137301941 := by
  unfold tailWord_3252219
  simp only [CollatzResearch.WordTrace]
  refine ⟨118618171804773472629887711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79078781203182315086591807 118618171804773472629887711)
  ·
    refine ⟨177927257707160208944831567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118618171804773472629887711 177927257707160208944831567)
    ·
      refine ⟨266890886560740313417247351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177927257707160208944831567 266890886560740313417247351)
      ·
        refine ⟨400336329841110470125871027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266890886560740313417247351 400336329841110470125871027)
        ·
          refine ⟨600504494761665705188806541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400336329841110470125871027 600504494761665705188806541)
          ·
            refine ⟨225189185535624639445802453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 600504494761665705188806541 225189185535624639445802453)
            ·
              refine ⟨5277871535991202487010995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 225189185535624639445802453 5277871535991202487010995)
              ·
                refine ⟨7916807303986803730516493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5277871535991202487010995 7916807303986803730516493)
                ·
                  refine ⟨2968802738995051398943685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7916807303986803730516493 2968802738995051398943685)
                  ·
                    refine ⟨556650513561572137301941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2968802738995051398943685 556650513561572137301941)
                    ·
                      rfl

theorem cell23_3252219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 4].length) (baseStart_3252219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252219 prefixEnd_3252219 := by exact prefixLift 3252219
  have htrace : WordTrace (prefixWord ++ tailWord_3252219) baseStart_3252219 baseEnd_3252219 := by
    simpa [prefixWord, tailWord_3252219, baseEnd_3252219] using wordTrace_append hprefix tailTrace_3252219
  have hstable : (prefixWord ++ tailWord_3252219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252219).length < 2 ^ (prefixWord ++ tailWord_3252219).sum := by decide
  have hdescent : baseEnd_3252219 < baseStart_3252219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252266 : List Nat := [3, 1, 4, 1, 2, 2, 2, 2, 6]
def baseStart_3252266 : Nat := 118140960795 + 3252266 * 2 ^ 59
def prefixEnd_3252266 : Nat := 4983230072969 + 3 ^ 40 * 3252266 * 2
def baseEnd_3252266 : Nat := 185552852697275303113123

theorem tailTrace_3252266 : CollatzResearch.WordTrace tailWord_3252266 prefixEnd_3252266 185552852697275303113123 := by
  unfold tailWord_3252266
  simp only [CollatzResearch.WordTrace]
  refine ⟨29654971508900799914212163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79079924023735466437899101 29654971508900799914212163)
  ·
    refine ⟨44482457263351199871318245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29654971508900799914212163 44482457263351199871318245)
    ·
      refine ⟨8340460736878349975872171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44482457263351199871318245 8340460736878349975872171)
      ·
        refine ⟨12510691105317524963808257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8340460736878349975872171 12510691105317524963808257)
        ·
          refine ⟨9383018328988143722856193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12510691105317524963808257 9383018328988143722856193)
          ·
            refine ⟨7037263746741107792142145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9383018328988143722856193 7037263746741107792142145)
            ·
              refine ⟨5277947810055830844106609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7037263746741107792142145 5277947810055830844106609)
              ·
                refine ⟨3958460857541873133079957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5277947810055830844106609 3958460857541873133079957)
                ·
                  refine ⟨185552852697275303113123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3958460857541873133079957 185552852697275303113123)
                  ·
                    rfl

theorem cell23_3252266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 6].length) (baseStart_3252266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252266 prefixEnd_3252266 := by exact prefixLift 3252266
  have htrace : WordTrace (prefixWord ++ tailWord_3252266) baseStart_3252266 baseEnd_3252266 := by
    simpa [prefixWord, tailWord_3252266, baseEnd_3252266] using wordTrace_append hprefix tailTrace_3252266
  have hstable : (prefixWord ++ tailWord_3252266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252266).length < 2 ^ (prefixWord ++ tailWord_3252266).sum := by decide
  have hdescent : baseEnd_3252266 < baseStart_3252266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252270 : List Nat := [4, 1, 3, 1, 1, 2, 4, 2, 1, 4]
def baseStart_3252270 : Nat := 118140960795 + 3252270 * 2 ^ 59
def prefixEnd_3252270 : Nat := 4983230072969 + 3 ^ 40 * 3252270 * 2
def baseEnd_3252270 : Nat := 556659242732698570789363

theorem tailTrace_3252270 : CollatzResearch.WordTrace tailWord_3252270 prefixEnd_3252270 556659242732698570789363 := by
  unfold tailWord_3252270
  simp only [CollatzResearch.WordTrace]
  refine ⟨14827503990948588542499283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79080021285059138893329509 14827503990948588542499283)
  ·
    refine ⟨22241255986422882813748925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14827503990948588542499283 22241255986422882813748925)
    ·
      refine ⟨8340470994908581055155847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22241255986422882813748925 8340470994908581055155847)
      ·
        refine ⟨12510706492362871582733771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8340470994908581055155847 12510706492362871582733771)
        ·
          refine ⟨18766059738544307374100657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12510706492362871582733771 18766059738544307374100657)
          ·
            refine ⟨14074544803908230530575493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18766059738544307374100657 14074544803908230530575493)
            ·
              refine ⟨2638977150732793224482905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14074544803908230530575493 2638977150732793224482905)
              ·
                refine ⟨1979232863049594918362179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2638977150732793224482905 1979232863049594918362179)
                ·
                  refine ⟨2968849294574392377543269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1979232863049594918362179 2968849294574392377543269)
                  ·
                    refine ⟨556659242732698570789363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2968849294574392377543269 556659242732698570789363)
                    ·
                      rfl

theorem cell23_3252270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_3252270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252270 prefixEnd_3252270 := by exact prefixLift 3252270
  have htrace : WordTrace (prefixWord ++ tailWord_3252270) baseStart_3252270 baseEnd_3252270 := by
    simpa [prefixWord, tailWord_3252270, baseEnd_3252270] using wordTrace_append hprefix tailTrace_3252270
  have hstable : (prefixWord ++ tailWord_3252270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252270).length < 2 ^ (prefixWord ++ tailWord_3252270).sum := by decide
  have hdescent : baseEnd_3252270 < baseStart_3252270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252299 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 2, 6, 2]
def baseStart_3252299 : Nat := 118140960795 + 3252299 * 2 ^ 59
def prefixEnd_3252299 : Nat := 4983230072969 + 3 ^ 40 * 3252299 * 2
def baseEnd_3252299 : Nat := 1669992619137076098905455

theorem tailTrace_3252299 : CollatzResearch.WordTrace tailWord_3252299 prefixEnd_3252299 1669992619137076098905455 := by
  unfold tailWord_3252299
  simp only [CollatzResearch.WordTrace]
  refine ⟨118621089644483646292799951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79080726429655764195199967 118621089644483646292799951)
  ·
    refine ⟨177931634466725469439199927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118621089644483646292799951 177931634466725469439199927)
    ·
      refine ⟨266897451700088204158799891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177931634466725469439199927 266897451700088204158799891)
      ·
        refine ⟨400346177550132306238199837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266897451700088204158799891 400346177550132306238199837)
        ·
          refine ⟨150129816581299614839324939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400346177550132306238199837 150129816581299614839324939)
          ·
            refine ⟨225194724871949422258987409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150129816581299614839324939 225194724871949422258987409)
            ·
              refine ⟨168896043653962066694240557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225194724871949422258987409 168896043653962066694240557)
              ·
                refine ⟨63336016370235775010340209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168896043653962066694240557 63336016370235775010340209)
                ·
                  refine ⟨47502012277676831257755157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63336016370235775010340209 47502012277676831257755157)
                  ·
                    refine ⟨2226656825516101465207273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47502012277676831257755157 2226656825516101465207273)
                    ·
                      refine ⟨1669992619137076098905455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2226656825516101465207273 1669992619137076098905455)
                      ·
                        rfl

theorem cell23_3252299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 6, 2].length) (baseStart_3252299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252299 prefixEnd_3252299 := by exact prefixLift 3252299
  have htrace : WordTrace (prefixWord ++ tailWord_3252299) baseStart_3252299 baseEnd_3252299 := by
    simpa [prefixWord, tailWord_3252299, baseEnd_3252299] using wordTrace_append hprefix tailTrace_3252299
  have hstable : (prefixWord ++ tailWord_3252299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252299).length < 2 ^ (prefixWord ++ tailWord_3252299).sum := by decide
  have hdescent : baseEnd_3252299 < baseStart_3252299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252309 : List Nat := [1, 3, 2, 2, 1, 3, 2, 2, 1, 6]
def baseStart_3252309 : Nat := 118140960795 + 3252309 * 2 ^ 59
def prefixEnd_3252309 : Nat := 4983230072969 + 3 ^ 40 * 3252309 * 2
def baseEnd_3252309 : Nat := 556665917981207019926803

theorem tailTrace_3252309 : CollatzResearch.WordTrace tailWord_3252309 prefixEnd_3252309 556665917981207019926803 := by
  unfold tailWord_3252309
  simp only [CollatzResearch.WordTrace]
  refine ⟨118621454374447418000663981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79080969582964945333775987 118621454374447418000663981)
  ·
    refine ⟨44483045390417781750248993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118621454374447418000663981 44483045390417781750248993)
    ·
      refine ⟨33362284042813336312686745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44483045390417781750248993 33362284042813336312686745)
      ·
        refine ⟨25021713032110002234515059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33362284042813336312686745 25021713032110002234515059)
        ·
          refine ⟨37532569548165003351772589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25021713032110002234515059 37532569548165003351772589)
          ·
            refine ⟨14074713580561876256914721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37532569548165003351772589 14074713580561876256914721)
            ·
              refine ⟨10556035185421407192686041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14074713580561876256914721 10556035185421407192686041)
              ·
                refine ⟨7917026389066055394514531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10556035185421407192686041 7917026389066055394514531)
                ·
                  refine ⟨11875539583599083091771797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7917026389066055394514531 11875539583599083091771797)
                  ·
                    refine ⟨556665917981207019926803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11875539583599083091771797 556665917981207019926803)
                    ·
                      rfl

theorem cell23_3252309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_3252309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252309 prefixEnd_3252309 := by exact prefixLift 3252309
  have htrace : WordTrace (prefixWord ++ tailWord_3252309) baseStart_3252309 baseEnd_3252309 := by
    simpa [prefixWord, tailWord_3252309, baseEnd_3252309] using wordTrace_append hprefix tailTrace_3252309
  have hstable : (prefixWord ++ tailWord_3252309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252309).length < 2 ^ (prefixWord ++ tailWord_3252309).sum := by decide
  have hdescent : baseEnd_3252309 < baseStart_3252309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252319 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 3]
def baseStart_3252319 : Nat := 118140960795 + 3252319 * 2 ^ 59
def prefixEnd_3252319 : Nat := 4983230072969 + 3 ^ 40 * 3252319 * 2
def baseEnd_3252319 : Nat := 1670002888750166020655363

theorem tailTrace_3252319 : CollatzResearch.WordTrace tailWord_3252319 prefixEnd_3252319 1670002888750166020655363 := by
  unfold tailWord_3252319
  simp only [CollatzResearch.WordTrace]
  refine ⟨118621819104411189708528011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79081212736274126472352007 118621819104411189708528011)
  ·
    refine ⟨177932728656616784562792017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118621819104411189708528011 177932728656616784562792017)
    ·
      refine ⟨133449546492462588422094013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177932728656616784562792017 133449546492462588422094013)
      ·
        refine ⟨50043579934673470658285255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133449546492462588422094013 50043579934673470658285255)
        ·
          refine ⟨75065369902010205987427883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50043579934673470658285255 75065369902010205987427883)
          ·
            refine ⟨112598054853015308981141825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75065369902010205987427883 112598054853015308981141825)
            ·
              refine ⟨84448541139761481735856369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112598054853015308981141825 84448541139761481735856369)
              ·
                refine ⟨63336405854821111301892277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84448541139761481735856369 63336405854821111301892277)
                ·
                  refine ⟨5937788048889479184552401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63336405854821111301892277 5937788048889479184552401)
                  ·
                    refine ⟨4453341036667109388414301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5937788048889479184552401 4453341036667109388414301)
                    ·
                      refine ⟨1670002888750166020655363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4453341036667109388414301 1670002888750166020655363)
                      ·
                        rfl

theorem cell23_3252319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_3252319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252319 prefixEnd_3252319 := by exact prefixLift 3252319
  have htrace : WordTrace (prefixWord ++ tailWord_3252319) baseStart_3252319 baseEnd_3252319 := by
    simpa [prefixWord, tailWord_3252319, baseEnd_3252319] using wordTrace_append hprefix tailTrace_3252319
  have hstable : (prefixWord ++ tailWord_3252319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252319).length < 2 ^ (prefixWord ++ tailWord_3252319).sum := by decide
  have hdescent : baseEnd_3252319 < baseStart_3252319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252343 : List Nat := [1, 1, 3, 1, 1, 6, 3, 1, 2, 4]
def baseStart_3252343 : Nat := 118140960795 + 3252343 * 2 ^ 59
def prefixEnd_3252343 : Nat := 4983230072969 + 3 ^ 40 * 3252343 * 2
def baseEnd_3252343 : Nat := 556671737428624642251751

theorem tailTrace_3252343 : CollatzResearch.WordTrace tailWord_3252343 prefixEnd_3252343 556671737428624642251751 := by
  unfold tailWord_3252343
  simp only [CollatzResearch.WordTrace]
  refine ⟨118622694456324241807401683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79081796304216161204934455 118622694456324241807401683)
  ·
    refine ⟨177934041684486362711102525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118622694456324241807401683 177934041684486362711102525)
    ·
      refine ⟨66725265631682386016663447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177934041684486362711102525 66725265631682386016663447)
      ·
        refine ⟨100087898447523579024995171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66725265631682386016663447 100087898447523579024995171)
        ·
          refine ⟨150131847671285368537492757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100087898447523579024995171 150131847671285368537492757)
          ·
            refine ⟨7037430359591501650194973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 150131847671285368537492757 7037430359591501650194973)
            ·
              refine ⟨2639036384846813118823115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7037430359591501650194973 2639036384846813118823115)
              ·
                refine ⟨3958554577270219678234673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2639036384846813118823115 3958554577270219678234673)
                ·
                  refine ⟨2968915932952664758676005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3958554577270219678234673 2968915932952664758676005)
                  ·
                    refine ⟨556671737428624642251751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2968915932952664758676005 556671737428624642251751)
                    ·
                      rfl

theorem cell23_3252343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 2, 4].length) (baseStart_3252343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252343 prefixEnd_3252343 := by exact prefixLift 3252343
  have htrace : WordTrace (prefixWord ++ tailWord_3252343) baseStart_3252343 baseEnd_3252343 := by
    simpa [prefixWord, tailWord_3252343, baseEnd_3252343] using wordTrace_append hprefix tailTrace_3252343
  have hstable : (prefixWord ++ tailWord_3252343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252343).length < 2 ^ (prefixWord ++ tailWord_3252343).sum := by decide
  have hdescent : baseEnd_3252343 < baseStart_3252343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252383 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 4, 1, 3]
def baseStart_3252383 : Nat := 118140960795 + 3252383 * 2 ^ 59
def prefixEnd_3252383 : Nat := 4983230072969 + 3 ^ 40 * 3252383 * 2
def baseEnd_3252383 : Nat := 1670035751512053770255069

theorem tailTrace_3252383 : CollatzResearch.WordTrace tailWord_3252383 prefixEnd_3252383 1670035751512053770255069 := by
  unfold tailWord_3252383
  simp only [CollatzResearch.WordTrace]
  refine ⟨118624153376179328638857803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79082768917452885759238535 118624153376179328638857803)
  ·
    refine ⟨177936230064268992958286705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118624153376179328638857803 177936230064268992958286705)
    ·
      refine ⟨133452172548201744718715029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177936230064268992958286705 133452172548201744718715029)
      ·
        refine ⟨6255570588196956783689767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 133452172548201744718715029 6255570588196956783689767)
        ·
          refine ⟨9383355882295435175534651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6255570588196956783689767 9383355882295435175534651)
          ·
            refine ⟨14075033823443152763301977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9383355882295435175534651 14075033823443152763301977)
            ·
              refine ⟨10556275367582364572476483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14075033823443152763301977 10556275367582364572476483)
              ·
                refine ⟨15834413051373546858714725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10556275367582364572476483 15834413051373546858714725)
                ·
                  refine ⟨2968952447132540036009011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15834413051373546858714725 2968952447132540036009011)
                  ·
                    refine ⟨4453428670698810054013517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2968952447132540036009011 4453428670698810054013517)
                    ·
                      refine ⟨1670035751512053770255069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4453428670698810054013517 1670035751512053770255069)
                      ·
                        rfl

theorem cell23_3252383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_3252383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252383 prefixEnd_3252383 := by exact prefixLift 3252383
  have htrace : WordTrace (prefixWord ++ tailWord_3252383) baseStart_3252383 baseEnd_3252383 := by
    simpa [prefixWord, tailWord_3252383, baseEnd_3252383] using wordTrace_append hprefix tailTrace_3252383
  have hstable : (prefixWord ++ tailWord_3252383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252383).length < 2 ^ (prefixWord ++ tailWord_3252383).sum := by decide
  have hdescent : baseEnd_3252383 < baseStart_3252383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252389 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 2, 3, 4]
def baseStart_3252389 : Nat := 118140960795 + 3252389 * 2 ^ 59
def prefixEnd_3252389 : Nat := 4983230072969 + 3 ^ 40 * 3252389 * 2
def baseEnd_3252389 : Nat := 1670038832395980746780041

theorem tailTrace_3252389 : CollatzResearch.WordTrace tailWord_3252389 prefixEnd_3252389 1670038832395980746780041 := by
  unfold tailWord_3252389
  simp only [CollatzResearch.WordTrace]
  refine ⟨118624372214157591663576221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79082914809438394442384147 118624372214157591663576221)
  ·
    refine ⟨44484139580309096873841083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118624372214157591663576221 44484139580309096873841083)
    ·
      refine ⟨66726209370463645310761625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44484139580309096873841083 66726209370463645310761625)
      ·
        refine ⟨50044657027847733983071219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66726209370463645310761625 50044657027847733983071219)
        ·
          refine ⟨75066985541771600974606829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50044657027847733983071219 75066985541771600974606829)
          ·
            refine ⟨28150119578164350365477561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75066985541771600974606829 28150119578164350365477561)
            ·
              refine ⟨21112589683623262774108171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28150119578164350365477561 21112589683623262774108171)
              ·
                refine ⟨31668884525434894161162257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21112589683623262774108171 31668884525434894161162257)
                ·
                  refine ⟨23751663394076170620871693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31668884525434894161162257 23751663394076170620871693)
                  ·
                    refine ⟨8906873772778563982826885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23751663394076170620871693 8906873772778563982826885)
                    ·
                      refine ⟨1670038832395980746780041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8906873772778563982826885 1670038832395980746780041)
                      ·
                        rfl

theorem cell23_3252389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_3252389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252389 prefixEnd_3252389 := by exact prefixLift 3252389
  have htrace : WordTrace (prefixWord ++ tailWord_3252389) baseStart_3252389 baseEnd_3252389 := by
    simpa [prefixWord, tailWord_3252389, baseEnd_3252389] using wordTrace_append hprefix tailTrace_3252389
  have hstable : (prefixWord ++ tailWord_3252389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252389).length < 2 ^ (prefixWord ++ tailWord_3252389).sum := by decide
  have hdescent : baseEnd_3252389 < baseStart_3252389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252394 : List Nat := [3, 1, 5, 1, 3, 1, 2, 1, 2, 4]
def baseStart_3252394 : Nat := 118140960795 + 3252394 * 2 ^ 59
def prefixEnd_3252394 : Nat := 4983230072969 + 3 ^ 40 * 3252394 * 2
def baseEnd_3252394 : Nat := 556680466599751075739173

theorem tailTrace_3252394 : CollatzResearch.WordTrace tailWord_3252394 prefixEnd_3252394 556680466599751075739173 := by
  unfold tailWord_3252394
  simp only [CollatzResearch.WordTrace]
  refine ⟨29656138644784869379377059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79083036386092985011672157 29656138644784869379377059)
  ·
    refine ⟨44484207967177304069065589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29656138644784869379377059 44484207967177304069065589)
    ·
      refine ⟨4170394496922872256474899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44484207967177304069065589 4170394496922872256474899)
      ·
        refine ⟨6255591745384308384712349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4170394496922872256474899 6255591745384308384712349)
        ·
          refine ⟨2345846904519115644267131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6255591745384308384712349 2345846904519115644267131)
          ·
            refine ⟨3518770356778673466400697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2345846904519115644267131 3518770356778673466400697)
            ·
              refine ⟨2639077767584005099800523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3518770356778673466400697 2639077767584005099800523)
              ·
                refine ⟨3958616651376007649700785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2639077767584005099800523 3958616651376007649700785)
                ·
                  refine ⟨2968962488532005737275589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3958616651376007649700785 2968962488532005737275589)
                  ·
                    refine ⟨556680466599751075739173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2968962488532005737275589 556680466599751075739173)
                    ·
                      rfl

theorem cell23_3252394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_3252394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252394 prefixEnd_3252394 := by exact prefixLift 3252394
  have htrace : WordTrace (prefixWord ++ tailWord_3252394) baseStart_3252394 baseEnd_3252394 := by
    simpa [prefixWord, tailWord_3252394, baseEnd_3252394] using wordTrace_append hprefix tailTrace_3252394
  have hstable : (prefixWord ++ tailWord_3252394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252394).length < 2 ^ (prefixWord ++ tailWord_3252394).sum := by decide
  have hdescent : baseEnd_3252394 < baseStart_3252394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252409 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 4, 1, 5]
def baseStart_3252409 : Nat := 118140960795 + 3252409 * 2 ^ 59
def prefixEnd_3252409 : Nat := 4983230072969 + 3 ^ 40 * 3252409 * 2
def baseEnd_3252409 : Nat := 1670049102009070668529949

theorem tailTrace_3252409 : CollatzResearch.WordTrace tailWord_3252409 prefixEnd_3252409 1670049102009070668529949 := by
  unfold tailWord_3252409
  simp only [CollatzResearch.WordTrace]
  refine ⟨118625101674085135079304281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79083401116056756719536187 118625101674085135079304281)
  ·
    refine ⟨88968826255563851309478211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118625101674085135079304281 88968826255563851309478211)
    ·
      refine ⟨133453239383345776964217317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88968826255563851309478211 133453239383345776964217317)
      ·
        refine ⟨25022482384377333180790747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133453239383345776964217317 25022482384377333180790747)
        ·
          refine ⟨37533723576565999771186121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25022482384377333180790747 37533723576565999771186121)
          ·
            refine ⟨28150292682424499828389591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37533723576565999771186121 28150292682424499828389591)
            ·
              refine ⟨42225439023636749742584387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28150292682424499828389591 42225439023636749742584387)
              ·
                refine ⟨63338158535455124613876581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42225439023636749742584387 63338158535455124613876581)
                ·
                  refine ⟨11875904725397835865101859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63338158535455124613876581 11875904725397835865101859)
                  ·
                    refine ⟨17813857088096753797652789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11875904725397835865101859 17813857088096753797652789)
                    ·
                      refine ⟨1670049102009070668529949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17813857088096753797652789 1670049102009070668529949)
                      ·
                        rfl

theorem cell23_3252409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_3252409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252409 prefixEnd_3252409 := by exact prefixLift 3252409
  have htrace : WordTrace (prefixWord ++ tailWord_3252409) baseStart_3252409 baseEnd_3252409 := by
    simpa [prefixWord, tailWord_3252409, baseEnd_3252409] using wordTrace_append hprefix tailTrace_3252409
  have hstable : (prefixWord ++ tailWord_3252409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252409).length < 2 ^ (prefixWord ++ tailWord_3252409).sum := by decide
  have hdescent : baseEnd_3252409 < baseStart_3252409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252440 : List Nat := [2, 1, 2, 2, 4, 1, 1, 4, 2, 2, 2]
def baseStart_3252440 : Nat := 118140960795 + 3252440 * 2 ^ 59
def prefixEnd_3252440 : Nat := 4983230072969 + 3 ^ 40 * 3252440 * 2
def baseEnd_3252440 : Nat := 1670065019909360047242307

theorem tailTrace_3252440 : CollatzResearch.WordTrace tailWord_3252440 prefixEnd_3252440 1670065019909360047242307 := by
  unfold tailWord_3252440
  simp only [CollatzResearch.WordTrace]
  refine ⟨59313116168486413686841387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79084154891315218249121849 59313116168486413686841387)
  ·
    refine ⟨88969674252729620530262081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59313116168486413686841387 88969674252729620530262081)
    ·
      refine ⟨66727255689547215397696561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88969674252729620530262081 66727255689547215397696561)
      ·
        refine ⟨50045441767160411548272421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66727255689547215397696561 50045441767160411548272421)
        ·
          refine ⟨9383520331342577165301079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50045441767160411548272421 9383520331342577165301079)
          ·
            refine ⟨14075280497013865747951619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9383520331342577165301079 14075280497013865747951619)
            ·
              refine ⟨21112920745520798621927429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14075280497013865747951619 21112920745520798621927429)
              ·
                refine ⟨3958672639785149741611393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21112920745520798621927429 3958672639785149741611393)
                ·
                  refine ⟨2969004479838862306208545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3958672639785149741611393 2969004479838862306208545)
                  ·
                    refine ⟨2226753359879146729656409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2969004479838862306208545 2226753359879146729656409)
                    ·
                      refine ⟨1670065019909360047242307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2226753359879146729656409 1670065019909360047242307)
                      ·
                        rfl

theorem cell23_3252440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 2, 2, 2].length) (baseStart_3252440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252440 prefixEnd_3252440 := by exact prefixLift 3252440
  have htrace : WordTrace (prefixWord ++ tailWord_3252440) baseStart_3252440 baseEnd_3252440 := by
    simpa [prefixWord, tailWord_3252440, baseEnd_3252440] using wordTrace_append hprefix tailTrace_3252440
  have hstable : (prefixWord ++ tailWord_3252440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252440).length < 2 ^ (prefixWord ++ tailWord_3252440).sum := by decide
  have hdescent : baseEnd_3252440 < baseStart_3252440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252456 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 1, 5, 3]
def baseStart_3252456 : Nat := 118140960795 + 3252456 * 2 ^ 59
def prefixEnd_3252456 : Nat := 4983230072969 + 3 ^ 40 * 3252456 * 2
def baseEnd_3252456 : Nat := 1670073235599831984642233

theorem tailTrace_3252456 : CollatzResearch.WordTrace tailWord_3252456 prefixEnd_3252456 1670073235599831984642233 := by
  unfold tailWord_3252456
  simp only [CollatzResearch.WordTrace]
  refine ⟨59313407952457431053132611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79084543936609908070843481 59313407952457431053132611)
  ·
    refine ⟨88970111928686146579698917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59313407952457431053132611 88970111928686146579698917)
    ·
      refine ⟨16681895986628652483693547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88970111928686146579698917 16681895986628652483693547)
      ·
        refine ⟨25022843979942978725540321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16681895986628652483693547 25022843979942978725540321)
        ·
          refine ⟨18767132984957234044155241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25022843979942978725540321 18767132984957234044155241)
          ·
            refine ⟨14075349738717925533116431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18767132984957234044155241 14075349738717925533116431)
            ·
              refine ⟨21113024608076888299674647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14075349738717925533116431 21113024608076888299674647)
              ·
                refine ⟨31669536912115332449511971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21113024608076888299674647 31669536912115332449511971)
                ·
                  refine ⟨47504305368172998674267957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31669536912115332449511971 47504305368172998674267957)
                  ·
                    refine ⟨4453528628266218625712621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47504305368172998674267957 4453528628266218625712621)
                    ·
                      refine ⟨1670073235599831984642233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4453528628266218625712621 1670073235599831984642233)
                      ·
                        rfl

theorem cell23_3252456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_3252456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252456 prefixEnd_3252456 := by exact prefixLift 3252456
  have htrace : WordTrace (prefixWord ++ tailWord_3252456) baseStart_3252456 baseEnd_3252456 := by
    simpa [prefixWord, tailWord_3252456, baseEnd_3252456] using wordTrace_append hprefix tailTrace_3252456
  have hstable : (prefixWord ++ tailWord_3252456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252456).length < 2 ^ (prefixWord ++ tailWord_3252456).sum := by decide
  have hdescent : baseEnd_3252456 < baseStart_3252456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252459 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 1, 7]
def baseStart_3252459 : Nat := 118140960795 + 3252459 * 2 ^ 59
def prefixEnd_3252459 : Nat := 4983230072969 + 3 ^ 40 * 3252459 * 2
def baseEnd_3252459 : Nat := 556691592013931824301573

theorem tailTrace_3252459 : CollatzResearch.WordTrace tailWord_3252459 prefixEnd_3252459 556691592013931824301573 := by
  unfold tailWord_3252459
  simp only [CollatzResearch.WordTrace]
  refine ⟨118626925323903993618624431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79084616882602662412416287 118626925323903993618624431)
  ·
    refine ⟨177940387985855990427936647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118626925323903993618624431 177940387985855990427936647)
    ·
      refine ⟨266910581978783985641904971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177940387985855990427936647 266910581978783985641904971)
      ·
        refine ⟨400365872968175978462857457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266910581978783985641904971 400365872968175978462857457)
        ·
          refine ⟨300274404726131983847143093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400365872968175978462857457 300274404726131983847143093)
          ·
            refine ⟨28150725443074873485669665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 300274404726131983847143093 28150725443074873485669665)
            ·
              refine ⟨21113044082306155114252249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28150725443074873485669665 21113044082306155114252249)
              ·
                refine ⟨15834783061729616335689187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21113044082306155114252249 15834783061729616335689187)
                ·
                  refine ⟨23752174592594424503533781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15834783061729616335689187 23752174592594424503533781)
                  ·
                    refine ⟨556691592013931824301573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23752174592594424503533781 556691592013931824301573)
                    ·
                      rfl

theorem cell23_3252459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 7].length) (baseStart_3252459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252459 prefixEnd_3252459 := by exact prefixLift 3252459
  have htrace : WordTrace (prefixWord ++ tailWord_3252459) baseStart_3252459 baseEnd_3252459 := by
    simpa [prefixWord, tailWord_3252459, baseEnd_3252459] using wordTrace_append hprefix tailTrace_3252459
  have hstable : (prefixWord ++ tailWord_3252459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252459).length < 2 ^ (prefixWord ++ tailWord_3252459).sum := by decide
  have hdescent : baseEnd_3252459 < baseStart_3252459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252476 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 1, 7]
def baseStart_3252476 : Nat := 118140960795 + 3252476 * 2 ^ 59
def prefixEnd_3252476 : Nat := 4983230072969 + 3 ^ 40 * 3252476 * 2
def baseEnd_3252476 : Nat := 556694501737640635464047

theorem tailTrace_3252476 : CollatzResearch.WordTrace tailWord_3252476 prefixEnd_3252476 556694501737640635464047 := by
  unfold tailWord_3252476
  simp only [CollatzResearch.WordTrace]
  refine ⟨59313772682421202760996641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79085030243228270347995521 59313772682421202760996641)
  ·
    refine ⟨44485329511815902070747481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59313772682421202760996641 44485329511815902070747481)
    ·
      refine ⟨33363997133861926553060611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44485329511815902070747481 33363997133861926553060611)
      ·
        refine ⟨50045995700792889829590917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33363997133861926553060611 50045995700792889829590917)
        ·
          refine ⟨9383624193898666843048297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50045995700792889829590917 9383624193898666843048297)
          ·
            refine ⟨7037718145424000132286223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9383624193898666843048297 7037718145424000132286223)
            ·
              refine ⟨10556577218136000198429335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7037718145424000132286223 10556577218136000198429335)
              ·
                refine ⟨15834865827204000297644003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10556577218136000198429335 15834865827204000297644003)
                ·
                  refine ⟨23752298740806000446466005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15834865827204000297644003 23752298740806000446466005)
                  ·
                    refine ⟨556694501737640635464047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23752298740806000446466005 556694501737640635464047)
                    ·
                      rfl

theorem cell23_3252476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_3252476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252476 prefixEnd_3252476 := by exact prefixLift 3252476
  have htrace : WordTrace (prefixWord ++ tailWord_3252476) baseStart_3252476 baseEnd_3252476 := by
    simpa [prefixWord, tailWord_3252476, baseEnd_3252476] using wordTrace_append hprefix tailTrace_3252476
  have hstable : (prefixWord ++ tailWord_3252476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252476).length < 2 ^ (prefixWord ++ tailWord_3252476).sum := by decide
  have hdescent : baseEnd_3252476 < baseStart_3252476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252496 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 2, 10, 2]
def baseStart_3252496 : Nat := 118140960795 + 3252496 * 2 ^ 59
def prefixEnd_3252496 : Nat := 4983230072969 + 3 ^ 40 * 3252496 * 2
def baseEnd_3252496 : Nat := 1670093774826011828142049

theorem tailTrace_3252496 : CollatzResearch.WordTrace tailWord_3252496 prefixEnd_3252496 1670093774826011828142049 := by
  unfold tailWord_3252496
  simp only [CollatzResearch.WordTrace]
  refine ⟨59314137412384974468860671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79085516549846632625147561 59314137412384974468860671)
  ·
    refine ⟨88971206118577461703291007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59314137412384974468860671 88971206118577461703291007)
    ·
      refine ⟨133456809177866192554936511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88971206118577461703291007 133456809177866192554936511)
      ·
        refine ⟨200185213766799288832404767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133456809177866192554936511 200185213766799288832404767)
        ·
          refine ⟨300277820650198933248607151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200185213766799288832404767 300277820650198933248607151)
          ·
            refine ⟨450416730975298399872910727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300277820650198933248607151 450416730975298399872910727)
            ·
              refine ⟨675625096462947599809366091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450416730975298399872910727 675625096462947599809366091)
              ·
                refine ⟨1013437644694421399714049137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675625096462947599809366091 1013437644694421399714049137)
                ·
                  refine ⟨760078233520816049785536853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1013437644694421399714049137 760078233520816049785536853)
                  ·
                    refine ⟨2226791699768015770856065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 760078233520816049785536853 2226791699768015770856065)
                    ·
                      refine ⟨1670093774826011828142049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2226791699768015770856065 1670093774826011828142049)
                      ·
                        rfl

theorem cell23_3252496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 10, 2].length) (baseStart_3252496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252496 prefixEnd_3252496 := by exact prefixLift 3252496
  have htrace : WordTrace (prefixWord ++ tailWord_3252496) baseStart_3252496 baseEnd_3252496 := by
    simpa [prefixWord, tailWord_3252496, baseEnd_3252496] using wordTrace_append hprefix tailTrace_3252496
  have hstable : (prefixWord ++ tailWord_3252496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252496).length < 2 ^ (prefixWord ++ tailWord_3252496).sum := by decide
  have hdescent : baseEnd_3252496 < baseStart_3252496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252499 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 5]
def baseStart_3252499 : Nat := 118140960795 + 3252499 * 2 ^ 59
def prefixEnd_3252499 : Nat := 4983230072969 + 3 ^ 40 * 3252499 * 2
def baseEnd_3252499 : Nat := 1670095315267975316404535

theorem tailTrace_3252499 : CollatzResearch.WordTrace tailWord_3252499 prefixEnd_3252499 1670095315267975316404535 := by
  unfold tailWord_3252499
  simp only [CollatzResearch.WordTrace]
  refine ⟨118628384243759080450080551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79085589495839386966720367 118628384243759080450080551)
  ·
    refine ⟨177942576365638620675120827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118628384243759080450080551 177942576365638620675120827)
    ·
      refine ⟨266913864548457931012681241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177942576365638620675120827 266913864548457931012681241)
      ·
        refine ⟨200185398411343448259510931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266913864548457931012681241 200185398411343448259510931)
        ·
          refine ⟨300278097617015172389266397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200185398411343448259510931 300278097617015172389266397)
          ·
            refine ⟨112604286606380689645974899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300278097617015172389266397 112604286606380689645974899)
            ·
              refine ⟨168906429909571034468962349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112604286606380689645974899 168906429909571034468962349)
              ·
                refine ⟨63339911216089137925860881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168906429909571034468962349 63339911216089137925860881)
                ·
                  refine ⟨47504933412066853444395661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63339911216089137925860881 47504933412066853444395661)
                  ·
                    refine ⟨17814350029525070041648373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47504933412066853444395661 17814350029525070041648373)
                    ·
                      refine ⟨1670095315267975316404535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17814350029525070041648373 1670095315267975316404535)
                      ·
                        rfl

theorem cell23_3252499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_3252499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252499 prefixEnd_3252499 := by exact prefixLift 3252499
  have htrace : WordTrace (prefixWord ++ tailWord_3252499) baseStart_3252499 baseEnd_3252499 := by
    simpa [prefixWord, tailWord_3252499, baseEnd_3252499] using wordTrace_append hprefix tailTrace_3252499
  have hstable : (prefixWord ++ tailWord_3252499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252499).length < 2 ^ (prefixWord ++ tailWord_3252499).sum := by decide
  have hdescent : baseEnd_3252499 < baseStart_3252499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252513 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 2, 4, 2]
def baseStart_3252513 : Nat := 118140960795 + 3252513 * 2 ^ 59
def prefixEnd_3252513 : Nat := 4983230072969 + 3 ^ 40 * 3252513 * 2
def baseEnd_3252513 : Nat := 1670102503997138261629471

theorem tailTrace_3252513 : CollatzResearch.WordTrace tailWord_3252513 prefixEnd_3252513 1670102503997138261629471 := by
  unfold tailWord_3252513
  simp only [CollatzResearch.WordTrace]
  refine ⟨118628894865708360841090193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79085929910472240560726795 118628894865708360841090193)
  ·
    refine ⟨88971671149281270630817645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118628894865708360841090193 88971671149281270630817645)
    ·
      refine ⟨33364376680980476486556617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88971671149281270630817645 33364376680980476486556617)
      ·
        refine ⟨25023282510735357364917463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33364376680980476486556617 25023282510735357364917463)
        ·
          refine ⟨37534923766103036047376195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25023282510735357364917463 37534923766103036047376195)
          ·
            refine ⟨56302385649154554071064293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37534923766103036047376195 56302385649154554071064293)
            ·
              refine ⟨10556697309216478888324555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56302385649154554071064293 10556697309216478888324555)
              ·
                refine ⟨15835045963824718332486833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10556697309216478888324555 15835045963824718332486833)
                ·
                  refine ⟨11876284472868538749365125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15835045963824718332486833 11876284472868538749365125)
                  ·
                    refine ⟨2226803338662851015505961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11876284472868538749365125 2226803338662851015505961)
                    ·
                      refine ⟨1670102503997138261629471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2226803338662851015505961 1670102503997138261629471)
                      ·
                        rfl

theorem cell23_3252513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_3252513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252513 prefixEnd_3252513 := by exact prefixLift 3252513
  have htrace : WordTrace (prefixWord ++ tailWord_3252513) baseStart_3252513 baseEnd_3252513 := by
    simpa [prefixWord, tailWord_3252513, baseEnd_3252513] using wordTrace_append hprefix tailTrace_3252513
  have hstable : (prefixWord ++ tailWord_3252513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252513).length < 2 ^ (prefixWord ++ tailWord_3252513).sum := by decide
  have hdescent : baseEnd_3252513 < baseStart_3252513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252533 : List Nat := [1, 3, 3, 1, 2, 1, 2, 3, 2, 2, 3]
def baseStart_3252533 : Nat := 118140960795 + 3252533 * 2 ^ 59
def prefixEnd_3252533 : Nat := 4983230072969 + 3 ^ 40 * 3252533 * 2
def baseEnd_3252533 : Nat := 1670112773610228183379379

theorem tailTrace_3252533 : CollatzResearch.WordTrace tailWord_3252533 prefixEnd_3252533 1670112773610228183379379 := by
  unfold tailWord_3252533
  simp only [CollatzResearch.WordTrace]
  refine ⟨118629624325635904256818253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79086416217090602837878835 118629624325635904256818253)
  ·
    refine ⟨44486109122113464096306845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118629624325635904256818253 44486109122113464096306845)
    ·
      refine ⟨16682290920792549036115067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44486109122113464096306845 16682290920792549036115067)
      ·
        refine ⟨25023436381188823554172601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16682290920792549036115067 25023436381188823554172601)
        ·
          refine ⟨18767577285891617665629451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25023436381188823554172601 18767577285891617665629451)
          ·
            refine ⟨28151365928837426498444177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18767577285891617665629451 28151365928837426498444177)
            ·
              refine ⟨21113524446628069873833133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28151365928837426498444177 21113524446628069873833133)
              ·
                refine ⟨7917571667485526202687425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21113524446628069873833133 7917571667485526202687425)
                ·
                  refine ⟨5938178750614144652015569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7917571667485526202687425 5938178750614144652015569)
                  ·
                    refine ⟨4453634062960608489011677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5938178750614144652015569 4453634062960608489011677)
                    ·
                      refine ⟨1670112773610228183379379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4453634062960608489011677 1670112773610228183379379)
                      ·
                        rfl

theorem cell23_3252533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_3252533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252533 prefixEnd_3252533 := by exact prefixLift 3252533
  have htrace : WordTrace (prefixWord ++ tailWord_3252533) baseStart_3252533 baseEnd_3252533 := by
    simpa [prefixWord, tailWord_3252533, baseEnd_3252533] using wordTrace_append hprefix tailTrace_3252533
  have hstable : (prefixWord ++ tailWord_3252533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252533).length < 2 ^ (prefixWord ++ tailWord_3252533).sum := by decide
  have hdescent : baseEnd_3252533 < baseStart_3252533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252539 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 6]
def baseStart_3252539 : Nat := 118140960795 + 3252539 * 2 ^ 59
def prefixEnd_3252539 : Nat := 4983230072969 + 3 ^ 40 * 3252539 * 2
def baseEnd_3252539 : Nat := 1670115854494155159904351

theorem tailTrace_3252539 : CollatzResearch.WordTrace tailWord_3252539 prefixEnd_3252539 1670115854494155159904351 := by
  unfold tailWord_3252539
  simp only [CollatzResearch.WordTrace]
  refine ⟨118629843163614167281536671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79086562109076111521024447 118629843163614167281536671)
  ·
    refine ⟨177944764745421250922305007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118629843163614167281536671 177944764745421250922305007)
    ·
      refine ⟨266917147118131876383457511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177944764745421250922305007 266917147118131876383457511)
      ·
        refine ⟨400375720677197814575186267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266917147118131876383457511 400375720677197814575186267)
        ·
          refine ⟨600563581015796721862779401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400375720677197814575186267 600563581015796721862779401)
          ·
            refine ⟨450422685761847541397084551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 600563581015796721862779401 450422685761847541397084551)
            ·
              refine ⟨675634028642771312095626827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450422685761847541397084551 675634028642771312095626827)
              ·
                refine ⟨1013451042964156968143440241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675634028642771312095626827 1013451042964156968143440241)
                ·
                  refine ⟨760088282223117726107580181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1013451042964156968143440241 760088282223117726107580181)
                  ·
                    refine ⟨35629138229208643411292821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 760088282223117726107580181 35629138229208643411292821)
                    ·
                      refine ⟨1670115854494155159904351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35629138229208643411292821 1670115854494155159904351)
                      ·
                        rfl

theorem cell23_3252539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 6].length) (baseStart_3252539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252539 prefixEnd_3252539 := by exact prefixLift 3252539
  have htrace : WordTrace (prefixWord ++ tailWord_3252539) baseStart_3252539 baseEnd_3252539 := by
    simpa [prefixWord, tailWord_3252539, baseEnd_3252539] using wordTrace_append hprefix tailTrace_3252539
  have hstable : (prefixWord ++ tailWord_3252539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252539).length < 2 ^ (prefixWord ++ tailWord_3252539).sum := by decide
  have hdescent : baseEnd_3252539 < baseStart_3252539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252563 : List Nat := [1, 1, 1, 2, 1, 1, 4, 5, 3, 1, 3]
def baseStart_3252563 : Nat := 118140960795 + 3252563 * 2 ^ 59
def prefixEnd_3252563 : Nat := 4983230072969 + 3 ^ 40 * 3252563 * 2
def baseEnd_3252563 : Nat := 1670128178029863066004241

theorem tailTrace_3252563 : CollatzResearch.WordTrace tailWord_3252563 prefixEnd_3252563 1670128178029863066004241 := by
  unfold tailWord_3252563
  simp only [CollatzResearch.WordTrace]
  refine ⟨118630718515527219380410343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79087145677018146253606895 118630718515527219380410343)
  ·
    refine ⟨177946077773290829070615515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118630718515527219380410343 177946077773290829070615515)
    ·
      refine ⟨266919116659936243605923273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177946077773290829070615515 266919116659936243605923273)
      ·
        refine ⟨200189337494952182704442455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266919116659936243605923273 200189337494952182704442455)
        ·
          refine ⟨300284006242428274056663683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200189337494952182704442455 300284006242428274056663683)
          ·
            refine ⟨450426009363642411084995525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300284006242428274056663683 450426009363642411084995525)
            ·
              refine ⟨84454876755682952078436661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 450426009363642411084995525 84454876755682952078436661)
              ·
                refine ⟨7917644695845276757353437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84454876755682952078436661 7917644695845276757353437)
                ·
                  refine ⟨2969116760941978784007539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7917644695845276757353437 2969116760941978784007539)
                  ·
                    refine ⟨4453675141412968176011309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2969116760941978784007539 4453675141412968176011309)
                    ·
                      refine ⟨1670128178029863066004241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4453675141412968176011309 1670128178029863066004241)
                      ·
                        rfl

theorem cell23_3252563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 1, 3].length) (baseStart_3252563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252563 prefixEnd_3252563 := by exact prefixLift 3252563
  have htrace : WordTrace (prefixWord ++ tailWord_3252563) baseStart_3252563 baseEnd_3252563 := by
    simpa [prefixWord, tailWord_3252563, baseEnd_3252563] using wordTrace_append hprefix tailTrace_3252563
  have hstable : (prefixWord ++ tailWord_3252563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252563).length < 2 ^ (prefixWord ++ tailWord_3252563).sum := by decide
  have hdescent : baseEnd_3252563 < baseStart_3252563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252583 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 3, 5]
def baseStart_3252583 : Nat := 118140960795 + 3252583 * 2 ^ 59
def prefixEnd_3252583 : Nat := 4983230072969 + 3 ^ 40 * 3252583 * 2
def baseEnd_3252583 : Nat := 556712815880984329251383

theorem tailTrace_3252583 : CollatzResearch.WordTrace tailWord_3252583 prefixEnd_3252583 556712815880984329251383 := by
  unfold tailWord_3252583
  simp only [CollatzResearch.WordTrace]
  refine ⟨118631447975454762796138403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79087631983636508530758935 118631447975454762796138403)
  ·
    refine ⟨177947171963182144194207605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118631447975454762796138403 177947171963182144194207605)
    ·
      refine ⟨16682547371548326018206963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177947171963182144194207605 16682547371548326018206963)
      ·
        refine ⟨25023821057322489027310445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16682547371548326018206963 25023821057322489027310445)
        ·
          refine ⟨9383932896495933385241417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25023821057322489027310445 9383932896495933385241417)
          ·
            refine ⟨7037949672371950038931063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9383932896495933385241417 7037949672371950038931063)
            ·
              refine ⟨10556924508557925058396595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7037949672371950038931063 10556924508557925058396595)
              ·
                refine ⟨15835386762836887587594893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10556924508557925058396595 15835386762836887587594893)
                ·
                  refine ⟨5938270036063832845348085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15835386762836887587594893 5938270036063832845348085)
                  ·
                    refine ⟨556712815880984329251383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5938270036063832845348085 556712815880984329251383)
                    ·
                      rfl

theorem cell23_3252583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_3252583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252583 prefixEnd_3252583 := by exact prefixLift 3252583
  have htrace : WordTrace (prefixWord ++ tailWord_3252583) baseStart_3252583 baseEnd_3252583 := by
    simpa [prefixWord, tailWord_3252583, baseEnd_3252583] using wordTrace_append hprefix tailTrace_3252583
  have hstable : (prefixWord ++ tailWord_3252583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252583).length < 2 ^ (prefixWord ++ tailWord_3252583).sum := by decide
  have hdescent : baseEnd_3252583 < baseStart_3252583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252633 : List Nat := [1, 2, 1, 2, 1, 4, 4, 1, 1, 2, 4]
def baseStart_3252633 : Nat := 118140960795 + 3252633 * 2 ^ 59
def prefixEnd_3252633 : Nat := 4983230072969 + 3 ^ 40 * 3252633 * 2
def baseEnd_3252633 : Nat := 1670164121675677792128919

theorem tailTrace_3252633 : CollatzResearch.WordTrace tailWord_3252633 prefixEnd_3252633 1670164121675677792128919 := by
  unfold tailWord_3252633
  simp only [CollatzResearch.WordTrace]
  refine ⟨118633271625273621335458553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79088847750182414223639035 118633271625273621335458553)
  ·
    refine ⟨88974953718955216001593915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118633271625273621335458553 88974953718955216001593915)
    ·
      refine ⟨133462430578432824002390873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88974953718955216001593915 133462430578432824002390873)
      ·
        refine ⟨100096822933824618001793155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133462430578432824002390873 100096822933824618001793155)
        ·
          refine ⟨150145234400736927002689733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100096822933824618001793155 150145234400736927002689733)
          ·
            refine ⟨28152231450138173813004325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150145234400736927002689733 28152231450138173813004325)
            ·
              refine ⟨5278543396900907589938311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28152231450138173813004325 5278543396900907589938311)
              ·
                refine ⟨7917815095351361384907467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5278543396900907589938311 7917815095351361384907467)
                ·
                  refine ⟨11876722643027042077361201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7917815095351361384907467 11876722643027042077361201)
                  ·
                    refine ⟨8907541982270281558020901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11876722643027042077361201 8907541982270281558020901)
                    ·
                      refine ⟨1670164121675677792128919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8907541982270281558020901 1670164121675677792128919)
                      ·
                        rfl

theorem cell23_3252633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 2, 4].length) (baseStart_3252633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252633 prefixEnd_3252633 := by exact prefixLift 3252633
  have htrace : WordTrace (prefixWord ++ tailWord_3252633) baseStart_3252633 baseEnd_3252633 := by
    simpa [prefixWord, tailWord_3252633, baseEnd_3252633] using wordTrace_append hprefix tailTrace_3252633
  have hstable : (prefixWord ++ tailWord_3252633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252633).length < 2 ^ (prefixWord ++ tailWord_3252633).sum := by decide
  have hdescent : baseEnd_3252633 < baseStart_3252633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252641 : List Nat := [1, 2, 3, 5, 2, 1, 1, 1, 2, 3, 2]
def baseStart_3252641 : Nat := 118140960795 + 3252641 * 2 ^ 59
def prefixEnd_3252641 : Nat := 4983230072969 + 3 ^ 40 * 3252641 * 2
def baseEnd_3252641 : Nat := 1670168229520913760828883

theorem tailTrace_3252641 : CollatzResearch.WordTrace tailWord_3252641 prefixEnd_3252641 1670168229520913760828883 := by
  unfold tailWord_3252641
  simp only [CollatzResearch.WordTrace]
  refine ⟨118633563409244638701749777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79089042272829759134499851 118633563409244638701749777)
  ·
    refine ⟨88975172556933479026312333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118633563409244638701749777 88975172556933479026312333)
    ·
      refine ⟨33365689708850054634867125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88975172556933479026312333 33365689708850054634867125)
      ·
        refine ⟨3128033410204692622018793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33365689708850054634867125 3128033410204692622018793)
        ·
          refine ⟨2346025057653519466514095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3128033410204692622018793 2346025057653519466514095)
          ·
            refine ⟨3519037586480279199771143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2346025057653519466514095 3519037586480279199771143)
            ·
              refine ⟨5278556379720418799656715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3519037586480279199771143 5278556379720418799656715)
              ·
                refine ⟨7917834569580628199485073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5278556379720418799656715 7917834569580628199485073)
                ·
                  refine ⟨5938375927185471149613805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7917834569580628199485073 5938375927185471149613805)
                  ·
                    refine ⟨2226890972694551681105177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5938375927185471149613805 2226890972694551681105177)
                    ·
                      refine ⟨1670168229520913760828883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2226890972694551681105177 1670168229520913760828883)
                      ·
                        rfl

theorem cell23_3252641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_3252641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252641 prefixEnd_3252641 := by exact prefixLift 3252641
  have htrace : WordTrace (prefixWord ++ tailWord_3252641) baseStart_3252641 baseEnd_3252641 := by
    simpa [prefixWord, tailWord_3252641, baseEnd_3252641] using wordTrace_append hprefix tailTrace_3252641
  have hstable : (prefixWord ++ tailWord_3252641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252641).length < 2 ^ (prefixWord ++ tailWord_3252641).sum := by decide
  have hdescent : baseEnd_3252641 < baseStart_3252641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252643 : List Nat := [1, 1, 1, 4, 1, 5, 3, 7]
def baseStart_3252643 : Nat := 118140960795 + 3252643 * 2 ^ 59
def prefixEnd_3252643 : Nat := 4983230072969 + 3 ^ 40 * 3252643 * 2
def baseEnd_3252643 : Nat := 61858120610452694555699

theorem tailTrace_3252643 : CollatzResearch.WordTrace tailWord_3252643 prefixEnd_3252643 61858120610452694555699 := by
  unfold tailWord_3252643
  simp only [CollatzResearch.WordTrace]
  refine ⟨118633636355237393043322583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79089090903491595362215055 118633636355237393043322583)
  ·
    refine ⟨177950454532856089564983875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118633636355237393043322583 177950454532856089564983875)
    ·
      refine ⟨266925681799284134347475813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177950454532856089564983875 266925681799284134347475813)
      ·
        refine ⟨50048565337365775190151715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 266925681799284134347475813 50048565337365775190151715)
        ·
          refine ⟨75072848006048662785227573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50048565337365775190151715 75072848006048662785227573)
          ·
            refine ⟨7038079500567062136115085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75072848006048662785227573 7038079500567062136115085)
            ·
              refine ⟨2639279812712648301043157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7038079500567062136115085 2639279812712648301043157)
              ·
                refine ⟨61858120610452694555699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2639279812712648301043157 61858120610452694555699)
                ·
                  rfl

theorem cell23_3252643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 7].length) (baseStart_3252643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252643 prefixEnd_3252643 := by exact prefixLift 3252643
  have htrace : WordTrace (prefixWord ++ tailWord_3252643) baseStart_3252643 baseEnd_3252643 := by
    simpa [prefixWord, tailWord_3252643, baseEnd_3252643] using wordTrace_append hprefix tailTrace_3252643
  have hstable : (prefixWord ++ tailWord_3252643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252643).length < 2 ^ (prefixWord ++ tailWord_3252643).sum := by decide
  have hdescent : baseEnd_3252643 < baseStart_3252643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252657 : List Nat := [1, 2, 2, 4, 1, 2, 4, 1, 1, 2, 3]
def baseStart_3252657 : Nat := 118140960795 + 3252657 * 2 ^ 59
def prefixEnd_3252657 : Nat := 4983230072969 + 3 ^ 40 * 3252657 * 2
def baseEnd_3252657 : Nat := 1670176445211385698228809

theorem tailTrace_3252657 : CollatzResearch.WordTrace tailWord_3252657 prefixEnd_3252657 1670176445211385698228809 := by
  unfold tailWord_3252657
  simp only [CollatzResearch.WordTrace]
  refine ⟨118634146977186673434332225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79089431318124448956221483 118634146977186673434332225)
  ·
    refine ⟨88975610232890005075749169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118634146977186673434332225 88975610232890005075749169)
    ·
      refine ⟨66731707674667503806811877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88975610232890005075749169 66731707674667503806811877)
      ·
        refine ⟨12512195189000156963777227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66731707674667503806811877 12512195189000156963777227)
        ·
          refine ⟨18768292783500235445665841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12512195189000156963777227 18768292783500235445665841)
          ·
            refine ⟨14076219587625176584249381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18768292783500235445665841 14076219587625176584249381)
            ·
              refine ⟨2639291172679720609546759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14076219587625176584249381 2639291172679720609546759)
              ·
                refine ⟨3958936759019580914320139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2639291172679720609546759 3958936759019580914320139)
                ·
                  refine ⟨5938405138529371371480209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3958936759019580914320139 5938405138529371371480209)
                  ·
                    refine ⟨4453803853897028528610157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5938405138529371371480209 4453803853897028528610157)
                    ·
                      refine ⟨1670176445211385698228809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4453803853897028528610157 1670176445211385698228809)
                      ·
                        rfl

theorem cell23_3252657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_3252657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252657 prefixEnd_3252657 := by exact prefixLift 3252657
  have htrace : WordTrace (prefixWord ++ tailWord_3252657) baseStart_3252657 baseEnd_3252657 := by
    simpa [prefixWord, tailWord_3252657, baseEnd_3252657] using wordTrace_append hprefix tailTrace_3252657
  have hstable : (prefixWord ++ tailWord_3252657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252657).length < 2 ^ (prefixWord ++ tailWord_3252657).sum := by decide
  have hdescent : baseEnd_3252657 < baseStart_3252657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252697 : List Nat := [1, 2, 1, 2, 4, 1, 4, 2, 1, 3, 2]
def baseStart_3252697 : Nat := 118140960795 + 3252697 * 2 ^ 59
def prefixEnd_3252697 : Nat := 4983230072969 + 3 ^ 40 * 3252697 * 2
def baseEnd_3252697 : Nat := 1670196984437565541728625

theorem tailTrace_3252697 : CollatzResearch.WordTrace tailWord_3252697 prefixEnd_3252697 1670196984437565541728625 := by
  unfold tailWord_3252697
  simp only [CollatzResearch.WordTrace]
  refine ⟨118635605897041760265788345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79090403931361173510525563 118635605897041760265788345)
  ·
    refine ⟨88976704422781320199341259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118635605897041760265788345 88976704422781320199341259)
    ·
      refine ⟨133465056634171980299011889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88976704422781320199341259 133465056634171980299011889)
      ·
        refine ⟨100098792475628985224258917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133465056634171980299011889 100098792475628985224258917)
        ·
          refine ⟨18768523589180434729548547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100098792475628985224258917 18768523589180434729548547)
          ·
            refine ⟨28152785383770652094322821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18768523589180434729548547 28152785383770652094322821)
            ·
              refine ⟨5278647259456997267685529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28152785383770652094322821 5278647259456997267685529)
              ·
                refine ⟨3958985444592747950764147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5278647259456997267685529 3958985444592747950764147)
                ·
                  refine ⟨5938478166889121926146221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3958985444592747950764147 5938478166889121926146221)
                  ·
                    refine ⟨2226929312583420722304833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5938478166889121926146221 2226929312583420722304833)
                    ·
                      refine ⟨1670196984437565541728625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2226929312583420722304833 1670196984437565541728625)
                      ·
                        rfl

theorem cell23_3252697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 3, 2].length) (baseStart_3252697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252697 prefixEnd_3252697 := by exact prefixLift 3252697
  have htrace : WordTrace (prefixWord ++ tailWord_3252697) baseStart_3252697 baseEnd_3252697 := by
    simpa [prefixWord, tailWord_3252697, baseEnd_3252697] using wordTrace_append hprefix tailTrace_3252697
  have hstable : (prefixWord ++ tailWord_3252697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252697).length < 2 ^ (prefixWord ++ tailWord_3252697).sum := by decide
  have hdescent : baseEnd_3252697 < baseStart_3252697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252738 : List Nat := [3, 4, 1, 2, 2, 2, 2, 1, 2, 1, 3]
def baseStart_3252738 : Nat := 118140960795 + 3252738 * 2 ^ 59
def prefixEnd_3252738 : Nat := 4983230072969 + 3 ^ 40 * 3252738 * 2
def baseEnd_3252738 : Nat := 1670218037144399881315937

theorem tailTrace_3252738 : CollatzResearch.WordTrace tailWord_3252738 prefixEnd_3252738 1670218037144399881315937 := by
  unfold tailWord_3252738
  simp only [CollatzResearch.WordTrace]
  refine ⟨29659275322473306067007717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79091400859928816178687245 29659275322473306067007717)
  ·
    refine ⟨5561114122963744887563947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29659275322473306067007717 5561114122963744887563947)
    ·
      refine ⟨8341671184445617331345921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5561114122963744887563947 8341671184445617331345921)
      ·
        refine ⟨6256253388334212998509441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8341671184445617331345921 6256253388334212998509441)
        ·
          refine ⟨4692190041250659748882081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6256253388334212998509441 4692190041250659748882081)
          ·
            refine ⟨3519142530937994811661561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4692190041250659748882081 3519142530937994811661561)
            ·
              refine ⟨2639356898203496108746171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3519142530937994811661561 2639356898203496108746171)
              ·
                refine ⟨3959035347305244163119257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2639356898203496108746171 3959035347305244163119257)
                ·
                  refine ⟨2969276510478933122339443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3959035347305244163119257 2969276510478933122339443)
                  ·
                    refine ⟨4453914765718399683509165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2969276510478933122339443 4453914765718399683509165)
                    ·
                      refine ⟨1670218037144399881315937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4453914765718399683509165 1670218037144399881315937)
                      ·
                        rfl

theorem cell23_3252738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_3252738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252738 prefixEnd_3252738 := by exact prefixLift 3252738
  have htrace : WordTrace (prefixWord ++ tailWord_3252738) baseStart_3252738 baseEnd_3252738 := by
    simpa [prefixWord, tailWord_3252738, baseEnd_3252738] using wordTrace_append hprefix tailTrace_3252738
  have hstable : (prefixWord ++ tailWord_3252738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252738).length < 2 ^ (prefixWord ++ tailWord_3252738).sum := by decide
  have hdescent : baseEnd_3252738 < baseStart_3252738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252773 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 1, 2, 5]
def baseStart_3252773 : Nat := 118140960795 + 3252773 * 2 ^ 59
def prefixEnd_3252773 : Nat := 4983230072969 + 3 ^ 40 * 3252773 * 2
def baseEnd_3252773 : Nat := 1670236008967307244378275

theorem tailTrace_3252773 : CollatzResearch.WordTrace tailWord_3252773 prefixEnd_3252773 1670236008967307244378275 := by
  unfold tailWord_3252773
  simp only [CollatzResearch.WordTrace]
  refine ⟨118638377844766425245554973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79092251896510950163703315 118638377844766425245554973)
  ·
    refine ⟨44489391691787409467083115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118638377844766425245554973 44489391691787409467083115)
    ·
      refine ⟨66734087537681114200624673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44489391691787409467083115 66734087537681114200624673)
      ·
        refine ⟨50050565653260835650468505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66734087537681114200624673 50050565653260835650468505)
        ·
          refine ⟨37537924239945626737851379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50050565653260835650468505 37537924239945626737851379)
          ·
            refine ⟨56306886359918440106777069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37537924239945626737851379 56306886359918440106777069)
            ·
              refine ⟨21115082384969415040041401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56306886359918440106777069 21115082384969415040041401)
              ·
                refine ⟨15836311788727061280031051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21115082384969415040041401 15836311788727061280031051)
                ·
                  refine ⟨23754467683090591920046577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15836311788727061280031051 23754467683090591920046577)
                  ·
                    refine ⟨17815850762317943940034933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23754467683090591920046577 17815850762317943940034933)
                    ·
                      refine ⟨1670236008967307244378275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17815850762317943940034933 1670236008967307244378275)
                      ·
                        rfl

theorem cell23_3252773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_3252773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252773 prefixEnd_3252773 := by exact prefixLift 3252773
  have htrace : WordTrace (prefixWord ++ tailWord_3252773) baseStart_3252773 baseEnd_3252773 := by
    simpa [prefixWord, tailWord_3252773, baseEnd_3252773] using wordTrace_append hprefix tailTrace_3252773
  have hstable : (prefixWord ++ tailWord_3252773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252773).length < 2 ^ (prefixWord ++ tailWord_3252773).sum := by decide
  have hdescent : baseEnd_3252773 < baseStart_3252773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252800 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 1, 6, 2]
def baseStart_3252800 : Nat := 118140960795 + 3252800 * 2 ^ 59
def prefixEnd_3252800 : Nat := 4983230072969 + 3 ^ 40 * 3252800 * 2
def baseEnd_3252800 : Nat := 1670249872944978638740651

theorem tailTrace_3252800 : CollatzResearch.WordTrace tailWord_3252800 prefixEnd_3252800 1670249872944978638740651 := by
  unfold tailWord_3252800
  simp only [CollatzResearch.WordTrace]
  refine ⟨59319681307834304428393927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79092908410445739237858569 59319681307834304428393927)
  ·
    refine ⟨88979521961751456642590891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59319681307834304428393927 88979521961751456642590891)
    ·
      refine ⟨133469282942627184963886337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88979521961751456642590891 133469282942627184963886337)
      ·
        refine ⟨100101962206970388722914753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133469282942627184963886337 100101962206970388722914753)
        ·
          refine ⟨75076471655227791542186065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100101962206970388722914753 75076471655227791542186065)
          ·
            refine ⟨56307353741420843656639549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75076471655227791542186065 56307353741420843656639549)
            ·
              refine ⟨21115257653032816371239831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56307353741420843656639549 21115257653032816371239831)
              ·
                refine ⟨31672886479549224556859747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21115257653032816371239831 31672886479549224556859747)
                ·
                  refine ⟨47509329719323836835289621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31672886479549224556859747 47509329719323836835289621)
                  ·
                    refine ⟨2226999830593304851654201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47509329719323836835289621 2226999830593304851654201)
                    ·
                      refine ⟨1670249872944978638740651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2226999830593304851654201 1670249872944978638740651)
                      ·
                        rfl

theorem cell23_3252800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 1, 6, 2].length) (baseStart_3252800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252800 prefixEnd_3252800 := by exact prefixLift 3252800
  have htrace : WordTrace (prefixWord ++ tailWord_3252800) baseStart_3252800 baseEnd_3252800 := by
    simpa [prefixWord, tailWord_3252800, baseEnd_3252800] using wordTrace_append hprefix tailTrace_3252800
  have hstable : (prefixWord ++ tailWord_3252800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252800).length < 2 ^ (prefixWord ++ tailWord_3252800).sum := by decide
  have hdescent : baseEnd_3252800 < baseStart_3252800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252810 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 5, 4]
def baseStart_3252810 : Nat := 118140960795 + 3252810 * 2 ^ 59
def prefixEnd_3252810 : Nat := 4983230072969 + 3 ^ 40 * 3252810 * 2
def baseEnd_3252810 : Nat := 556751669250507866538535

theorem tailTrace_3252810 : CollatzResearch.WordTrace tailWord_3252810 prefixEnd_3252810 556751669250507866538535 := by
  unfold tailWord_3252810
  simp only [CollatzResearch.WordTrace]
  refine ⟨29659931836408095141162971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79093151563754920376434589 29659931836408095141162971)
  ·
    refine ⟨44489897754612142711744457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29659931836408095141162971 44489897754612142711744457)
    ·
      refine ⟨33367423315959107033808343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44489897754612142711744457 33367423315959107033808343)
      ·
        refine ⟨50051134973938660550712515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33367423315959107033808343 50051134973938660550712515)
        ·
          refine ⟨75076702460907990826068773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50051134973938660550712515 75076702460907990826068773)
          ·
            refine ⟨14076881711420248279887895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75076702460907990826068773 14076881711420248279887895)
            ·
              refine ⟨21115322567130372419831843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14076881711420248279887895 21115322567130372419831843)
              ·
                refine ⟨31672983850695558629747765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21115322567130372419831843 31672983850695558629747765)
                ·
                  refine ⟨2969342236002708621538853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31672983850695558629747765 2969342236002708621538853)
                  ·
                    refine ⟨556751669250507866538535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2969342236002708621538853 556751669250507866538535)
                    ·
                      rfl

theorem cell23_3252810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_3252810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252810 prefixEnd_3252810 := by exact prefixLift 3252810
  have htrace : WordTrace (prefixWord ++ tailWord_3252810) baseStart_3252810 baseEnd_3252810 := by
    simpa [prefixWord, tailWord_3252810, baseEnd_3252810] using wordTrace_append hprefix tailTrace_3252810
  have hstable : (prefixWord ++ tailWord_3252810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252810).length < 2 ^ (prefixWord ++ tailWord_3252810).sum := by decide
  have hdescent : baseEnd_3252810 < baseStart_3252810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252817 : List Nat := [1, 2, 2, 1, 3, 5, 1, 1, 2, 1, 4]
def baseStart_3252817 : Nat := 118140960795 + 3252817 * 2 ^ 59
def prefixEnd_3252817 : Nat := 4983230072969 + 3 ^ 40 * 3252817 * 2
def baseEnd_3252817 : Nat := 1670258602116105072228073

theorem tailTrace_3252817 : CollatzResearch.WordTrace tailWord_3252817 prefixEnd_3252817 1670258602116105072228073 := by
  unfold tailWord_3252817
  simp only [CollatzResearch.WordTrace]
  refine ⟨118639982656607020760156705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79093321771071347173437803 118639982656607020760156705)
  ·
    refine ⟨88979986992455265570117529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118639982656607020760156705 88979986992455265570117529)
    ·
      refine ⟨66734990244341449177588147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88979986992455265570117529 66734990244341449177588147)
      ·
        refine ⟨100102485366512173766382221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66734990244341449177588147 100102485366512173766382221)
        ·
          refine ⟨37538432012442065162393333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100102485366512173766382221 37538432012442065162393333)
          ·
            refine ⟨3519228001166443608974375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37538432012442065162393333 3519228001166443608974375)
            ·
              refine ⟨5278842001749665413461563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3519228001166443608974375 5278842001749665413461563)
              ·
                refine ⟨7918263002624498120192345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5278842001749665413461563 7918263002624498120192345)
                ·
                  refine ⟨5938697251968373590144259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7918263002624498120192345 5938697251968373590144259)
                  ·
                    refine ⟨8908045877952560385216389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5938697251968373590144259 8908045877952560385216389)
                    ·
                      refine ⟨1670258602116105072228073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8908045877952560385216389 1670258602116105072228073)
                      ·
                        rfl

theorem cell23_3252817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 1, 4].length) (baseStart_3252817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252817 prefixEnd_3252817 := by exact prefixLift 3252817
  have htrace : WordTrace (prefixWord ++ tailWord_3252817) baseStart_3252817 baseEnd_3252817 := by
    simpa [prefixWord, tailWord_3252817, baseEnd_3252817] using wordTrace_append hprefix tailTrace_3252817
  have hstable : (prefixWord ++ tailWord_3252817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252817).length < 2 ^ (prefixWord ++ tailWord_3252817).sum := by decide
  have hdescent : baseEnd_3252817 < baseStart_3252817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252823 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 8]
def baseStart_3252823 : Nat := 118140960795 + 3252823 * 2 ^ 59
def prefixEnd_3252823 : Nat := 4983230072969 + 3 ^ 40 * 3252823 * 2
def baseEnd_3252823 : Nat := 185584631444448005417005

theorem tailTrace_3252823 : CollatzResearch.WordTrace tailWord_3252823 prefixEnd_3252823 185584631444448005417005 := by
  unfold tailWord_3252823
  simp only [CollatzResearch.WordTrace]
  refine ⟨118640201494585283784875123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79093467663056855856583415 118640201494585283784875123)
  ·
    refine ⟨177960302241877925677312685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118640201494585283784875123 177960302241877925677312685)
    ·
      refine ⟨66735113340704222128992257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177960302241877925677312685 66735113340704222128992257)
      ·
        refine ⟨50051335005528166596744193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66735113340704222128992257 50051335005528166596744193)
        ·
          refine ⟨37538501254146124947558145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50051335005528166596744193 37538501254146124947558145)
          ·
            refine ⟨28153875940609593710668609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37538501254146124947558145 28153875940609593710668609)
            ·
              refine ⟨21115406955457195283001457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28153875940609593710668609 21115406955457195283001457)
              ·
                refine ⟨15836555216592896462251093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21115406955457195283001457 15836555216592896462251093)
                ·
                  refine ⟨185584631444448005417005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15836555216592896462251093 185584631444448005417005)
                  ·
                    rfl

theorem cell23_3252823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 8].length) (baseStart_3252823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252823 prefixEnd_3252823 := by exact prefixLift 3252823
  have htrace : WordTrace (prefixWord ++ tailWord_3252823) baseStart_3252823 baseEnd_3252823 := by
    simpa [prefixWord, tailWord_3252823, baseEnd_3252823] using wordTrace_append hprefix tailTrace_3252823
  have hstable : (prefixWord ++ tailWord_3252823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252823).length < 2 ^ (prefixWord ++ tailWord_3252823).sum := by decide
  have hdescent : baseEnd_3252823 < baseStart_3252823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252857 : List Nat := [1, 2, 1, 3, 3, 3, 3, 1, 6]
def baseStart_3252857 : Nat := 118140960795 + 3252857 * 2 ^ 59
def prefixEnd_3252857 : Nat := 4983230072969 + 3 ^ 40 * 3252857 * 2
def baseEnd_3252857 : Nat := 185586571260253879525321

theorem tailTrace_3252857 : CollatzResearch.WordTrace tailWord_3252857 prefixEnd_3252857 185586571260253879525321 := by
  unfold tailWord_3252857
  simp only [CollatzResearch.WordTrace]
  refine ⟨118641441576462107591612825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79094294384308071727741883 118641441576462107591612825)
  ·
    refine ⟨88981081182346580693709619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118641441576462107591612825 88981081182346580693709619)
    ·
      refine ⟨133471621773519871040564429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88981081182346580693709619 133471621773519871040564429)
      ·
        refine ⟨50051858165069951640211661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133471621773519871040564429 50051858165069951640211661)
        ·
          refine ⟨18769446811901231865079373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50051858165069951640211661 18769446811901231865079373)
          ·
            refine ⟨7038542554462961949404765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18769446811901231865079373 7038542554462961949404765)
            ·
              refine ⟨2639453457923610731026787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7038542554462961949404765 2639453457923610731026787)
              ·
                refine ⟨3959180186885416096540181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2639453457923610731026787 3959180186885416096540181)
                ·
                  refine ⟨185586571260253879525321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3959180186885416096540181 185586571260253879525321)
                  ·
                    rfl

theorem cell23_3252857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 6].length) (baseStart_3252857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252857 prefixEnd_3252857 := by exact prefixLift 3252857
  have htrace : WordTrace (prefixWord ++ tailWord_3252857) baseStart_3252857 baseEnd_3252857 := by
    simpa [prefixWord, tailWord_3252857, baseEnd_3252857] using wordTrace_append hprefix tailTrace_3252857
  have hstable : (prefixWord ++ tailWord_3252857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252857).length < 2 ^ (prefixWord ++ tailWord_3252857).sum := by decide
  have hdescent : baseEnd_3252857 < baseStart_3252857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252867 : List Nat := [1, 1, 1, 3, 3, 1, 4, 2, 3, 1, 3]
def baseStart_3252867 : Nat := 118140960795 + 3252867 * 2 ^ 59
def prefixEnd_3252867 : Nat := 4983230072969 + 3 ^ 40 * 3252867 * 2
def baseEnd_3252867 : Nat := 1670284276148829876602843

theorem tailTrace_3252867 : CollatzResearch.WordTrace tailWord_3252867 prefixEnd_3252867 1670284276148829876602843 := by
  unfold tailWord_3252867
  simp only [CollatzResearch.WordTrace]
  refine ⟨118641806306425879299476855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79094537537617252866317903 118641806306425879299476855)
  ·
    refine ⟨177962709459638818949215283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118641806306425879299476855 177962709459638818949215283)
    ·
      refine ⟨266944064189458228423822925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177962709459638818949215283 266944064189458228423822925)
      ·
        refine ⟨100104024071046835658933597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266944064189458228423822925 100104024071046835658933597)
        ·
          refine ⟨37539009026642563372100099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100104024071046835658933597 37539009026642563372100099)
          ·
            refine ⟨56308513539963845058150149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37539009026642563372100099 56308513539963845058150149)
            ·
              refine ⟨10557846288743220948403153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56308513539963845058150149 10557846288743220948403153)
              ·
                refine ⟨7918384716557415711302365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10557846288743220948403153 7918384716557415711302365)
                ·
                  refine ⟨2969394268709030891738387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7918384716557415711302365 2969394268709030891738387)
                  ·
                    refine ⟨4454091403063546337607581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2969394268709030891738387 4454091403063546337607581)
                    ·
                      refine ⟨1670284276148829876602843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4454091403063546337607581 1670284276148829876602843)
                      ·
                        rfl

theorem cell23_3252867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 1, 3].length) (baseStart_3252867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252867 prefixEnd_3252867 := by exact prefixLift 3252867
  have htrace : WordTrace (prefixWord ++ tailWord_3252867) baseStart_3252867 baseEnd_3252867 := by
    simpa [prefixWord, tailWord_3252867, baseEnd_3252867] using wordTrace_append hprefix tailTrace_3252867
  have hstable : (prefixWord ++ tailWord_3252867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252867).length < 2 ^ (prefixWord ++ tailWord_3252867).sum := by decide
  have hdescent : baseEnd_3252867 < baseStart_3252867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252924 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 5, 2, 2]
def baseStart_3252924 : Nat := 118140960795 + 3252924 * 2 ^ 59
def prefixEnd_3252924 : Nat := 4983230072969 + 3 ^ 40 * 3252924 * 2
def baseEnd_3252924 : Nat := 1670313544546136153590081

theorem tailTrace_3252924 : CollatzResearch.WordTrace tailWord_3252924 prefixEnd_3252924 1670313544546136153590081 := by
  unfold tailWord_3252924
  simp only [CollatzResearch.WordTrace]
  refine ⟨59321942633609689017150913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79095923511479585356201217 59321942633609689017150913)
  ·
    refine ⟨44491456975207266762863185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59321942633609689017150913 44491456975207266762863185)
    ·
      refine ⟨33368592731405450072147389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44491456975207266762863185 33368592731405450072147389)
      ·
        refine ⟨12513222274277043777055271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33368592731405450072147389 12513222274277043777055271)
        ·
          refine ⟨18769833411415565665582907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12513222274277043777055271 18769833411415565665582907)
          ·
            refine ⟨28154750117123348498374361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18769833411415565665582907 28154750117123348498374361)
            ·
              refine ⟨21116062587842511373780771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28154750117123348498374361 21116062587842511373780771)
              ·
                refine ⟨31674093881763767060671157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21116062587842511373780771 31674093881763767060671157)
                ·
                  refine ⟨2969446301415353161937921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31674093881763767060671157 2969446301415353161937921)
                  ·
                    refine ⟨2227084726061514871453441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2969446301415353161937921 2227084726061514871453441)
                    ·
                      refine ⟨1670313544546136153590081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2227084726061514871453441 1670313544546136153590081)
                      ·
                        rfl

theorem cell23_3252924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_3252924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252924 prefixEnd_3252924 := by exact prefixLift 3252924
  have htrace : WordTrace (prefixWord ++ tailWord_3252924) baseStart_3252924 baseEnd_3252924 := by
    simpa [prefixWord, tailWord_3252924, baseEnd_3252924] using wordTrace_append hprefix tailTrace_3252924
  have hstable : (prefixWord ++ tailWord_3252924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252924).length < 2 ^ (prefixWord ++ tailWord_3252924).sum := by decide
  have hdescent : baseEnd_3252924 < baseStart_3252924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252927 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 3]
def baseStart_3252927 : Nat := 118140960795 + 3252927 * 2 ^ 59
def prefixEnd_3252927 : Nat := 4983230072969 + 3 ^ 40 * 3252927 * 2
def baseEnd_3252927 : Nat := 1670315084988099641852567

theorem tailTrace_3252927 : CollatzResearch.WordTrace tailWord_3252927 prefixEnd_3252927 1670315084988099641852567 := by
  unfold tailWord_3252927
  simp only [CollatzResearch.WordTrace]
  refine ⟨118643994686208509546661035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79095996457472339697774023 118643994686208509546661035)
  ·
    refine ⟨177965992029312764319991553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118643994686208509546661035 177965992029312764319991553)
    ·
      refine ⟨133474494021984573239993665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177965992029312764319991553 133474494021984573239993665)
      ·
        refine ⟨100105870516488429929995249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133474494021984573239993665 100105870516488429929995249)
        ·
          refine ⟨75079402887366322447496437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100105870516488429929995249 75079402887366322447496437)
          ·
            refine ⟨7038694020690592729452791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75079402887366322447496437 7038694020690592729452791)
            ·
              refine ⟨10558041031035889094179187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7038694020690592729452791 10558041031035889094179187)
              ·
                refine ⟨15837061546553833641268781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10558041031035889094179187 15837061546553833641268781)
                ·
                  refine ⟨5938898079957687615475793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15837061546553833641268781 5938898079957687615475793)
                  ·
                    refine ⟨4454173559968265711606845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5938898079957687615475793 4454173559968265711606845)
                    ·
                      refine ⟨1670315084988099641852567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4454173559968265711606845 1670315084988099641852567)
                      ·
                        rfl

theorem cell23_3252927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 3].length) (baseStart_3252927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252927 prefixEnd_3252927 := by exact prefixLift 3252927
  have htrace : WordTrace (prefixWord ++ tailWord_3252927) baseStart_3252927 baseEnd_3252927 := by
    simpa [prefixWord, tailWord_3252927, baseEnd_3252927] using wordTrace_append hprefix tailTrace_3252927
  have hstable : (prefixWord ++ tailWord_3252927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252927).length < 2 ^ (prefixWord ++ tailWord_3252927).sum := by decide
  have hdescent : baseEnd_3252927 < baseStart_3252927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252970 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_3252970 : Nat := 118140960795 + 3252970 * 2 ^ 59
def prefixEnd_3252970 : Nat := 4983230072969 + 3 ^ 40 * 3252970 * 2
def baseEnd_3252970 : Nat := 1670337164656242973614869

theorem tailTrace_3252970 : CollatzResearch.WordTrace tailWord_3252970 prefixEnd_3252970 1670337164656242973614869 := by
  unfold tailWord_3252970
  simp only [CollatzResearch.WordTrace]
  refine ⟨29661390756263181972619091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79097042016701818593650909 29661390756263181972619091)
  ·
    refine ⟨44492086134394772958928637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29661390756263181972619091 44492086134394772958928637)
    ·
      refine ⟨16684532300398039859598239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44492086134394772958928637 16684532300398039859598239)
      ·
        refine ⟨25026798450597059789397359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16684532300398039859598239 25026798450597059789397359)
        ·
          refine ⟨37540197675895589684096039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25026798450597059789397359 37540197675895589684096039)
          ·
            refine ⟨56310296513843384526144059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37540197675895589684096039 56310296513843384526144059)
            ·
              refine ⟨84465444770765076789216089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56310296513843384526144059 84465444770765076789216089)
              ·
                refine ⟨63349083578073807591912067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84465444770765076789216089 63349083578073807591912067)
                ·
                  refine ⟨95023625367110711387868101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63349083578073807591912067 95023625367110711387868101)
                  ·
                    refine ⟨17816929756333258385225269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95023625367110711387868101 17816929756333258385225269)
                    ·
                      refine ⟨1670337164656242973614869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17816929756333258385225269 1670337164656242973614869)
                      ·
                        rfl

theorem cell23_3252970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_3252970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252970 prefixEnd_3252970 := by exact prefixLift 3252970
  have htrace : WordTrace (prefixWord ++ tailWord_3252970) baseStart_3252970 baseEnd_3252970 := by
    simpa [prefixWord, tailWord_3252970, baseEnd_3252970] using wordTrace_append hprefix tailTrace_3252970
  have hstable : (prefixWord ++ tailWord_3252970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252970).length < 2 ^ (prefixWord ++ tailWord_3252970).sum := by decide
  have hdescent : baseEnd_3252970 < baseStart_3252970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252974 : List Nat := [4, 1, 2, 1, 1, 4, 2, 1, 1, 3, 3]
def baseStart_3252974 : Nat := 118140960795 + 3252974 * 2 ^ 59
def prefixEnd_3252974 : Nat := 4983230072969 + 3 ^ 40 * 3252974 * 2
def baseEnd_3252974 : Nat := 1670339218578860957964851

theorem tailTrace_3252974 : CollatzResearch.WordTrace tailWord_3252974 prefixEnd_3252974 1670339218578860957964851 := by
  unfold tailWord_3252974
  simp only [CollatzResearch.WordTrace]
  refine ⟨14830713614629779571702747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79097139278025491049081317 14830713614629779571702747)
  ·
    refine ⟨22246070421944669357554121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14830713614629779571702747 22246070421944669357554121)
    ·
      refine ⟨16684552816458502018165591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22246070421944669357554121 16684552816458502018165591)
      ·
        refine ⟨25026829224687753027248387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16684552816458502018165591 25026829224687753027248387)
        ·
          refine ⟨37540243837031629540872581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25026829224687753027248387 37540243837031629540872581)
          ·
            refine ⟨7038795719443430538913609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37540243837031629540872581 7038795719443430538913609)
            ·
              refine ⟨5279096789582572904185207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7038795719443430538913609 5279096789582572904185207)
              ·
                refine ⟨7918645184373859356277811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5279096789582572904185207 7918645184373859356277811)
                ·
                  refine ⟨11877967776560789034416717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7918645184373859356277811 11877967776560789034416717)
                  ·
                    refine ⟨4454237916210295887906269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11877967776560789034416717 4454237916210295887906269)
                    ·
                      refine ⟨1670339218578860957964851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4454237916210295887906269 1670339218578860957964851)
                      ·
                        rfl

theorem cell23_3252974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_3252974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252974 prefixEnd_3252974 := by exact prefixLift 3252974
  have htrace : WordTrace (prefixWord ++ tailWord_3252974) baseStart_3252974 baseEnd_3252974 := by
    simpa [prefixWord, tailWord_3252974, baseEnd_3252974] using wordTrace_append hprefix tailTrace_3252974
  have hstable : (prefixWord ++ tailWord_3252974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252974).length < 2 ^ (prefixWord ++ tailWord_3252974).sum := by decide
  have hdescent : baseEnd_3252974 < baseStart_3252974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3252984 : List Nat := [2, 1, 2, 1, 1, 2, 4, 4, 1, 3, 2]
def baseStart_3252984 : Nat := 118140960795 + 3252984 * 2 ^ 59
def prefixEnd_3252984 : Nat := 4983230072969 + 3 ^ 40 * 3252984 * 2
def baseEnd_3252984 : Nat := 1670344353385405918839805

theorem tailTrace_3252984 : CollatzResearch.WordTrace tailWord_3252984 prefixEnd_3252984 1670344353385405918839805 := by
  unfold tailWord_3252984
  simp only [CollatzResearch.WordTrace]
  refine ⟨59323036823501004140743003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79097382431334672187657337 59323036823501004140743003)
  ·
    refine ⟨88984555235251506211114505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59323036823501004140743003 88984555235251506211114505)
    ·
      refine ⟨66738416426438629658335879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88984555235251506211114505 66738416426438629658335879)
      ·
        refine ⟨100107624639657944487503819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66738416426438629658335879 100107624639657944487503819)
        ·
          refine ⟨150161436959486916731255729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100107624639657944487503819 150161436959486916731255729)
          ·
            refine ⟨112621077719615187548441797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150161436959486916731255729 112621077719615187548441797)
            ·
              refine ⟨21116452072427847665332837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112621077719615187548441797 21116452072427847665332837)
              ·
                refine ⟨3959334763580221437249907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21116452072427847665332837 3959334763580221437249907)
                ·
                  refine ⟨5939002145370332155874861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3959334763580221437249907 5939002145370332155874861)
                  ·
                    refine ⟨2227125804513874558453073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5939002145370332155874861 2227125804513874558453073)
                    ·
                      refine ⟨1670344353385405918839805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2227125804513874558453073 1670344353385405918839805)
                      ·
                        rfl

theorem cell23_3252984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 1, 3, 2].length) (baseStart_3252984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3252984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3252984 prefixEnd_3252984 := by exact prefixLift 3252984
  have htrace : WordTrace (prefixWord ++ tailWord_3252984) baseStart_3252984 baseEnd_3252984 := by
    simpa [prefixWord, tailWord_3252984, baseEnd_3252984] using wordTrace_append hprefix tailTrace_3252984
  have hstable : (prefixWord ++ tailWord_3252984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3252984).length < 2 ^ (prefixWord ++ tailWord_3252984).sum := by decide
  have hdescent : baseEnd_3252984 < baseStart_3252984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3252984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253001 : List Nat := [1, 2, 1, 1, 3, 2, 6, 1, 1, 3, 2]
def baseStart_3253001 : Nat := 118140960795 + 3253001 * 2 ^ 59
def prefixEnd_3253001 : Nat := 4983230072969 + 3 ^ 40 * 3253001 * 2
def baseEnd_3253001 : Nat := 1670353082556532352327227

theorem tailTrace_3253001 : CollatzResearch.WordTrace tailWord_3253001 prefixEnd_3253001 1670353082556532352327227 := by
  unfold tailWord_3253001
  simp only [CollatzResearch.WordTrace]
  refine ⟨118646693687940420184854857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79097795791960280123236571 118646693687940420184854857)
  ·
    refine ⟨88985020265955315138641143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118646693687940420184854857 88985020265955315138641143)
    ·
      refine ⟨133477530398932972707961715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88985020265955315138641143 133477530398932972707961715)
      ·
        refine ⟨200216295598399459061942573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133477530398932972707961715 200216295598399459061942573)
        ·
          refine ⟨75081110849399797148228465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200216295598399459061942573 75081110849399797148228465)
          ·
            refine ⟨56310833137049847861171349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75081110849399797148228465 56310833137049847861171349)
            ·
              refine ⟨2639570303299211618492407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56310833137049847861171349 2639570303299211618492407)
              ·
                refine ⟨3959355454948817427738611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2639570303299211618492407 3959355454948817427738611)
                ·
                  refine ⟨5939033182423226141607917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3959355454948817427738611 5939033182423226141607917)
                  ·
                    refine ⟨2227137443408709803102969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5939033182423226141607917 2227137443408709803102969)
                    ·
                      refine ⟨1670353082556532352327227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2227137443408709803102969 1670353082556532352327227)
                      ·
                        rfl

theorem cell23_3253001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 1, 3, 2].length) (baseStart_3253001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253001 prefixEnd_3253001 := by exact prefixLift 3253001
  have htrace : WordTrace (prefixWord ++ tailWord_3253001) baseStart_3253001 baseEnd_3253001 := by
    simpa [prefixWord, tailWord_3253001, baseEnd_3253001] using wordTrace_append hprefix tailTrace_3253001
  have hstable : (prefixWord ++ tailWord_3253001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253001).length < 2 ^ (prefixWord ++ tailWord_3253001).sum := by decide
  have hdescent : baseEnd_3253001 < baseStart_3253001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253074 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2]
def baseStart_3253074 : Nat := 118140960795 + 3253074 * 2 ^ 59
def prefixEnd_3253074 : Nat := 4983230072969 + 3 ^ 40 * 3253074 * 2
def baseEnd_3253074 : Nat := 1670390566644310566714391

theorem tailTrace_3253074 : CollatzResearch.WordTrace tailWord_3253074 prefixEnd_3253074 1670390566644310566714391 := by
  unfold tailWord_3253074
  simp only [CollatzResearch.WordTrace]
  refine ⟨29662339054168988413065569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79099570811117302434841517 29662339054168988413065569)
  ·
    refine ⟨22246754290626741309799177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29662339054168988413065569 22246754290626741309799177)
    ·
      refine ⟨16685065717970055982349383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22246754290626741309799177 16685065717970055982349383)
      ·
        refine ⟨25027598576955083973524075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16685065717970055982349383 25027598576955083973524075)
        ·
          refine ⟨37541397865432625960286113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25027598576955083973524075 37541397865432625960286113)
          ·
            refine ⟨28156048399074469470214585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37541397865432625960286113 28156048399074469470214585)
            ·
              refine ⟨21117036299305852102660939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28156048399074469470214585 21117036299305852102660939)
              ·
                refine ⟨31675554448958778153991409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21117036299305852102660939 31675554448958778153991409)
                ·
                  refine ⟨23756665836719083615493557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31675554448958778153991409 23756665836719083615493557)
                  ·
                    refine ⟨2227187422192414088952521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23756665836719083615493557 2227187422192414088952521)
                    ·
                      refine ⟨1670390566644310566714391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2227187422192414088952521 1670390566644310566714391)
                      ·
                        rfl

theorem cell23_3253074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_3253074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253074 prefixEnd_3253074 := by exact prefixLift 3253074
  have htrace : WordTrace (prefixWord ++ tailWord_3253074) baseStart_3253074 baseEnd_3253074 := by
    simpa [prefixWord, tailWord_3253074, baseEnd_3253074] using wordTrace_append hprefix tailTrace_3253074
  have hstable : (prefixWord ++ tailWord_3253074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253074).length < 2 ^ (prefixWord ++ tailWord_3253074).sum := by decide
  have hdescent : baseEnd_3253074 < baseStart_3253074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253077 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 1, 2, 5]
def baseStart_3253077 : Nat := 118140960795 + 3253077 * 2 ^ 59
def prefixEnd_3253077 : Nat := 4983230072969 + 3 ^ 40 * 3253077 * 2
def baseEnd_3253077 : Nat := 1670392107086274054976877

theorem tailTrace_3253077 : CollatzResearch.WordTrace tailWord_3253077 prefixEnd_3253077 1670392107086274054976877 := by
  unfold tailWord_3253077
  simp only [CollatzResearch.WordTrace]
  refine ⟨118649465635665085164621485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79099643757110056776414323 118649465635665085164621485)
  ·
    refine ⟨44493549613374406936733057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118649465635665085164621485 44493549613374406936733057)
    ·
      refine ⟨33370162210030805202549793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44493549613374406936733057 33370162210030805202549793)
      ·
        refine ⟨25027621657523103901912345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33370162210030805202549793 25027621657523103901912345)
        ·
          refine ⟨18770716243142327926434259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25027621657523103901912345 18770716243142327926434259)
          ·
            refine ⟨28156074364713491889651389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18770716243142327926434259 28156074364713491889651389)
            ·
              refine ⟨10558527886767559458619271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28156074364713491889651389 10558527886767559458619271)
              ·
                refine ⟨15837791830151339187928907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10558527886767559458619271 15837791830151339187928907)
                ·
                  refine ⟨23756687745227008781893361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15837791830151339187928907 23756687745227008781893361)
                  ·
                    refine ⟨17817515808920256586420021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23756687745227008781893361 17817515808920256586420021)
                    ·
                      refine ⟨1670392107086274054976877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17817515808920256586420021 1670392107086274054976877)
                      ·
                        rfl

theorem cell23_3253077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_3253077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253077 prefixEnd_3253077 := by exact prefixLift 3253077
  have htrace : WordTrace (prefixWord ++ tailWord_3253077) baseStart_3253077 baseEnd_3253077 := by
    simpa [prefixWord, tailWord_3253077, baseEnd_3253077] using wordTrace_append hprefix tailTrace_3253077
  have hstable : (prefixWord ++ tailWord_3253077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253077).length < 2 ^ (prefixWord ++ tailWord_3253077).sum := by decide
  have hdescent : baseEnd_3253077 < baseStart_3253077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253087 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 4]
def baseStart_3253087 : Nat := 118140960795 + 3253087 * 2 ^ 59
def prefixEnd_3253087 : Nat := 4983230072969 + 3 ^ 40 * 3253087 * 2
def baseEnd_3253087 : Nat := 1670397241892819015851831

theorem tailTrace_3253087 : CollatzResearch.WordTrace tailWord_3253087 prefixEnd_3253087 1670397241892819015851831 := by
  unfold tailWord_3253087
  simp only [CollatzResearch.WordTrace]
  refine ⟨118649830365628856872485515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79099886910419237914990343 118649830365628856872485515)
  ·
    refine ⟨177974745548443285308728273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118649830365628856872485515 177974745548443285308728273)
    ·
      refine ⟨133481059161332463981546205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177974745548443285308728273 133481059161332463981546205)
      ·
        refine ⟨50055397185499673993079827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133481059161332463981546205 50055397185499673993079827)
        ·
          refine ⟨75083095778249510989619741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50055397185499673993079827 75083095778249510989619741)
          ·
            refine ⟨28156160916843566621107403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75083095778249510989619741 28156160916843566621107403)
            ·
              refine ⟨42234241375265349931661105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28156160916843566621107403 42234241375265349931661105)
              ·
                refine ⟨31675681031449012448745829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42234241375265349931661105 31675681031449012448745829)
                ·
                  refine ⟨5939190193396689834139843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31675681031449012448745829 5939190193396689834139843)
                  ·
                    refine ⟨8908785290095034751209765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5939190193396689834139843 8908785290095034751209765)
                    ·
                      refine ⟨1670397241892819015851831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8908785290095034751209765 1670397241892819015851831)
                      ·
                        rfl

theorem cell23_3253087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_3253087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253087 prefixEnd_3253087 := by exact prefixLift 3253087
  have htrace : WordTrace (prefixWord ++ tailWord_3253087) baseStart_3253087 baseEnd_3253087 := by
    simpa [prefixWord, tailWord_3253087, baseEnd_3253087] using wordTrace_append hprefix tailTrace_3253087
  have hstable : (prefixWord ++ tailWord_3253087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253087).length < 2 ^ (prefixWord ++ tailWord_3253087).sum := by decide
  have hdescent : baseEnd_3253087 < baseStart_3253087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253107 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 3]
def baseStart_3253107 : Nat := 118140960795 + 3253107 * 2 ^ 59
def prefixEnd_3253107 : Nat := 4983230072969 + 3 ^ 40 * 3253107 * 2
def baseEnd_3253107 : Nat := 1670407511505908937601739

theorem tailTrace_3253107 : CollatzResearch.WordTrace tailWord_3253107 prefixEnd_3253107 1670407511505908937601739 := by
  unfold tailWord_3253107
  simp only [CollatzResearch.WordTrace]
  refine ⟨118650559825556400288213575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79100373217037600192142383 118650559825556400288213575)
  ·
    refine ⟨177975839738334600432320363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118650559825556400288213575 177975839738334600432320363)
    ·
      refine ⟨266963759607501900648480545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177975839738334600432320363 266963759607501900648480545)
      ·
        refine ⟨200222819705626425486360409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266963759607501900648480545 200222819705626425486360409)
        ·
          refine ⟨150167114779219819114770307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200222819705626425486360409 150167114779219819114770307)
          ·
            refine ⟨225250672168829728672155461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150167114779219819114770307 225250672168829728672155461)
            ·
              refine ⟨42234501031655574126029149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225250672168829728672155461 42234501031655574126029149)
              ·
                refine ⟨15837937886870840297260931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42234501031655574126029149 15837937886870840297260931)
                ·
                  refine ⟨23756906830306260445891397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15837937886870840297260931 23756906830306260445891397)
                  ·
                    refine ⟨4454420030682423833604637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23756906830306260445891397 4454420030682423833604637)
                    ·
                      refine ⟨1670407511505908937601739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4454420030682423833604637 1670407511505908937601739)
                      ·
                        rfl

theorem cell23_3253107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 3].length) (baseStart_3253107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253107 prefixEnd_3253107 := by exact prefixLift 3253107
  have htrace : WordTrace (prefixWord ++ tailWord_3253107) baseStart_3253107 baseEnd_3253107 := by
    simpa [prefixWord, tailWord_3253107, baseEnd_3253107] using wordTrace_append hprefix tailTrace_3253107
  have hstable : (prefixWord ++ tailWord_3253107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253107).length < 2 ^ (prefixWord ++ tailWord_3253107).sum := by decide
  have hdescent : baseEnd_3253107 < baseStart_3253107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253122 : List Nat := [3, 4, 2, 2, 1, 2, 2, 2, 5]
def baseStart_3253122 : Nat := 118140960795 + 3253122 * 2 ^ 59
def prefixEnd_3253122 : Nat := 4983230072969 + 3 ^ 40 * 3253122 * 2
def baseEnd_3253122 : Nat := 185601690412858486546019

theorem tailTrace_3253122 : CollatzResearch.WordTrace tailWord_3253122 prefixEnd_3253122 185601690412858486546019 := by
  unfold tailWord_3253122
  simp only [CollatzResearch.WordTrace]
  refine ⟨29662776730125514462502405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79100737947001371900006413 29662776730125514462502405)
  ·
    refine ⟨5561770636898533961719201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29662776730125514462502405 5561770636898533961719201)
    ·
      refine ⟨4171327977673900471289401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5561770636898533961719201 4171327977673900471289401)
      ·
        refine ⟨3128495983255425353467051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4171327977673900471289401 3128495983255425353467051)
        ·
          refine ⟨4692743974883138030200577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3128495983255425353467051 4692743974883138030200577)
          ·
            refine ⟨3519557981162353522650433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4692743974883138030200577 3519557981162353522650433)
            ·
              refine ⟨2639668485871765141987825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3519557981162353522650433 2639668485871765141987825)
              ·
                refine ⟨1979751364403823856490869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2639668485871765141987825 1979751364403823856490869)
                ·
                  refine ⟨185601690412858486546019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1979751364403823856490869 185601690412858486546019)
                  ·
                    rfl

theorem cell23_3253122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_3253122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253122 prefixEnd_3253122 := by exact prefixLift 3253122
  have htrace : WordTrace (prefixWord ++ tailWord_3253122) baseStart_3253122 baseEnd_3253122 := by
    simpa [prefixWord, tailWord_3253122, baseEnd_3253122] using wordTrace_append hprefix tailTrace_3253122
  have hstable : (prefixWord ++ tailWord_3253122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253122).length < 2 ^ (prefixWord ++ tailWord_3253122).sum := by decide
  have hdescent : baseEnd_3253122 < baseStart_3253122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253137 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 3]
def baseStart_3253137 : Nat := 118140960795 + 3253137 * 2 ^ 59
def prefixEnd_3253137 : Nat := 4983230072969 + 3 ^ 40 * 3253137 * 2
def baseEnd_3253137 : Nat := 1670422915925543820226601

theorem tailTrace_3253137 : CollatzResearch.WordTrace tailWord_3253137 prefixEnd_3253137 1670422915925543820226601 := by
  unfold tailWord_3253137
  simp only [CollatzResearch.WordTrace]
  refine ⟨118651654015447715411805665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79101102676965143607870443 118651654015447715411805665)
  ·
    refine ⟨88988740511585786558854249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118651654015447715411805665 88988740511585786558854249)
    ·
      refine ⟨66741555383689339919140687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88988740511585786558854249 66741555383689339919140687)
      ·
        refine ⟨100112333075534009878711031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66741555383689339919140687 100112333075534009878711031)
        ·
          refine ⟨150168499613301014818066547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100112333075534009878711031 150168499613301014818066547)
          ·
            refine ⟨225252749419951522227099821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150168499613301014818066547 225252749419951522227099821)
            ·
              refine ⟨84469781032481820835162433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225252749419951522227099821 84469781032481820835162433)
              ·
                refine ⟨63352335774361365626371825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84469781032481820835162433 63352335774361365626371825)
                ·
                  refine ⟨47514251830771024219778869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63352335774361365626371825 47514251830771024219778869)
                  ·
                    refine ⟨4454461109134783520604269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47514251830771024219778869 4454461109134783520604269)
                    ·
                      refine ⟨1670422915925543820226601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4454461109134783520604269 1670422915925543820226601)
                      ·
                        rfl

theorem cell23_3253137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 3].length) (baseStart_3253137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253137 prefixEnd_3253137 := by exact prefixLift 3253137
  have htrace : WordTrace (prefixWord ++ tailWord_3253137) baseStart_3253137 baseEnd_3253137 := by
    simpa [prefixWord, tailWord_3253137, baseEnd_3253137] using wordTrace_append hprefix tailTrace_3253137
  have hstable : (prefixWord ++ tailWord_3253137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253137).length < 2 ^ (prefixWord ++ tailWord_3253137).sum := by decide
  have hdescent : baseEnd_3253137 < baseStart_3253137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253138 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 2, 4, 2]
def baseStart_3253138 : Nat := 118140960795 + 3253138 * 2 ^ 59
def prefixEnd_3253138 : Nat := 4983230072969 + 3 ^ 40 * 3253138 * 2
def baseEnd_3253138 : Nat := 1670423429406198316314097

theorem tailTrace_3253138 : CollatzResearch.WordTrace tailWord_3253138 prefixEnd_3253138 1670423429406198316314097 := by
  unfold tailWord_3253138
  simp only [CollatzResearch.WordTrace]
  refine ⟨29662922622111023145648017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79101126992296061721728045 29662922622111023145648017)
  ·
    refine ⟨22247191966583267359236013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29662922622111023145648017 22247191966583267359236013)
    ·
      refine ⟨8342696987468725259713505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22247191966583267359236013 8342696987468725259713505)
      ·
        refine ⟨6257022740601543944785129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8342696987468725259713505 6257022740601543944785129)
        ·
          refine ⟨4692767055451157958588847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6257022740601543944785129 4692767055451157958588847)
          ·
            refine ⟨7039150583176736937883271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4692767055451157958588847 7039150583176736937883271)
            ·
              refine ⟨10558725874765105406824907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7039150583176736937883271 10558725874765105406824907)
              ·
                refine ⟨15838088812147658110237361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10558725874765105406824907 15838088812147658110237361)
                ·
                  refine ⟨11878566609110743582678021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15838088812147658110237361 11878566609110743582678021)
                  ·
                    refine ⟨2227231239208264421752129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11878566609110743582678021 2227231239208264421752129)
                    ·
                      refine ⟨1670423429406198316314097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2227231239208264421752129 1670423429406198316314097)
                      ·
                        rfl

theorem cell23_3253138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_3253138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253138 prefixEnd_3253138 := by exact prefixLift 3253138
  have htrace : WordTrace (prefixWord ++ tailWord_3253138) baseStart_3253138 baseEnd_3253138 := by
    simpa [prefixWord, tailWord_3253138, baseEnd_3253138] using wordTrace_append hprefix tailTrace_3253138
  have hstable : (prefixWord ++ tailWord_3253138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253138).length < 2 ^ (prefixWord ++ tailWord_3253138).sum := by decide
  have hdescent : baseEnd_3253138 < baseStart_3253138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253164 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 1, 5, 2]
def baseStart_3253164 : Nat := 118140960795 + 3253164 * 2 ^ 59
def prefixEnd_3253164 : Nat := 4983230072969 + 3 ^ 40 * 3253164 * 2
def baseEnd_3253164 : Nat := 1670436779903215214588977

theorem tailTrace_3253164 : CollatzResearch.WordTrace tailWord_3253164 prefixEnd_3253164 1670436779903215214588977 := by
  unfold tailWord_3253164
  simp only [CollatzResearch.WordTrace]
  refine ⟨59326319393174949511519273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79101759190899932682025697 59326319393174949511519273)
  ·
    refine ⟨44494739544881212133639455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59326319393174949511519273 44494739544881212133639455)
    ·
      refine ⟨66742109317321818200459183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44494739544881212133639455 66742109317321818200459183)
      ·
        refine ⟨100113163975982727300688775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66742109317321818200459183 100113163975982727300688775)
        ·
          refine ⟨150169745963974090951033163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100113163975982727300688775 150169745963974090951033163)
          ·
            refine ⟨225254618945961136426549745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150169745963974090951033163 225254618945961136426549745)
            ·
              refine ⟨168940964209470852319912309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225254618945961136426549745 168940964209470852319912309)
              ·
                refine ⟨15838215394637892404991779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168940964209470852319912309 15838215394637892404991779)
                ·
                  refine ⟨23757323091956838607487669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15838215394637892404991779 23757323091956838607487669)
                  ·
                    refine ⟨2227249039870953619451969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23757323091956838607487669 2227249039870953619451969)
                    ·
                      refine ⟨1670436779903215214588977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2227249039870953619451969 1670436779903215214588977)
                      ·
                        rfl

theorem cell23_3253164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 5, 2].length) (baseStart_3253164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253164 prefixEnd_3253164 := by exact prefixLift 3253164
  have htrace : WordTrace (prefixWord ++ tailWord_3253164) baseStart_3253164 baseEnd_3253164 := by
    simpa [prefixWord, tailWord_3253164, baseEnd_3253164] using wordTrace_append hprefix tailTrace_3253164
  have hstable : (prefixWord ++ tailWord_3253164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253164).length < 2 ^ (prefixWord ++ tailWord_3253164).sum := by decide
  have hdescent : baseEnd_3253164 < baseStart_3253164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253224 : List Nat := [2, 1, 4, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_3253224 : Nat := 118140960795 + 3253224 * 2 ^ 59
def prefixEnd_3253224 : Nat := 4983230072969 + 3 ^ 40 * 3253224 * 2
def baseEnd_3253224 : Nat := 1670467588742484979838701

theorem tailTrace_3253224 : CollatzResearch.WordTrace tailWord_3253224 prefixEnd_3253224 1670467588742484979838701 := by
  unfold tailWord_3253224
  simp only [CollatzResearch.WordTrace]
  refine ⟨59327413583066264635111363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79103218110755019513481817 59327413583066264635111363)
  ·
    refine ⟨88991120374599396952667045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59327413583066264635111363 88991120374599396952667045)
    ·
      refine ⟨16685835070237386928625071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88991120374599396952667045 16685835070237386928625071)
      ·
        refine ⟨25028752605356080392937607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16685835070237386928625071 25028752605356080392937607)
        ·
          refine ⟨37543128908034120589406411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25028752605356080392937607 37543128908034120589406411)
          ·
            refine ⟨56314693362051180884109617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37543128908034120589406411 56314693362051180884109617)
            ·
              refine ⟨42236020021538385663082213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56314693362051180884109617 42236020021538385663082213)
              ·
                refine ⟨7919253754038447311827915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42236020021538385663082213 7919253754038447311827915)
                ·
                  refine ⟨11878880631057670967741873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7919253754038447311827915 11878880631057670967741873)
                  ·
                    refine ⟨8909160473293253225806405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11878880631057670967741873 8909160473293253225806405)
                    ·
                      refine ⟨1670467588742484979838701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8909160473293253225806405 1670467588742484979838701)
                      ·
                        rfl

theorem cell23_3253224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_3253224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253224 prefixEnd_3253224 := by exact prefixLift 3253224
  have htrace : WordTrace (prefixWord ++ tailWord_3253224) baseStart_3253224 baseEnd_3253224 := by
    simpa [prefixWord, tailWord_3253224, baseEnd_3253224] using wordTrace_append hprefix tailTrace_3253224
  have hstable : (prefixWord ++ tailWord_3253224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253224).length < 2 ^ (prefixWord ++ tailWord_3253224).sum := by decide
  have hdescent : baseEnd_3253224 < baseStart_3253224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253231 : List Nat := [1, 1, 2, 1, 4, 3, 2, 3, 1, 2, 3]
def baseStart_3253231 : Nat := 118140960795 + 3253231 * 2 ^ 59
def prefixEnd_3253231 : Nat := 4983230072969 + 3 ^ 40 * 3253231 * 2
def baseEnd_3253231 : Nat := 1670471183107066452451169

theorem tailTrace_3253231 : CollatzResearch.WordTrace tailWord_3253231 prefixEnd_3253231 1670471183107066452451169 := by
  unfold tailWord_3253231
  simp only [CollatzResearch.WordTrace]
  refine ⟨118655082477107169465727547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79103388318071446310485031 118655082477107169465727547)
  ·
    refine ⟨177982623715660754198591321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118655082477107169465727547 177982623715660754198591321)
    ·
      refine ⟨133486967786745565648943491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177982623715660754198591321 133486967786745565648943491)
      ·
        refine ⟨200230451680118348473415237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133486967786745565648943491 200230451680118348473415237)
        ·
          refine ⟨37543209690022190338765357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 200230451680118348473415237 37543209690022190338765357)
          ·
            refine ⟨14078703633758321377037009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37543209690022190338765357 14078703633758321377037009)
            ·
              refine ⟨10559027725318741032777757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14078703633758321377037009 10559027725318741032777757)
              ·
                refine ⟨3959635396994527887291659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10559027725318741032777757 3959635396994527887291659)
                ·
                  refine ⟨5939453095491791830937489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3959635396994527887291659 5939453095491791830937489)
                  ·
                    refine ⟨4454589821618843873203117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5939453095491791830937489 4454589821618843873203117)
                    ·
                      refine ⟨1670471183107066452451169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4454589821618843873203117 1670471183107066452451169)
                      ·
                        rfl

theorem cell23_3253231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 2, 3].length) (baseStart_3253231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253231 prefixEnd_3253231 := by exact prefixLift 3253231
  have htrace : WordTrace (prefixWord ++ tailWord_3253231) baseStart_3253231 baseEnd_3253231 := by
    simpa [prefixWord, tailWord_3253231, baseEnd_3253231] using wordTrace_append hprefix tailTrace_3253231
  have hstable : (prefixWord ++ tailWord_3253231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253231).length < 2 ^ (prefixWord ++ tailWord_3253231).sum := by decide
  have hdescent : baseEnd_3253231 < baseStart_3253231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253267 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 8]
def baseStart_3253267 : Nat := 118140960795 + 3253267 * 2 ^ 59
def prefixEnd_3253267 : Nat := 4983230072969 + 3 ^ 40 * 3253267 * 2
def baseEnd_3253267 : Nat := 1670489668410628311601003

theorem tailTrace_3253267 : CollatzResearch.WordTrace tailWord_3253267 prefixEnd_3253267 1670489668410628311601003 := by
  unfold tailWord_3253267
  simp only [CollatzResearch.WordTrace]
  refine ⟨118656395504976747614038055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79104263669984498409358703 118656395504976747614038055)
  ·
    refine ⟨177984593257465121421057083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118656395504976747614038055 177984593257465121421057083)
    ·
      refine ⟨266976889886197682131585625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177984593257465121421057083 266976889886197682131585625)
      ·
        refine ⟨200232667414648261598689219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266976889886197682131585625 200232667414648261598689219)
        ·
          refine ⟨300349001121972392398033829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200232667414648261598689219 300349001121972392398033829)
          ·
            refine ⟨56315437710369823574631343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 300349001121972392398033829 56315437710369823574631343)
            ·
              refine ⟨84473156565554735361947015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56315437710369823574631343 84473156565554735361947015)
              ·
                refine ⟨126709734848332103042920523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84473156565554735361947015 126709734848332103042920523)
                ·
                  refine ⟨190064602272498154564380785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126709734848332103042920523 190064602272498154564380785)
                  ·
                    refine ⟨142548451704373615923285589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 190064602272498154564380785 142548451704373615923285589)
                    ·
                      refine ⟨1670489668410628311601003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 142548451704373615923285589 1670489668410628311601003)
                      ·
                        rfl

theorem cell23_3253267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_3253267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253267 prefixEnd_3253267 := by exact prefixLift 3253267
  have htrace : WordTrace (prefixWord ++ tailWord_3253267) baseStart_3253267 baseEnd_3253267 := by
    simpa [prefixWord, tailWord_3253267, baseEnd_3253267] using wordTrace_append hprefix tailTrace_3253267
  have hstable : (prefixWord ++ tailWord_3253267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253267).length < 2 ^ (prefixWord ++ tailWord_3253267).sum := by decide
  have hdescent : baseEnd_3253267 < baseStart_3253267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253301 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 5, 4, 2]
def baseStart_3253301 : Nat := 118140960795 + 3253301 * 2 ^ 59
def prefixEnd_3253301 : Nat := 4983230072969 + 3 ^ 40 * 3253301 * 2
def baseEnd_3253301 : Nat := 1670507126752881178575847

theorem tailTrace_3253301 : CollatzResearch.WordTrace tailWord_3253301 prefixEnd_3253301 1670507126752881178575847 := by
  unfold tailWord_3253301
  simp only [CollatzResearch.WordTrace]
  refine ⟨118657635586853571420775757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79105090391235714280517171 118657635586853571420775757)
  ·
    refine ⟨44496613345070089282790909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118657635586853571420775757 44496613345070089282790909)
    ·
      refine ⟨16686230004401283481046591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44496613345070089282790909 16686230004401283481046591)
      ·
        refine ⟨25029345006601925221569887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16686230004401283481046591 25029345006601925221569887)
        ·
          refine ⟨37544017509902887832354831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25029345006601925221569887 37544017509902887832354831)
          ·
            refine ⟨56316026264854331748532247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37544017509902887832354831 56316026264854331748532247)
            ·
              refine ⟨84474039397281497622798371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56316026264854331748532247 84474039397281497622798371)
              ·
                refine ⟨126711059095922246434197557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84474039397281497622798371 126711059095922246434197557)
                ·
                  refine ⟨11879161790242710603206021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126711059095922246434197557 11879161790242710603206021)
                  ·
                    refine ⟨2227342835670508238101129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11879161790242710603206021 2227342835670508238101129)
                    ·
                      refine ⟨1670507126752881178575847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2227342835670508238101129 1670507126752881178575847)
                      ·
                        rfl

theorem cell23_3253301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_3253301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253301 prefixEnd_3253301 := by exact prefixLift 3253301
  have htrace : WordTrace (prefixWord ++ tailWord_3253301) baseStart_3253301 baseEnd_3253301 := by
    simpa [prefixWord, tailWord_3253301, baseEnd_3253301] using wordTrace_append hprefix tailTrace_3253301
  have hstable : (prefixWord ++ tailWord_3253301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253301).length < 2 ^ (prefixWord ++ tailWord_3253301).sum := by decide
  have hdescent : baseEnd_3253301 < baseStart_3253301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253351 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 3]
def baseStart_3253351 : Nat := 118140960795 + 3253351 * 2 ^ 59
def prefixEnd_3253351 : Nat := 4983230072969 + 3 ^ 40 * 3253351 * 2
def baseEnd_3253351 : Nat := 1670532800785605982950617

theorem tailTrace_3253351 : CollatzResearch.WordTrace tailWord_3253351 prefixEnd_3253351 1670532800785605982950617 := by
  unfold tailWord_3253351
  simp only [CollatzResearch.WordTrace]
  refine ⟨118659459236672429960095907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79106306157781619973397271 118659459236672429960095907)
  ·
    refine ⟨177989188855008644940143861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118659459236672429960095907 177989188855008644940143861)
    ·
      refine ⟨16686486455157060463138487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177989188855008644940143861 16686486455157060463138487)
      ·
        refine ⟨25029729682735590694707731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16686486455157060463138487 25029729682735590694707731)
        ·
          refine ⟨37544594524103386042061597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25029729682735590694707731 37544594524103386042061597)
          ·
            refine ⟨14079222946538769765773099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37544594524103386042061597 14079222946538769765773099)
            ·
              refine ⟨21118834419808154648659649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14079222946538769765773099 21118834419808154648659649)
              ·
                refine ⟨15839125814856115986494737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21118834419808154648659649 15839125814856115986494737)
                ·
                  refine ⟨11879344361142086989871053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15839125814856115986494737 11879344361142086989871053)
                  ·
                    refine ⟨4454754135428282621201645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11879344361142086989871053 4454754135428282621201645)
                    ·
                      refine ⟨1670532800785605982950617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4454754135428282621201645 1670532800785605982950617)
                      ·
                        rfl

theorem cell23_3253351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_3253351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253351 prefixEnd_3253351 := by exact prefixLift 3253351
  have htrace : WordTrace (prefixWord ++ tailWord_3253351) baseStart_3253351 baseEnd_3253351 := by
    simpa [prefixWord, tailWord_3253351, baseEnd_3253351] using wordTrace_append hprefix tailTrace_3253351
  have hstable : (prefixWord ++ tailWord_3253351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253351).length < 2 ^ (prefixWord ++ tailWord_3253351).sum := by decide
  have hdescent : baseEnd_3253351 < baseStart_3253351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253352 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 4, 2, 2]
def baseStart_3253352 : Nat := 118140960795 + 3253352 * 2 ^ 59
def prefixEnd_3253352 : Nat := 4983230072969 + 3 ^ 40 * 3253352 * 2
def baseEnd_3253352 : Nat := 1670533314266260479038113

theorem tailTrace_3253352 : CollatzResearch.WordTrace tailWord_3253352 prefixEnd_3253352 1670533314266260479038113 := by
  unfold tailWord_3253352
  simp only [CollatzResearch.WordTrace]
  refine ⟨59329747854834403565441155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79106330473112538087254873 59329747854834403565441155)
  ·
    refine ⟨88994621782251605348161733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59329747854834403565441155 88994621782251605348161733)
    ·
      refine ⟨16686491584172176002780325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88994621782251605348161733 16686491584172176002780325)
      ·
        refine ⟨3128717172032283000521311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16686491584172176002780325 3128717172032283000521311)
        ·
          refine ⟨4693075758048424500781967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3128717172032283000521311 4693075758048424500781967)
          ·
            refine ⟨7039613637072636751172951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4693075758048424500781967 7039613637072636751172951)
            ·
              refine ⟨10559420455608955126759427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7039613637072636751172951 10559420455608955126759427)
              ·
                refine ⟨15839130683413432690139141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10559420455608955126759427 15839130683413432690139141)
                ·
                  refine ⟨2969837003140018629401089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15839130683413432690139141 2969837003140018629401089)
                  ·
                    refine ⟨2227377752355013972050817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2969837003140018629401089 2227377752355013972050817)
                    ·
                      refine ⟨1670533314266260479038113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2227377752355013972050817 1670533314266260479038113)
                      ·
                        rfl

theorem cell23_3253352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_3253352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253352 prefixEnd_3253352 := by exact prefixLift 3253352
  have htrace : WordTrace (prefixWord ++ tailWord_3253352) baseStart_3253352 baseEnd_3253352 := by
    simpa [prefixWord, tailWord_3253352, baseEnd_3253352] using wordTrace_append hprefix tailTrace_3253352
  have hstable : (prefixWord ++ tailWord_3253352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253352).length < 2 ^ (prefixWord ++ tailWord_3253352).sum := by decide
  have hdescent : baseEnd_3253352 < baseStart_3253352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253358 : List Nat := [4, 1, 2, 2, 1, 2, 2, 4, 5]
def baseStart_3253358 : Nat := 118140960795 + 3253358 * 2 ^ 59
def prefixEnd_3253358 : Nat := 4983230072969 + 3 ^ 40 * 3253358 * 2
def baseEnd_3253358 : Nat := 185615155016687495062565

theorem tailTrace_3253358 : CollatzResearch.WordTrace tailWord_3253358 prefixEnd_3253358 185615155016687495062565 := by
  unfold tailWord_3253358
  simp only [CollatzResearch.WordTrace]
  refine ⟨14832464318455883769450091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79106476365098046770400485 14832464318455883769450091)
  ·
    refine ⟨22248696477683825654175137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14832464318455883769450091 22248696477683825654175137)
    ·
      refine ⟨16686522358262869240631353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22248696477683825654175137 16686522358262869240631353)
      ·
        refine ⟨12514891768697151930473515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16686522358262869240631353 12514891768697151930473515)
        ·
          refine ⟨18772337653045727895710273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12514891768697151930473515 18772337653045727895710273)
          ·
            refine ⟨14079253239784295921782705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18772337653045727895710273 14079253239784295921782705)
            ·
              refine ⟨10559439929838221941337029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14079253239784295921782705 10559439929838221941337029)
              ·
                refine ⟨1979894986844666614000693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10559439929838221941337029 1979894986844666614000693)
                ·
                  refine ⟨185615155016687495062565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1979894986844666614000693 185615155016687495062565)
                  ·
                    rfl

theorem cell23_3253358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_3253358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253358 prefixEnd_3253358 := by exact prefixLift 3253358
  have htrace : WordTrace (prefixWord ++ tailWord_3253358) baseStart_3253358 baseEnd_3253358 := by
    simpa [prefixWord, tailWord_3253358, baseEnd_3253358] using wordTrace_append hprefix tailTrace_3253358
  have hstable : (prefixWord ++ tailWord_3253358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253358).length < 2 ^ (prefixWord ++ tailWord_3253358).sum := by decide
  have hdescent : baseEnd_3253358 < baseStart_3253358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253361 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 2, 5, 2]
def baseStart_3253361 : Nat := 118140960795 + 3253361 * 2 ^ 59
def prefixEnd_3253361 : Nat := 4983230072969 + 3 ^ 40 * 3253361 * 2
def baseEnd_3253361 : Nat := 1670537935592150943825571

theorem tailTrace_3253361 : CollatzResearch.WordTrace tailWord_3253361 prefixEnd_3253361 1670537935592150943825571 := by
  unfold tailWord_3253361
  simp only [CollatzResearch.WordTrace]
  refine ⟨118659823966636201667959937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79106549311090801111973291 118659823966636201667959937)
  ·
    refine ⟨88994867974977151250969953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118659823966636201667959937 88994867974977151250969953)
    ·
      refine ⟨66746150981232863438227465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88994867974977151250969953 66746150981232863438227465)
      ·
        refine ⟨50059613235924647578670599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66746150981232863438227465 50059613235924647578670599)
        ·
          refine ⟨75089419853886971368005899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50059613235924647578670599 75089419853886971368005899)
          ·
            refine ⟨112634129780830457052008849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75089419853886971368005899 112634129780830457052008849)
            ·
              refine ⟨84475597335622842789006637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112634129780830457052008849 84475597335622842789006637)
              ·
                refine ⟨31678349000858566045877489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84475597335622842789006637 31678349000858566045877489)
                ·
                  refine ⟨23758761750643924534408117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31678349000858566045877489 23758761750643924534408117)
                  ·
                    refine ⟨2227383914122867925100761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23758761750643924534408117 2227383914122867925100761)
                    ·
                      refine ⟨1670537935592150943825571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2227383914122867925100761 1670537935592150943825571)
                      ·
                        rfl

theorem cell23_3253361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 5, 2].length) (baseStart_3253361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253361 prefixEnd_3253361 := by exact prefixLift 3253361
  have htrace : WordTrace (prefixWord ++ tailWord_3253361) baseStart_3253361 baseEnd_3253361 := by
    simpa [prefixWord, tailWord_3253361, baseEnd_3253361] using wordTrace_append hprefix tailTrace_3253361
  have hstable : (prefixWord ++ tailWord_3253361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253361).length < 2 ^ (prefixWord ++ tailWord_3253361).sum := by decide
  have hdescent : baseEnd_3253361 < baseStart_3253361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253431 : List Nat := [1, 1, 3, 1, 4, 1, 3, 3, 6]
def baseStart_3253431 : Nat := 118140960795 + 3253431 * 2 ^ 59
def prefixEnd_3253431 : Nat := 4983230072969 + 3 ^ 40 * 3253431 * 2
def baseEnd_3253431 : Nat := 185619319915329518883361

theorem tailTrace_3253431 : CollatzResearch.WordTrace tailWord_3253431 prefixEnd_3253431 185619319915329518883361 := by
  unfold tailWord_3253431
  simp only [CollatzResearch.WordTrace]
  refine ⟨118662377076382603623008147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79108251384255069082005431 118662377076382603623008147)
  ·
    refine ⟨177993565614573905434512221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118662377076382603623008147 177993565614573905434512221)
    ·
      refine ⟨66747587105465214537942083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177993565614573905434512221 66747587105465214537942083)
      ·
        refine ⟨100121380658197821806913125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66747587105465214537942083 100121380658197821806913125)
        ·
          refine ⟨18772758873412091588796211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100121380658197821806913125 18772758873412091588796211)
          ·
            refine ⟨28159138310118137383194317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18772758873412091588796211 28159138310118137383194317)
            ·
              refine ⟨10559676866294301518697869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28159138310118137383194317 10559676866294301518697869)
              ·
                refine ⟨3959878824860363069511701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10559676866294301518697869 3959878824860363069511701)
                ·
                  refine ⟨185619319915329518883361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3959878824860363069511701 185619319915329518883361)
                  ·
                    rfl

theorem cell23_3253431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 6].length) (baseStart_3253431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253431 prefixEnd_3253431 := by exact prefixLift 3253431
  have htrace : WordTrace (prefixWord ++ tailWord_3253431) baseStart_3253431 baseEnd_3253431 := by
    simpa [prefixWord, tailWord_3253431, baseEnd_3253431] using wordTrace_append hprefix tailTrace_3253431
  have hstable : (prefixWord ++ tailWord_3253431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253431).length < 2 ^ (prefixWord ++ tailWord_3253431).sum := by decide
  have hdescent : baseEnd_3253431 < baseStart_3253431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253491 : List Nat := [1, 1, 1, 2, 2, 5, 1, 3, 1, 6]
def baseStart_3253491 : Nat := 118140960795 + 3253491 * 2 ^ 59
def prefixEnd_3253491 : Nat := 4983230072969 + 3 ^ 40 * 3253491 * 2
def baseEnd_3253491 : Nat := 556868229359078478399991

theorem tailTrace_3253491 : CollatzResearch.WordTrace tailWord_3253491 prefixEnd_3253491 556868229359078478399991 := by
  unfold tailWord_3253491
  simp only [CollatzResearch.WordTrace]
  refine ⟨118664565456165233870192327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79109710304110155913461551 118664565456165233870192327)
  ·
    refine ⟨177996848184247850805288491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118664565456165233870192327 177996848184247850805288491)
    ·
      refine ⟨266995272276371776207932737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177996848184247850805288491 266995272276371776207932737)
      ·
        refine ⟨200246454207278832155949553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266995272276371776207932737 200246454207278832155949553)
        ·
          refine ⟨150184840655459124116962165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200246454207278832155949553 150184840655459124116962165)
          ·
            refine ⟨14079828811449292885965203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150184840655459124116962165 14079828811449292885965203)
            ·
              refine ⟨21119743217173939328947805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14079828811449292885965203 21119743217173939328947805)
              ·
                refine ⟨7919903706440227248355427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21119743217173939328947805 7919903706440227248355427)
                ·
                  refine ⟨11879855559660340872533141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7919903706440227248355427 11879855559660340872533141)
                  ·
                    refine ⟨556868229359078478399991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11879855559660340872533141 556868229359078478399991)
                    ·
                      rfl

theorem cell23_3253491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 6].length) (baseStart_3253491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253491 prefixEnd_3253491 := by exact prefixLift 3253491
  have htrace : WordTrace (prefixWord ++ tailWord_3253491) baseStart_3253491 baseEnd_3253491 := by
    simpa [prefixWord, tailWord_3253491, baseEnd_3253491] using wordTrace_append hprefix tailTrace_3253491
  have hstable : (prefixWord ++ tailWord_3253491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253491).length < 2 ^ (prefixWord ++ tailWord_3253491).sum := by decide
  have hdescent : baseEnd_3253491 < baseStart_3253491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253498 : List Nat := [3, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4]
def baseStart_3253498 : Nat := 118140960795 + 3253498 * 2 ^ 59
def prefixEnd_3253498 : Nat := 4983230072969 + 3 ^ 40 * 3253498 * 2
def baseEnd_3253498 : Nat := 1670608282441816907812441

theorem tailTrace_3253498 : CollatzResearch.WordTrace tailWord_3253498 prefixEnd_3253498 1670608282441816907812441 := by
  unfold tailWord_3253498
  simp only [CollatzResearch.WordTrace]
  refine ⟨29666205191784968516424287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79109880511426582710464765 29666205191784968516424287)
  ·
    refine ⟨44499307787677452774636431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29666205191784968516424287 44499307787677452774636431)
    ·
      refine ⟨66748961681516179161954647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44499307787677452774636431 66748961681516179161954647)
      ·
        refine ⟨100123442522274268742931971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66748961681516179161954647 100123442522274268742931971)
        ·
          refine ⟨150185163783411403114397957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100123442522274268742931971 150185163783411403114397957)
          ·
            refine ⟨28159718209389638083949617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150185163783411403114397957 28159718209389638083949617)
            ·
              refine ⟨21119788657042228562962213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28159718209389638083949617 21119788657042228562962213)
              ·
                refine ⟨3959960373195417855555415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21119788657042228562962213 3959960373195417855555415)
                ·
                  refine ⟨5939940559793126783333123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3959960373195417855555415 5939940559793126783333123)
                  ·
                    refine ⟨8909910839689690174999685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5939940559793126783333123 8909910839689690174999685)
                    ·
                      refine ⟨1670608282441816907812441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8909910839689690174999685 1670608282441816907812441)
                      ·
                        rfl

theorem cell23_3253498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4].length) (baseStart_3253498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253498 prefixEnd_3253498 := by exact prefixLift 3253498
  have htrace : WordTrace (prefixWord ++ tailWord_3253498) baseStart_3253498 baseEnd_3253498 := by
    simpa [prefixWord, tailWord_3253498, baseEnd_3253498] using wordTrace_append hprefix tailTrace_3253498
  have hstable : (prefixWord ++ tailWord_3253498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253498).length < 2 ^ (prefixWord ++ tailWord_3253498).sum := by decide
  have hdescent : baseEnd_3253498 < baseStart_3253498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253502 : List Nat := [4, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2]
def baseStart_3253502 : Nat := 118140960795 + 3253502 * 2 ^ 59
def prefixEnd_3253502 : Nat := 4983230072969 + 3 ^ 40 * 3253502 * 2
def baseEnd_3253502 : Nat := 1670610336364434892162423

theorem tailTrace_3253502 : CollatzResearch.WordTrace tailWord_3253502 prefixEnd_3253502 1670610336364434892162423 := by
  unfold tailWord_3253502
  simp only [CollatzResearch.WordTrace]
  refine ⟨14833120832390672843605345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79109977772750255165895173 14833120832390672843605345)
  ·
    refine ⟨11124840624293004632704009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14833120832390672843605345 11124840624293004632704009)
    ·
      refine ⟨8343630468219753474528007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11124840624293004632704009 8343630468219753474528007)
      ·
        refine ⟨12515445702329630211792011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8343630468219753474528007 12515445702329630211792011)
        ·
          refine ⟨18773168553494445317688017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12515445702329630211792011 18773168553494445317688017)
          ·
            refine ⟨14079876415120833988266013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18773168553494445317688017 14079876415120833988266013)
            ·
              refine ⟨5279953655670312745599755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14079876415120833988266013 5279953655670312745599755)
              ·
                refine ⟨7919930483505469118399633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5279953655670312745599755 7919930483505469118399633)
                ·
                  refine ⟨5939947862629101838799725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7919930483505469118399633 5939947862629101838799725)
                  ·
                    refine ⟨2227480448485913189549897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5939947862629101838799725 2227480448485913189549897)
                    ·
                      refine ⟨1670610336364434892162423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2227480448485913189549897 1670610336364434892162423)
                      ·
                        rfl

theorem cell23_3253502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_3253502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253502 prefixEnd_3253502 := by exact prefixLift 3253502
  have htrace : WordTrace (prefixWord ++ tailWord_3253502) baseStart_3253502 baseEnd_3253502 := by
    simpa [prefixWord, tailWord_3253502, baseEnd_3253502] using wordTrace_append hprefix tailTrace_3253502
  have hstable : (prefixWord ++ tailWord_3253502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253502).length < 2 ^ (prefixWord ++ tailWord_3253502).sum := by decide
  have hdescent : baseEnd_3253502 < baseStart_3253502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253508 : List Nat := [2, 3, 2, 2, 2, 1, 2, 2, 1, 6]
def baseStart_3253508 : Nat := 118140960795 + 3253508 * 2 ^ 59
def prefixEnd_3253508 : Nat := 4983230072969 + 3 ^ 40 * 3253508 * 2
def baseEnd_3253508 : Nat := 556871139082787289562465

theorem tailTrace_3253508 : CollatzResearch.WordTrace tailWord_3253508 prefixEnd_3253508 556871139082787289562465 := by
  unfold tailWord_3253508
  simp only [CollatzResearch.WordTrace]
  refine ⟨59332592748551822886780589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79110123664735763849040785 59332592748551822886780589)
  ·
    refine ⟨22249722280706933582542721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59332592748551822886780589 22249722280706933582542721)
    ·
      refine ⟨16687291710530200186907041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22249722280706933582542721 16687291710530200186907041)
      ·
        refine ⟨12515468782897650140180281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16687291710530200186907041 12515468782897650140180281)
        ·
          refine ⟨9386601587173237605135211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12515468782897650140180281 9386601587173237605135211)
          ·
            refine ⟨14079902380759856407702817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9386601587173237605135211 14079902380759856407702817)
            ·
              refine ⟨10559926785569892305777113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14079902380759856407702817 10559926785569892305777113)
              ·
                refine ⟨7919945089177419229332835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10559926785569892305777113 7919945089177419229332835)
                ·
                  refine ⟨11879917633766128843999253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7919945089177419229332835 11879917633766128843999253)
                  ·
                    refine ⟨556871139082787289562465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11879917633766128843999253 556871139082787289562465)
                    ·
                      rfl

theorem cell23_3253508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_3253508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253508 prefixEnd_3253508 := by exact prefixLift 3253508
  have htrace : WordTrace (prefixWord ++ tailWord_3253508) baseStart_3253508 baseEnd_3253508 := by
    simpa [prefixWord, tailWord_3253508, baseEnd_3253508] using wordTrace_append hprefix tailTrace_3253508
  have hstable : (prefixWord ++ tailWord_3253508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253508).length < 2 ^ (prefixWord ++ tailWord_3253508).sum := by decide
  have hdescent : baseEnd_3253508 < baseStart_3253508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253512 : List Nat := [2, 1, 3, 2, 4, 2, 2, 1, 1, 5]
def baseStart_3253512 : Nat := 118140960795 + 3253512 * 2 ^ 59
def prefixEnd_3253512 : Nat := 4983230072969 + 3 ^ 40 * 3253512 * 2
def baseEnd_3253512 : Nat := 556871823723659951012459

theorem tailTrace_3253512 : CollatzResearch.WordTrace tailWord_3253512 prefixEnd_3253512 556871823723659951012459 := by
  unfold tailWord_3253512
  simp only [CollatzResearch.WordTrace]
  refine ⟨59332665694544577228353395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79110220926059436304471193 59332665694544577228353395)
  ·
    refine ⟨88998998541816865842530093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59332665694544577228353395 88998998541816865842530093)
    ·
      refine ⟨33374624453181324690948785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88998998541816865842530093 33374624453181324690948785)
      ·
        refine ⟨25030968339885993518211589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33374624453181324690948785 25030968339885993518211589)
        ·
          refine ⟨4693306563728623784664673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25030968339885993518211589 4693306563728623784664673)
          ·
            refine ⟨3519979922796467838498505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4693306563728623784664673 3519979922796467838498505)
            ·
              refine ⟨2639984942097350878873879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3519979922796467838498505 2639984942097350878873879)
              ·
                refine ⟨3959977413146026318310819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2639984942097350878873879 3959977413146026318310819)
                ·
                  refine ⟨5939966119719039477466229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3959977413146026318310819 5939966119719039477466229)
                  ·
                    refine ⟨556871823723659951012459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5939966119719039477466229 556871823723659951012459)
                    ·
                      rfl

theorem cell23_3253512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_3253512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253512 prefixEnd_3253512 := by exact prefixLift 3253512
  have htrace : WordTrace (prefixWord ++ tailWord_3253512) baseStart_3253512 baseEnd_3253512 := by
    simpa [prefixWord, tailWord_3253512, baseEnd_3253512] using wordTrace_append hprefix tailTrace_3253512
  have hstable : (prefixWord ++ tailWord_3253512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253512).length < 2 ^ (prefixWord ++ tailWord_3253512).sum := by decide
  have hdescent : baseEnd_3253512 < baseStart_3253512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253515 : List Nat := [1, 1, 1, 1, 5, 3, 4, 1, 1, 1, 4]
def baseStart_3253515 : Nat := 118140960795 + 3253515 * 2 ^ 59
def prefixEnd_3253515 : Nat := 4983230072969 + 3 ^ 40 * 3253515 * 2
def baseEnd_3253515 : Nat := 1670617011612943341299863

theorem tailTrace_3253515 : CollatzResearch.WordTrace tailWord_3253515 prefixEnd_3253515 1670617011612943341299863 := by
  unfold tailWord_3253515
  simp only [CollatzResearch.WordTrace]
  refine ⟨118665440808078285969065999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79110293872052190646043999 118665440808078285969065999)
  ·
    refine ⟨177998161212117428953598999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118665440808078285969065999 177998161212117428953598999)
    ·
      refine ⟨266997241818176143430398499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177998161212117428953598999 266997241818176143430398499)
      ·
        refine ⟨400495862727264215145597749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266997241818176143430398499 400495862727264215145597749)
        ·
          refine ⟨37546487130681020169899789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 400495862727264215145597749 37546487130681020169899789)
          ·
            refine ⟨14079932674005382563712421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37546487130681020169899789 14079932674005382563712421)
            ·
              refine ⟨2639987376376009230696079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14079932674005382563712421 2639987376376009230696079)
              ·
                refine ⟨3959981064564013846044119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2639987376376009230696079 3959981064564013846044119)
                ·
                  refine ⟨5939971596846020769066179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3959981064564013846044119 5939971596846020769066179)
                  ·
                    refine ⟨8909957395269031153599269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5939971596846020769066179 8909957395269031153599269)
                    ·
                      refine ⟨1670617011612943341299863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8909957395269031153599269 1670617011612943341299863)
                      ·
                        rfl

theorem cell23_3253515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 1, 1, 4].length) (baseStart_3253515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253515 prefixEnd_3253515 := by exact prefixLift 3253515
  have htrace : WordTrace (prefixWord ++ tailWord_3253515) baseStart_3253515 baseEnd_3253515 := by
    simpa [prefixWord, tailWord_3253515, baseEnd_3253515] using wordTrace_append hprefix tailTrace_3253515
  have hstable : (prefixWord ++ tailWord_3253515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253515).length < 2 ^ (prefixWord ++ tailWord_3253515).sum := by decide
  have hdescent : baseEnd_3253515 < baseStart_3253515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253549 : List Nat := [1, 5, 3, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_3253549 : Nat := 118140960795 + 3253549 * 2 ^ 59
def prefixEnd_3253549 : Nat := 4983230072969 + 3 ^ 40 * 3253549 * 2
def baseEnd_3253549 : Nat := 1670634469955196208274707

theorem tailTrace_3253549 : CollatzResearch.WordTrace tailWord_3253549 prefixEnd_3253549 1670634469955196208274707 := by
  unfold tailWord_3253549
  simp only [CollatzResearch.WordTrace]
  refine ⟨118666680889955109775803701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79111120593303406517202467 118666680889955109775803701)
  ·
    refine ⟨11125001333433291541481597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118666680889955109775803701 11125001333433291541481597)
    ·
      refine ⟨4171875500037484328055599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11125001333433291541481597 4171875500037484328055599)
      ·
        refine ⟨6257813250056226492083399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4171875500037484328055599 6257813250056226492083399)
        ·
          refine ⟨9386719875084339738125099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6257813250056226492083399 9386719875084339738125099)
          ·
            refine ⟨14080079812626509607187649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9386719875084339738125099 14080079812626509607187649)
            ·
              refine ⟨10560059859469882205390737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14080079812626509607187649 10560059859469882205390737)
              ·
                refine ⟨7920044894602411654043053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10560059859469882205390737 7920044894602411654043053)
                ·
                  refine ⟨2970016835475904370266145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7920044894602411654043053 2970016835475904370266145)
                  ·
                    refine ⟨2227512626606928277699609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2970016835475904370266145 2227512626606928277699609)
                    ·
                      refine ⟨1670634469955196208274707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2227512626606928277699609 1670634469955196208274707)
                      ·
                        rfl

theorem cell23_3253549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_3253549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253549 prefixEnd_3253549 := by exact prefixLift 3253549
  have htrace : WordTrace (prefixWord ++ tailWord_3253549) baseStart_3253549 baseEnd_3253549 := by
    simpa [prefixWord, tailWord_3253549, baseEnd_3253549] using wordTrace_append hprefix tailTrace_3253549
  have hstable : (prefixWord ++ tailWord_3253549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253549).length < 2 ^ (prefixWord ++ tailWord_3253549).sum := by decide
  have hdescent : baseEnd_3253549 < baseStart_3253549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253571 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 4]
def baseStart_3253571 : Nat := 118140960795 + 3253571 * 2 ^ 59
def prefixEnd_3253571 : Nat := 4983230072969 + 3 ^ 40 * 3253571 * 2
def baseEnd_3253571 : Nat := 1670645766529595122199605

theorem tailTrace_3253571 : CollatzResearch.WordTrace tailWord_3253571 prefixEnd_3253571 1670645766529595122199605 := by
  unfold tailWord_3253571
  simp only [CollatzResearch.WordTrace]
  refine ⟨118667483295875407533104567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79111655530583605022069711 118667483295875407533104567)
  ·
    refine ⟨178001224943813111299656851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118667483295875407533104567 178001224943813111299656851)
    ·
      refine ⟨267001837415719666949485277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178001224943813111299656851 267001837415719666949485277)
      ·
        refine ⟨100125689030894875106056979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267001837415719666949485277 100125689030894875106056979)
        ·
          refine ⟨150188533546342312659085469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100125689030894875106056979 150188533546342312659085469)
          ·
            refine ⟨56320700079878367247157051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150188533546342312659085469 56320700079878367247157051)
            ·
              refine ⟨84481050119817550870735577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56320700079878367247157051 84481050119817550870735577)
              ·
                refine ⟨63360787589863163153051683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84481050119817550870735577 63360787589863163153051683)
                ·
                  refine ⟨95041181384794744729577525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63360787589863163153051683 95041181384794744729577525)
                  ·
                    refine ⟨8910110754824507318397893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95041181384794744729577525 8910110754824507318397893)
                    ·
                      refine ⟨1670645766529595122199605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8910110754824507318397893 1670645766529595122199605)
                      ·
                        rfl

theorem cell23_3253571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_3253571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253571 prefixEnd_3253571 := by exact prefixLift 3253571
  have htrace : WordTrace (prefixWord ++ tailWord_3253571) baseStart_3253571 baseEnd_3253571 := by
    simpa [prefixWord, tailWord_3253571, baseEnd_3253571] using wordTrace_append hprefix tailTrace_3253571
  have hstable : (prefixWord ++ tailWord_3253571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253571).length < 2 ^ (prefixWord ++ tailWord_3253571).sum := by decide
  have hdescent : baseEnd_3253571 < baseStart_3253571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253588 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_3253588 : Nat := 118140960795 + 3253588 * 2 ^ 59
def prefixEnd_3253588 : Nat := 4983230072969 + 3 ^ 40 * 3253588 * 2
def baseEnd_3253588 : Nat := 1670654495700721555687027

theorem tailTrace_3253588 : CollatzResearch.WordTrace tailWord_3253588 prefixEnd_3253588 1670654495700721555687027 := by
  unfold tailWord_3253588
  simp only [CollatzResearch.WordTrace]
  refine ⟨59334051668406909718236709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79112068891209212957648945 59334051668406909718236709)
  ·
    refine ⟨11125134687826295572169383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59334051668406909718236709 11125134687826295572169383)
    ·
      refine ⟨16687702031739443358254075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11125134687826295572169383 16687702031739443358254075)
      ·
        refine ⟨25031553047609165037381113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16687702031739443358254075 25031553047609165037381113)
        ·
          refine ⟨18773664785706873778035835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25031553047609165037381113 18773664785706873778035835)
          ·
            refine ⟨28160497178560310667053753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18773664785706873778035835 28160497178560310667053753)
            ·
              refine ⟨21120372883920233000290315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28160497178560310667053753 21120372883920233000290315)
              ·
                refine ⟨31680559325880349500435473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21120372883920233000290315 31680559325880349500435473)
                ·
                  refine ⟨23760419494410262125326605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31680559325880349500435473 23760419494410262125326605)
                  ·
                    refine ⟨8910157310403848296997477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23760419494410262125326605 8910157310403848296997477)
                    ·
                      refine ⟨1670654495700721555687027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8910157310403848296997477 1670654495700721555687027)
                      ·
                        rfl

theorem cell23_3253588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_3253588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253588 prefixEnd_3253588 := by exact prefixLift 3253588
  have htrace : WordTrace (prefixWord ++ tailWord_3253588) baseStart_3253588 baseEnd_3253588 := by
    simpa [prefixWord, tailWord_3253588, baseEnd_3253588] using wordTrace_append hprefix tailTrace_3253588
  have hstable : (prefixWord ++ tailWord_3253588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253588).length < 2 ^ (prefixWord ++ tailWord_3253588).sum := by decide
  have hdescent : baseEnd_3253588 < baseStart_3253588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253601 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 2, 3, 6]
def baseStart_3253601 : Nat := 118140960795 + 3253601 * 2 ^ 59
def prefixEnd_3253601 : Nat := 4983230072969 + 3 ^ 40 * 3253601 * 2
def baseEnd_3253601 : Nat := 1670661170949230004824467

theorem tailTrace_3253601 : CollatzResearch.WordTrace tailWord_3253601 prefixEnd_3253601 1670661170949230004824467 := by
  unfold tailWord_3253601
  simp only [CollatzResearch.WordTrace]
  refine ⟨118668577485766722656696657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79112384990511148437797771 118668577485766722656696657)
  ·
    refine ⟨89001433114325041992522493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118668577485766722656696657 89001433114325041992522493)
    ·
      refine ⟨33375537417871890747195935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89001433114325041992522493 33375537417871890747195935)
      ·
        refine ⟨50063306126807836120793903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33375537417871890747195935 50063306126807836120793903)
        ·
          refine ⟨75094959190211754181190855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50063306126807836120793903 75094959190211754181190855)
          ·
            refine ⟨112642438785317631271786283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75094959190211754181190855 112642438785317631271786283)
            ·
              refine ⟨168963658177976446907679425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112642438785317631271786283 168963658177976446907679425)
              ·
                refine ⟨126722743633482335180759569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168963658177976446907679425 126722743633482335180759569)
                ·
                  refine ⟨95042057725111751385569677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126722743633482335180759569 95042057725111751385569677)
                  ·
                    refine ⟨35640771646916906769588629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95042057725111751385569677 35640771646916906769588629)
                    ·
                      refine ⟨1670661170949230004824467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35640771646916906769588629 1670661170949230004824467)
                      ·
                        rfl

theorem cell23_3253601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_3253601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253601 prefixEnd_3253601 := by exact prefixLift 3253601
  have htrace : WordTrace (prefixWord ++ tailWord_3253601) baseStart_3253601 baseEnd_3253601 := by
    simpa [prefixWord, tailWord_3253601, baseEnd_3253601] using wordTrace_append hprefix tailTrace_3253601
  have hstable : (prefixWord ++ tailWord_3253601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253601).length < 2 ^ (prefixWord ++ tailWord_3253601).sum := by decide
  have hdescent : baseEnd_3253601 < baseStart_3253601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253605 : List Nat := [1, 3, 1, 3, 1, 2, 2, 3, 1, 4, 2]
def baseStart_3253605 : Nat := 118140960795 + 3253605 * 2 ^ 59
def prefixEnd_3253605 : Nat := 4983230072969 + 3 ^ 40 * 3253605 * 2
def baseEnd_3253605 : Nat := 1670663224871847989174449

theorem tailTrace_3253605 : CollatzResearch.WordTrace tailWord_3253605 prefixEnd_3253605 1670663224871847989174449 := by
  unfold tailWord_3253605
  simp only [CollatzResearch.WordTrace]
  refine ⟨118668723377752231339842269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79112482251834820893228179 118668723377752231339842269)
  ·
    refine ⟨44500771266657086752440851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118668723377752231339842269 44500771266657086752440851)
    ·
      refine ⟨66751156899985630128661277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44500771266657086752440851 66751156899985630128661277)
      ·
        refine ⟨25031683837494611298247979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66751156899985630128661277 25031683837494611298247979)
        ·
          refine ⟨37547525756241916947371969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25031683837494611298247979 37547525756241916947371969)
          ·
            refine ⟨28160644317181437710528977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37547525756241916947371969 28160644317181437710528977)
            ·
              refine ⟨21120483237886078282896733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28160644317181437710528977 21120483237886078282896733)
              ·
                refine ⟨7920181214207279356086275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21120483237886078282896733 7920181214207279356086275)
                ·
                  refine ⟨11880271821310919034129413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7920181214207279356086275 11880271821310919034129413)
                  ·
                    refine ⟨2227550966495797318899265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11880271821310919034129413 2227550966495797318899265)
                    ·
                      refine ⟨1670663224871847989174449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2227550966495797318899265 1670663224871847989174449)
                      ·
                        rfl

theorem cell23_3253605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_3253605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253605 prefixEnd_3253605 := by exact prefixLift 3253605
  have htrace : WordTrace (prefixWord ++ tailWord_3253605) baseStart_3253605 baseEnd_3253605 := by
    simpa [prefixWord, tailWord_3253605, baseEnd_3253605] using wordTrace_append hprefix tailTrace_3253605
  have hstable : (prefixWord ++ tailWord_3253605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253605).length < 2 ^ (prefixWord ++ tailWord_3253605).sum := by decide
  have hdescent : baseEnd_3253605 < baseStart_3253605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253631 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 6]
def baseStart_3253631 : Nat := 118140960795 + 3253631 * 2 ^ 59
def prefixEnd_3253631 : Nat := 4983230072969 + 3 ^ 40 * 3253631 * 2
def baseEnd_3253631 : Nat := 1670676575368864887449329

theorem tailTrace_3253631 : CollatzResearch.WordTrace tailWord_3253631 prefixEnd_3253631 1670676575368864887449329 := by
  unfold tailWord_3253631
  simp only [CollatzResearch.WordTrace]
  refine ⟨118669671675658037780288747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79113114450438691853525831 118669671675658037780288747)
  ·
    refine ⟨178004507513487056670433121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118669671675658037780288747 178004507513487056670433121)
    ·
      refine ⟨133503380635115292502824841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178004507513487056670433121 133503380635115292502824841)
      ·
        refine ⟨100127535476336469377118631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133503380635115292502824841 100127535476336469377118631)
        ·
          refine ⟨150191303214504704065677947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100127535476336469377118631 150191303214504704065677947)
          ·
            refine ⟨225286954821757056098516921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150191303214504704065677947 225286954821757056098516921)
            ·
              refine ⟨168965216116317792073887691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225286954821757056098516921 168965216116317792073887691)
              ·
                refine ⟨253447824174476688110831537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168965216116317792073887691 253447824174476688110831537)
                ·
                  refine ⟨190085868130857516083123653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253447824174476688110831537 190085868130857516083123653)
                  ·
                    refine ⟨35641100274535784265585685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 190085868130857516083123653 35641100274535784265585685)
                    ·
                      refine ⟨1670676575368864887449329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35641100274535784265585685 1670676575368864887449329)
                      ·
                        rfl

theorem cell23_3253631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_3253631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253631 prefixEnd_3253631 := by exact prefixLift 3253631
  have htrace : WordTrace (prefixWord ++ tailWord_3253631) baseStart_3253631 baseEnd_3253631 := by
    simpa [prefixWord, tailWord_3253631, baseEnd_3253631] using wordTrace_append hprefix tailTrace_3253631
  have hstable : (prefixWord ++ tailWord_3253631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253631).length < 2 ^ (prefixWord ++ tailWord_3253631).sum := by decide
  have hdescent : baseEnd_3253631 < baseStart_3253631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253639 : List Nat := [1, 1, 4, 2, 2, 3, 2, 2, 2, 2, 2]
def baseStart_3253639 : Nat := 118140960795 + 3253639 * 2 ^ 59
def prefixEnd_3253639 : Nat := 4983230072969 + 3 ^ 40 * 3253639 * 2
def baseEnd_3253639 : Nat := 1670680683214100856149293

theorem tailTrace_3253639 : CollatzResearch.WordTrace tailWord_3253639 prefixEnd_3253639 1670680683214100856149293 := by
  unfold tailWord_3253639
  simp only [CollatzResearch.WordTrace]
  refine ⟨118669963459629055146579971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79113308973086036764386647 118669963459629055146579971)
  ·
    refine ⟨178004945189443582719869957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118669963459629055146579971 178004945189443582719869957)
    ·
      refine ⟨33375927223020671759975617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178004945189443582719869957 33375927223020671759975617)
      ·
        refine ⟨25031945417265503819981713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33375927223020671759975617 25031945417265503819981713)
        ·
          refine ⟨18773959062949127864986285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25031945417265503819981713 18773959062949127864986285)
          ·
            refine ⟨7040234648605922949369857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18773959062949127864986285 7040234648605922949369857)
            ·
              refine ⟨5280175986454442212027393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7040234648605922949369857 5280175986454442212027393)
              ·
                refine ⟨3960131989840831659020545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5280175986454442212027393 3960131989840831659020545)
                ·
                  refine ⟨2970098992380623744265409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3960131989840831659020545 2970098992380623744265409)
                  ·
                    refine ⟨2227574244285467808199057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2970098992380623744265409 2227574244285467808199057)
                    ·
                      refine ⟨1670680683214100856149293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2227574244285467808199057 1670680683214100856149293)
                      ·
                        rfl

theorem cell23_3253639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_3253639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253639 prefixEnd_3253639 := by exact prefixLift 3253639
  have htrace : WordTrace (prefixWord ++ tailWord_3253639) baseStart_3253639 baseEnd_3253639 := by
    simpa [prefixWord, tailWord_3253639, baseEnd_3253639] using wordTrace_append hprefix tailTrace_3253639
  have hstable : (prefixWord ++ tailWord_3253639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253639).length < 2 ^ (prefixWord ++ tailWord_3253639).sum := by decide
  have hdescent : baseEnd_3253639 < baseStart_3253639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253658 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 1, 7]
def baseStart_3253658 : Nat := 118140960795 + 3253658 * 2 ^ 59
def prefixEnd_3253658 : Nat := 4983230072969 + 3 ^ 40 * 3253658 * 2
def baseEnd_3253658 : Nat := 556896813115512093937235

theorem tailTrace_3253658 : CollatzResearch.WordTrace tailWord_3253658 prefixEnd_3253658 556896813115512093937235 := by
  unfold tailWord_3253658
  simp only [CollatzResearch.WordTrace]
  refine ⟨29667664111640055347880407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79113770964373480927681085 29667664111640055347880407)
  ·
    refine ⟨44501496167460083021820611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29667664111640055347880407 44501496167460083021820611)
    ·
      refine ⟨66752244251190124532730917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44501496167460083021820611 66752244251190124532730917)
      ·
        refine ⟨12516045797098148349887047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66752244251190124532730917 12516045797098148349887047)
        ·
          refine ⟨18774068695647222524830571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12516045797098148349887047 18774068695647222524830571)
          ·
            refine ⟨28161103043470833787245857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18774068695647222524830571 28161103043470833787245857)
            ·
              refine ⟨21120827282603125340434393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28161103043470833787245857 21120827282603125340434393)
              ·
                refine ⟨15840620461952344005325795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21120827282603125340434393 15840620461952344005325795)
                ·
                  refine ⟨23760930692928516007988693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15840620461952344005325795 23760930692928516007988693)
                  ·
                    refine ⟨556896813115512093937235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23760930692928516007988693 556896813115512093937235)
                    ·
                      rfl

theorem cell23_3253658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_3253658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253658 prefixEnd_3253658 := by exact prefixLift 3253658
  have htrace : WordTrace (prefixWord ++ tailWord_3253658) baseStart_3253658 baseEnd_3253658 := by
    simpa [prefixWord, tailWord_3253658, baseEnd_3253658] using wordTrace_append hprefix tailTrace_3253658
  have hstable : (prefixWord ++ tailWord_3253658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253658).length < 2 ^ (prefixWord ++ tailWord_3253658).sum := by decide
  have hdescent : baseEnd_3253658 < baseStart_3253658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253662 : List Nat := [4, 3, 1, 2, 2, 1, 1, 2, 7]
def baseStart_3253662 : Nat := 118140960795 + 3253662 * 2 ^ 59
def prefixEnd_3253662 : Nat := 4983230072969 + 3 ^ 40 * 3253662 * 2
def baseEnd_3253662 : Nat := 185632499252128251795743

theorem tailTrace_3253662 : CollatzResearch.WordTrace tailWord_3253662 prefixEnd_3253662 185632499252128251795743 := by
  unfold tailWord_3253662
  simp only [CollatzResearch.WordTrace]
  refine ⟨14833850292318216259333405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79113868225697153383111493 14833850292318216259333405)
  ·
    refine ⟨5562693859619331097250027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14833850292318216259333405 5562693859619331097250027)
    ·
      refine ⟨8344040789428996645875041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5562693859619331097250027 8344040789428996645875041)
      ·
        refine ⟨6258030592071747484406281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8344040789428996645875041 6258030592071747484406281)
        ·
          refine ⟨4693522944053810613304711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6258030592071747484406281 4693522944053810613304711)
          ·
            refine ⟨7040284416080715919957067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4693522944053810613304711 7040284416080715919957067)
            ·
              refine ⟨10560426624121073879935601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7040284416080715919957067 10560426624121073879935601)
              ·
                refine ⟨7920319968090805409951701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10560426624121073879935601 7920319968090805409951701)
                ·
                  refine ⟨185632499252128251795743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7920319968090805409951701 185632499252128251795743)
                  ·
                    rfl

theorem cell23_3253662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_3253662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253662 prefixEnd_3253662 := by exact prefixLift 3253662
  have htrace : WordTrace (prefixWord ++ tailWord_3253662) baseStart_3253662 baseEnd_3253662 := by
    simpa [prefixWord, tailWord_3253662, baseEnd_3253662] using wordTrace_append hprefix tailTrace_3253662
  have hstable : (prefixWord ++ tailWord_3253662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253662).length < 2 ^ (prefixWord ++ tailWord_3253662).sum := by decide
  have hdescent : baseEnd_3253662 < baseStart_3253662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253749 : List Nat := [1, 3, 5, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_3253749 : Nat := 118140960795 + 3253749 * 2 ^ 59
def prefixEnd_3253749 : Nat := 4983230072969 + 3 ^ 40 * 3253749 * 2
def baseEnd_3253749 : Nat := 1670737166086095425773787

theorem tailTrace_3253749 : CollatzResearch.WordTrace tailWord_3253749 prefixEnd_3253749 1670737166086095425773787 := by
  unfold tailWord_3253749
  simp only [CollatzResearch.WordTrace]
  refine ⟨118673975489230543933084301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79115983659487029288722867 118673975489230543933084301)
  ·
    refine ⟨44502740808461453974906613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118673975489230543933084301 44502740808461453974906613)
    ·
      refine ⟨4172131950793261310147495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44502740808461453974906613 4172131950793261310147495)
      ·
        refine ⟨6258197926189891965221243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4172131950793261310147495 6258197926189891965221243)
        ·
          refine ⟨9387296889284837947831865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6258197926189891965221243 9387296889284837947831865)
          ·
            refine ⟨7040472666963628460873899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9387296889284837947831865 7040472666963628460873899)
            ·
              refine ⟨10560709000445442691310849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7040472666963628460873899 10560709000445442691310849)
              ·
                refine ⟨7920531750334082018483137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10560709000445442691310849 7920531750334082018483137)
                ·
                  refine ⟨5940398812750561513862353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7920531750334082018483137 5940398812750561513862353)
                  ·
                    refine ⟨4455299109562921135396765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5940398812750561513862353 4455299109562921135396765)
                    ·
                      refine ⟨1670737166086095425773787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4455299109562921135396765 1670737166086095425773787)
                      ·
                        rfl

theorem cell23_3253749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_3253749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253749 prefixEnd_3253749 := by exact prefixLift 3253749
  have htrace : WordTrace (prefixWord ++ tailWord_3253749) baseStart_3253749 baseEnd_3253749 := by
    simpa [prefixWord, tailWord_3253749, baseEnd_3253749] using wordTrace_append hprefix tailTrace_3253749
  have hstable : (prefixWord ++ tailWord_3253749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253749).length < 2 ^ (prefixWord ++ tailWord_3253749).sum := by decide
  have hdescent : baseEnd_3253749 < baseStart_3253749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253789 : List Nat := [1, 4, 2, 2, 1, 1, 4, 1, 2, 3, 2]
def baseStart_3253789 : Nat := 118140960795 + 3253789 * 2 ^ 59
def prefixEnd_3253789 : Nat := 4983230072969 + 3 ^ 40 * 3253789 * 2
def baseEnd_3253789 : Nat := 1670757705312275269273603

theorem tailTrace_3253789 : CollatzResearch.WordTrace tailWord_3253789 prefixEnd_3253789 1670757705312275269273603 := by
  unfold tailWord_3253789
  simp only [CollatzResearch.WordTrace]
  refine ⟨118675434409085630764540421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79116956272723753843026947 118675434409085630764540421)
  ·
    refine ⟨22251643951703555768351329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118675434409085630764540421 22251643951703555768351329)
    ·
      refine ⟨16688732963777666826263497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22251643951703555768351329 16688732963777666826263497)
      ·
        refine ⟨12516549722833250119697623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16688732963777666826263497 12516549722833250119697623)
        ·
          refine ⟨18774824584249875179546435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12516549722833250119697623 18774824584249875179546435)
          ·
            refine ⟨28162236876374812769319653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18774824584249875179546435 28162236876374812769319653)
            ·
              refine ⟨5280419414320277394247435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28162236876374812769319653 5280419414320277394247435)
              ·
                refine ⟨7920629121480416091371153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5280419414320277394247435 7920629121480416091371153)
                ·
                  refine ⟨5940471841110312068528365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7920629121480416091371153 5940471841110312068528365)
                  ·
                    refine ⟨2227676940416367025698137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5940471841110312068528365 2227676940416367025698137)
                    ·
                      refine ⟨1670757705312275269273603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2227676940416367025698137 1670757705312275269273603)
                      ·
                        rfl

theorem cell23_3253789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_3253789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253789 prefixEnd_3253789 := by exact prefixLift 3253789
  have htrace : WordTrace (prefixWord ++ tailWord_3253789) baseStart_3253789 baseEnd_3253789 := by
    simpa [prefixWord, tailWord_3253789, baseEnd_3253789] using wordTrace_append hprefix tailTrace_3253789
  have hstable : (prefixWord ++ tailWord_3253789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253789).length < 2 ^ (prefixWord ++ tailWord_3253789).sum := by decide
  have hdescent : baseEnd_3253789 < baseStart_3253789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253813 : List Nat := [1, 3, 3, 1, 1, 5, 2, 2, 1, 1, 3]
def baseStart_3253813 : Nat := 118140960795 + 3253813 * 2 ^ 59
def prefixEnd_3253813 : Nat := 4983230072969 + 3 ^ 40 * 3253813 * 2
def baseEnd_3253813 : Nat := 1670770028847983175373493

theorem tailTrace_3253813 : CollatzResearch.WordTrace tailWord_3253813 prefixEnd_3253813 1670770028847983175373493 := by
  unfold tailWord_3253813
  simp only [CollatzResearch.WordTrace]
  refine ⟨118676309760998682863414093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79117539840665788575609395 118676309760998682863414093)
  ·
    refine ⟨44503616160374506073780285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118676309760998682863414093 44503616160374506073780285)
    ·
      refine ⟨16688856060140439777667607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44503616160374506073780285 16688856060140439777667607)
      ·
        refine ⟨25033284090210659666501411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16688856060140439777667607 25033284090210659666501411)
        ·
          refine ⟨37549926135315989499752117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25033284090210659666501411 37549926135315989499752117)
          ·
            refine ⟨3520305575185874015601761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37549926135315989499752117 3520305575185874015601761)
            ·
              refine ⟨2640229181389405511701321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3520305575185874015601761 2640229181389405511701321)
              ·
                refine ⟨1980171886042054133775991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2640229181389405511701321 1980171886042054133775991)
                ·
                  refine ⟨2970257829063081200663987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1980171886042054133775991 2970257829063081200663987)
                  ·
                    refine ⟨4455386743594621800995981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2970257829063081200663987 4455386743594621800995981)
                    ·
                      refine ⟨1670770028847983175373493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4455386743594621800995981 1670770028847983175373493)
                      ·
                        rfl

theorem cell23_3253813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_3253813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253813 prefixEnd_3253813 := by exact prefixLift 3253813
  have htrace : WordTrace (prefixWord ++ tailWord_3253813) baseStart_3253813 baseEnd_3253813 := by
    simpa [prefixWord, tailWord_3253813, baseEnd_3253813] using wordTrace_append hprefix tailTrace_3253813
  have hstable : (prefixWord ++ tailWord_3253813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253813).length < 2 ^ (prefixWord ++ tailWord_3253813).sum := by decide
  have hdescent : baseEnd_3253813 < baseStart_3253813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253842 : List Nat := [3, 2, 2, 1, 2, 3, 3, 7]
def baseStart_3253842 : Nat := 118140960795 + 3253842 * 2 ^ 59
def prefixEnd_3253842 : Nat := 4983230072969 + 3 ^ 40 * 3253842 * 2
def baseEnd_3253842 : Nat := 61880922955072724515217

theorem tailTrace_3253842 : CollatzResearch.WordTrace tailWord_3253842 prefixEnd_3253842 61880922955072724515217 := by
  unfold tailWord_3253842
  simp only [CollatzResearch.WordTrace]
  refine ⟨29669341869473405204054945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79118244985262413877479853 29669341869473405204054945)
  ·
    refine ⟨22252006402105053903041209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29669341869473405204054945 22252006402105053903041209)
    ·
      refine ⟨16689004801578790427280907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22252006402105053903041209 16689004801578790427280907)
      ·
        refine ⟨25033507202368185640921361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16689004801578790427280907 25033507202368185640921361)
        ·
          refine ⟨18775130401776139230691021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25033507202368185640921361 18775130401776139230691021)
          ·
            refine ⟨7040673900666052211509133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18775130401776139230691021 7040673900666052211509133)
            ·
              refine ⟨2640252712749769579315925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7040673900666052211509133 2640252712749769579315925)
              ·
                refine ⟨61880922955072724515217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2640252712749769579315925 61880922955072724515217)
                ·
                  rfl

theorem cell23_3253842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 7].length) (baseStart_3253842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253842 prefixEnd_3253842 := by exact prefixLift 3253842
  have htrace : WordTrace (prefixWord ++ tailWord_3253842) baseStart_3253842 baseEnd_3253842 := by
    simpa [prefixWord, tailWord_3253842, baseEnd_3253842] using wordTrace_append hprefix tailTrace_3253842
  have hstable : (prefixWord ++ tailWord_3253842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253842).length < 2 ^ (prefixWord ++ tailWord_3253842).sum := by decide
  have hdescent : baseEnd_3253842 < baseStart_3253842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253905 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 4]
def baseStart_3253905 : Nat := 118140960795 + 3253905 * 2 ^ 59
def prefixEnd_3253905 : Nat := 4983230072969 + 3 ^ 40 * 3253905 * 2
def baseEnd_3253905 : Nat := 1670817269068196815423069

theorem tailTrace_3253905 : CollatzResearch.WordTrace tailWord_3253905 prefixEnd_3253905 1670817269068196815423069 := by
  unfold tailWord_3253905
  simp only [CollatzResearch.WordTrace]
  refine ⟨118679665276665382575763169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79119776851110255050508779 118679665276665382575763169)
  ·
    refine ⟨89009748957499036931822377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118679665276665382575763169 89009748957499036931822377)
    ·
      refine ⟨66757311718124277698866783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89009748957499036931822377 66757311718124277698866783)
      ·
        refine ⟨100135967577186416548300175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66757311718124277698866783 100135967577186416548300175)
        ·
          refine ⟨150203951365779624822450263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100135967577186416548300175 150203951365779624822450263)
          ·
            refine ⟨225305927048669437233675395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150203951365779624822450263 225305927048669437233675395)
            ·
              refine ⟨337958890573004155850513093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225305927048669437233675395 337958890573004155850513093)
              ·
                refine ⟨63367291982438279221971205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 337958890573004155850513093 63367291982438279221971205)
                ·
                  refine ⟨11881367246707177354119601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63367291982438279221971205 11881367246707177354119601)
                  ·
                    refine ⟨8911025435030383015589701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11881367246707177354119601 8911025435030383015589701)
                    ·
                      refine ⟨1670817269068196815423069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8911025435030383015589701 1670817269068196815423069)
                      ·
                        rfl

theorem cell23_3253905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_3253905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253905 prefixEnd_3253905 := by exact prefixLift 3253905
  have htrace : WordTrace (prefixWord ++ tailWord_3253905) baseStart_3253905 baseEnd_3253905 := by
    simpa [prefixWord, tailWord_3253905, baseEnd_3253905] using wordTrace_append hprefix tailTrace_3253905
  have hstable : (prefixWord ++ tailWord_3253905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253905).length < 2 ^ (prefixWord ++ tailWord_3253905).sum := by decide
  have hdescent : baseEnd_3253905 < baseStart_3253905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253912 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 2, 1, 5]
def baseStart_3253912 : Nat := 118140960795 + 3253912 * 2 ^ 59
def prefixEnd_3253912 : Nat := 4983230072969 + 3 ^ 40 * 3253912 * 2
def baseEnd_3253912 : Nat := 1670820863432778288035537

theorem tailTrace_3253912 : CollatzResearch.WordTrace tailWord_3253912 prefixEnd_3253912 1670820863432778288035537 := by
  unfold tailWord_3253912
  simp only [CollatzResearch.WordTrace]
  refine ⟨59339960293820011385633995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79119947058426681847511993 59339960293820011385633995)
  ·
    refine ⟨89009940440730017078450993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59339960293820011385633995 89009940440730017078450993)
    ·
      refine ⟨66757455330547512808838245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89009940440730017078450993 66757455330547512808838245)
      ·
        refine ⟨12517022874477658651657171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66757455330547512808838245 12517022874477658651657171)
        ·
          refine ⟨18775534311716487977485757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12517022874477658651657171 18775534311716487977485757)
          ·
            refine ⟨7040825366893682991557159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18775534311716487977485757 7040825366893682991557159)
            ·
              refine ⟨10561238050340524487335739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7040825366893682991557159 10561238050340524487335739)
              ·
                refine ⟨15841857075510786731003609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10561238050340524487335739 15841857075510786731003609)
                ·
                  refine ⟨11881392806633090048252707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15841857075510786731003609 11881392806633090048252707)
                  ·
                    refine ⟨17822089209949635072379061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11881392806633090048252707 17822089209949635072379061)
                    ·
                      refine ⟨1670820863432778288035537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17822089209949635072379061 1670820863432778288035537)
                      ·
                        rfl

theorem cell23_3253912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_3253912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253912 prefixEnd_3253912 := by exact prefixLift 3253912
  have htrace : WordTrace (prefixWord ++ tailWord_3253912) baseStart_3253912 baseEnd_3253912 := by
    simpa [prefixWord, tailWord_3253912, baseEnd_3253912] using wordTrace_append hprefix tailTrace_3253912
  have hstable : (prefixWord ++ tailWord_3253912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253912).length < 2 ^ (prefixWord ++ tailWord_3253912).sum := by decide
  have hdescent : baseEnd_3253912 < baseStart_3253912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253943 : List Nat := [1, 1, 3, 1, 5, 1, 4, 1, 2, 2, 2]
def baseStart_3253943 : Nat := 118140960795 + 3253943 * 2 ^ 59
def prefixEnd_3253943 : Nat := 4983230072969 + 3 ^ 40 * 3253943 * 2
def baseEnd_3253943 : Nat := 1670836781333067666747895

theorem tailTrace_3253943 : CollatzResearch.WordTrace tailWord_3253943 prefixEnd_3253943 1670836781333067666747895 := by
  unfold tailWord_3253943
  simp only [CollatzResearch.WordTrace]
  refine ⟨118681051250527715065646483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79120700833685143377097655 118681051250527715065646483)
  ·
    refine ⟨178021576875791572598469725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118681051250527715065646483 178021576875791572598469725)
    ·
      refine ⟨66758091328421839724426147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178021576875791572598469725 66758091328421839724426147)
      ·
        refine ⟨100137136992632759586639221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66758091328421839724426147 100137136992632759586639221)
        ·
          refine ⟨9387856593059321211247427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100137136992632759586639221 9387856593059321211247427)
          ·
            refine ⟨14081784889588981816871141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9387856593059321211247427 14081784889588981816871141)
            ·
              refine ⟨2640334666797934090663339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14081784889588981816871141 2640334666797934090663339)
              ·
                refine ⟨3960502000196901135995009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2640334666797934090663339 3960502000196901135995009)
                ·
                  refine ⟨2970376500147675851996257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3960502000196901135995009 2970376500147675851996257)
                  ·
                    refine ⟨2227782375110756888997193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2970376500147675851996257 2227782375110756888997193)
                    ·
                      refine ⟨1670836781333067666747895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2227782375110756888997193 1670836781333067666747895)
                      ·
                        rfl

theorem cell23_3253943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 2, 2, 2].length) (baseStart_3253943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253943 prefixEnd_3253943 := by exact prefixLift 3253943
  have htrace : WordTrace (prefixWord ++ tailWord_3253943) baseStart_3253943 baseEnd_3253943 := by
    simpa [prefixWord, tailWord_3253943, baseEnd_3253943] using wordTrace_append hprefix tailTrace_3253943
  have hstable : (prefixWord ++ tailWord_3253943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253943).length < 2 ^ (prefixWord ++ tailWord_3253943).sum := by decide
  have hdescent : baseEnd_3253943 < baseStart_3253943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253945 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 3, 7]
def baseStart_3253945 : Nat := 118140960795 + 3253945 * 2 ^ 59
def prefixEnd_3253945 : Nat := 4983230072969 + 3 ^ 40 * 3253945 * 2
def baseEnd_3253945 : Nat := 556945936098125552974295

theorem tailTrace_3253945 : CollatzResearch.WordTrace tailWord_3253945 prefixEnd_3253945 556945936098125552974295 := by
  unfold tailWord_3253945
  simp only [CollatzResearch.WordTrace]
  refine ⟨118681124196520469407219289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79120749464346979604812859 118681124196520469407219289)
  ·
    refine ⟨89010843147390352055414467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118681124196520469407219289 89010843147390352055414467)
    ·
      refine ⟨133516264721085528083121701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89010843147390352055414467 133516264721085528083121701)
      ·
        refine ⟨25034299635203536515585319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133516264721085528083121701 25034299635203536515585319)
        ·
          refine ⟨37551449452805304773377979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25034299635203536515585319 37551449452805304773377979)
          ·
            refine ⟨56327174179207957160066969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37551449452805304773377979 56327174179207957160066969)
            ·
              refine ⟨42245380634405967870050227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56327174179207957160066969 42245380634405967870050227)
              ·
                refine ⟨63368070951608951805075341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42245380634405967870050227 63368070951608951805075341)
                ·
                  refine ⟨23763026606853356926903253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63368070951608951805075341 23763026606853356926903253)
                  ·
                    refine ⟨556945936098125552974295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23763026606853356926903253 556945936098125552974295)
                    ·
                      rfl

theorem cell23_3253945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 7].length) (baseStart_3253945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253945 prefixEnd_3253945 := by exact prefixLift 3253945
  have htrace : WordTrace (prefixWord ++ tailWord_3253945) baseStart_3253945 baseEnd_3253945 := by
    simpa [prefixWord, tailWord_3253945, baseEnd_3253945] using wordTrace_append hprefix tailTrace_3253945
  have hstable : (prefixWord ++ tailWord_3253945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253945).length < 2 ^ (prefixWord ++ tailWord_3253945).sum := by decide
  have hdescent : baseEnd_3253945 < baseStart_3253945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253999 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 2, 4, 2]
def baseStart_3253999 : Nat := 118140960795 + 3253999 * 2 ^ 59
def prefixEnd_3253999 : Nat := 4983230072969 + 3 ^ 40 * 3253999 * 2
def baseEnd_3253999 : Nat := 1670865536249719447647637

theorem tailTrace_3253999 : CollatzResearch.WordTrace tailWord_3253999 prefixEnd_3253999 1670865536249719447647637 := by
  unfold tailWord_3253999
  simp only [CollatzResearch.WordTrace]
  refine ⟨118683093738324836629685051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79122062492216557753123367 118683093738324836629685051)
  ·
    refine ⟨178024640607487254944527577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118683093738324836629685051 178024640607487254944527577)
    ·
      refine ⟨133518480455615441208395683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178024640607487254944527577 133518480455615441208395683)
      ·
        refine ⟨200277720683423161812593525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133518480455615441208395683 200277720683423161812593525)
        ·
          refine ⟨18776036314070921419930643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 200277720683423161812593525 18776036314070921419930643)
          ·
            refine ⟨28164054471106382129895965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18776036314070921419930643 28164054471106382129895965)
            ·
              refine ⟨10561520426664893298710987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28164054471106382129895965 10561520426664893298710987)
              ·
                refine ⟨15842280639997339948066481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10561520426664893298710987 15842280639997339948066481)
                ·
                  refine ⟨11881710479998004961049861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15842280639997339948066481 11881710479998004961049861)
                  ·
                    refine ⟨2227820714999625930196849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11881710479998004961049861 2227820714999625930196849)
                    ·
                      refine ⟨1670865536249719447647637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2227820714999625930196849 1670865536249719447647637)
                      ·
                        rfl

theorem cell23_3253999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 4, 2].length) (baseStart_3253999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3253999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3253999 prefixEnd_3253999 := by exact prefixLift 3253999
  have htrace : WordTrace (prefixWord ++ tailWord_3253999) baseStart_3253999 baseEnd_3253999 := by
    simpa [prefixWord, tailWord_3253999, baseEnd_3253999] using wordTrace_append hprefix tailTrace_3253999
  have hstable : (prefixWord ++ tailWord_3253999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253999).length < 2 ^ (prefixWord ++ tailWord_3253999).sum := by decide
  have hdescent : baseEnd_3253999 < baseStart_3253999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254019 : List Nat := [1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 3]
def baseStart_3254019 : Nat := 118140960795 + 3254019 * 2 ^ 59
def prefixEnd_3254019 : Nat := 4983230072969 + 3 ^ 40 * 3254019 * 2
def baseEnd_3254019 : Nat := 1670875805862809369397545

theorem tailTrace_3254019 : CollatzResearch.WordTrace tailWord_3254019 prefixEnd_3254019 1670875805862809369397545 := by
  unfold tailWord_3254019
  simp only [CollatzResearch.WordTrace]
  refine ⟨118683823198252380045413111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79122548798834920030275407 118683823198252380045413111)
  ·
    refine ⟨178025734797378570068119667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118683823198252380045413111 178025734797378570068119667)
    ·
      refine ⟨267038602196067855102179501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178025734797378570068119667 267038602196067855102179501)
      ·
        refine ⟨100139475823525445663317313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267038602196067855102179501 100139475823525445663317313)
        ·
          refine ⟨75104606867644084247487985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100139475823525445663317313 75104606867644084247487985)
          ·
            refine ⟨56328455150733063185615989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75104606867644084247487985 56328455150733063185615989)
            ·
              refine ⟨5280792670381224673651499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56328455150733063185615989 5280792670381224673651499)
              ·
                refine ⟨7921189005571837010477249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5280792670381224673651499 7921189005571837010477249)
                ·
                  refine ⟨5940891754178877757857937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7921189005571837010477249 5940891754178877757857937)
                  ·
                    refine ⟨4455668815634158318393453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5940891754178877757857937 4455668815634158318393453)
                    ·
                      refine ⟨1670875805862809369397545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4455668815634158318393453 1670875805862809369397545)
                      ·
                        rfl

theorem cell23_3254019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 3].length) (baseStart_3254019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254019 prefixEnd_3254019 := by exact prefixLift 3254019
  have htrace : WordTrace (prefixWord ++ tailWord_3254019) baseStart_3254019 baseEnd_3254019 := by
    simpa [prefixWord, tailWord_3254019, baseEnd_3254019] using wordTrace_append hprefix tailTrace_3254019
  have hstable : (prefixWord ++ tailWord_3254019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254019).length < 2 ^ (prefixWord ++ tailWord_3254019).sum := by decide
  have hdescent : baseEnd_3254019 < baseStart_3254019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254026 : List Nat := [3, 1, 2, 2, 1, 3, 1, 5, 1, 4]
def baseStart_3254026 : Nat := 118140960795 + 3254026 * 2 ^ 59
def prefixEnd_3254026 : Nat := 4983230072969 + 3 ^ 40 * 3254026 * 2
def baseEnd_3254026 : Nat := 556959800075796947336671

theorem tailTrace_3254026 : CollatzResearch.WordTrace tailWord_3254026 prefixEnd_3254026 556959800075796947336671 := by
  unfold tailWord_3254026
  simp only [CollatzResearch.WordTrace]
  refine ⟨29671019627306755060229483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79122719006151346827278621 29671019627306755060229483)
  ·
    refine ⟨44506529440960132590344225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29671019627306755060229483 44506529440960132590344225)
    ·
      refine ⟨33379897080720099442758169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44506529440960132590344225 33379897080720099442758169)
      ·
        refine ⟨25034922810540074582068627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33379897080720099442758169 25034922810540074582068627)
        ·
          refine ⟨37552384215810111873102941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25034922810540074582068627 37552384215810111873102941)
          ·
            refine ⟨14082144080928791952413603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37552384215810111873102941 14082144080928791952413603)
            ·
              refine ⟨21123216121393187928620405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14082144080928791952413603 21123216121393187928620405)
              ·
                refine ⟨1980301511380611368308163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21123216121393187928620405 1980301511380611368308163)
                ·
                  refine ⟨2970452267070917052462245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1980301511380611368308163 2970452267070917052462245)
                  ·
                    refine ⟨556959800075796947336671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2970452267070917052462245 556959800075796947336671)
                    ·
                      rfl

theorem cell23_3254026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_3254026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254026 prefixEnd_3254026 := by exact prefixLift 3254026
  have htrace : WordTrace (prefixWord ++ tailWord_3254026) baseStart_3254026 baseEnd_3254026 := by
    simpa [prefixWord, tailWord_3254026, baseEnd_3254026] using wordTrace_append hprefix tailTrace_3254026
  have hstable : (prefixWord ++ tailWord_3254026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254026).length < 2 ^ (prefixWord ++ tailWord_3254026).sum := by decide
  have hdescent : baseEnd_3254026 < baseStart_3254026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254039 : List Nat := [1, 1, 3, 4, 2, 1, 3, 2, 6]
def baseStart_3254039 : Nat := 118140960795 + 3254039 * 2 ^ 59
def prefixEnd_3254039 : Nat := 4983230072969 + 3 ^ 40 * 3254039 * 2
def baseEnd_3254039 : Nat := 185654008386211032349717

theorem tailTrace_3254039 : CollatzResearch.WordTrace tailWord_3254039 prefixEnd_3254039 185654008386211032349717 := by
  unfold tailWord_3254039
  simp only [CollatzResearch.WordTrace]
  refine ⟨118684552658179923461141171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79123035105453282307427447 118684552658179923461141171)
  ·
    refine ⟨178026828987269885191711757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118684552658179923461141171 178026828987269885191711757)
    ·
      refine ⟨66760060870226206946891909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178026828987269885191711757 66760060870226206946891909)
      ·
        refine ⟨12517511413167413802542233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66760060870226206946891909 12517511413167413802542233)
        ·
          refine ⟨9388133559875560351906675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12517511413167413802542233 9388133559875560351906675)
          ·
            refine ⟨14082200339813340527860013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9388133559875560351906675 14082200339813340527860013)
            ·
              refine ⟨5280825127430002697947505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14082200339813340527860013 5280825127430002697947505)
              ·
                refine ⟨3960618845572502023460629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5280825127430002697947505 3960618845572502023460629)
                ·
                  refine ⟨185654008386211032349717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3960618845572502023460629 185654008386211032349717)
                  ·
                    rfl

theorem cell23_3254039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 6].length) (baseStart_3254039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254039 prefixEnd_3254039 := by exact prefixLift 3254039
  have htrace : WordTrace (prefixWord ++ tailWord_3254039) baseStart_3254039 baseEnd_3254039 := by
    simpa [prefixWord, tailWord_3254039, baseEnd_3254039] using wordTrace_append hprefix tailTrace_3254039
  have hstable : (prefixWord ++ tailWord_3254039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254039).length < 2 ^ (prefixWord ++ tailWord_3254039).sum := by decide
  have hdescent : baseEnd_3254039 < baseStart_3254039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254042 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6]
def baseStart_3254042 : Nat := 118140960795 + 3254042 * 2 ^ 59
def prefixEnd_3254042 : Nat := 4983230072969 + 3 ^ 40 * 3254042 * 2
def baseEnd_3254042 : Nat := 1670887615917862779409939

theorem tailTrace_3254042 : CollatzResearch.WordTrace tailWord_3254042 prefixEnd_3254042 1670887615917862779409939 := by
  unfold tailWord_3254042
  simp only [CollatzResearch.WordTrace]
  refine ⟨29671165519292263743375095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79123108051446036649000253 29671165519292263743375095)
  ·
    refine ⟨44506748278938395615062643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29671165519292263743375095 44506748278938395615062643)
    ·
      refine ⟨66760122418407593422593965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44506748278938395615062643 66760122418407593422593965)
      ·
        refine ⟨25035045906902847533472737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66760122418407593422593965 25035045906902847533472737)
        ·
          refine ⟨18776284430177135650104553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25035045906902847533472737 18776284430177135650104553)
          ·
            refine ⟨14082213322632851737578415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18776284430177135650104553 14082213322632851737578415)
            ·
              refine ⟨21123319983949277606367623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14082213322632851737578415 21123319983949277606367623)
              ·
                refine ⟨31684979975923916409551435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21123319983949277606367623 31684979975923916409551435)
                ·
                  refine ⟨47527469963885874614327153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31684979975923916409551435 47527469963885874614327153)
                  ·
                    refine ⟨35645602472914405960745365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47527469963885874614327153 35645602472914405960745365)
                    ·
                      refine ⟨1670887615917862779409939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35645602472914405960745365 1670887615917862779409939)
                      ·
                        rfl

theorem cell23_3254042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_3254042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254042 prefixEnd_3254042 := by exact prefixLift 3254042
  have htrace : WordTrace (prefixWord ++ tailWord_3254042) baseStart_3254042 baseEnd_3254042 := by
    simpa [prefixWord, tailWord_3254042, baseEnd_3254042] using wordTrace_append hprefix tailTrace_3254042
  have hstable : (prefixWord ++ tailWord_3254042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254042).length < 2 ^ (prefixWord ++ tailWord_3254042).sum := by decide
  have hdescent : baseEnd_3254042 < baseStart_3254042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254056 : List Nat := [2, 1, 5, 1, 1, 3, 3, 1, 6]
def baseStart_3254056 : Nat := 118140960795 + 3254056 * 2 ^ 59
def prefixEnd_3254056 : Nat := 4983230072969 + 3 ^ 40 * 3254056 * 2
def baseEnd_3254056 : Nat := 185654978294113969403875

theorem tailTrace_3254056 : CollatzResearch.WordTrace tailWord_3254056 prefixEnd_3254056 185654978294113969403875 := by
  unfold tailWord_3254056
  simp only [CollatzResearch.WordTrace]
  refine ⟨59342586349559167682255011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79123448466078890243006681 59342586349559167682255011)
  ·
    refine ⟨89013879524338751523382517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59342586349559167682255011 89013879524338751523382517)
    ·
      refine ⟨8345051205406757955317111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89013879524338751523382517 8345051205406757955317111)
      ·
        refine ⟨12517576808110136932975667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8345051205406757955317111 12517576808110136932975667)
        ·
          refine ⟨18776365212165205399463501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12517576808110136932975667 18776365212165205399463501)
          ·
            refine ⟨7041136954561952024798813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18776365212165205399463501 7041136954561952024798813)
            ·
              refine ⟨2640426357960732009299555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7041136954561952024798813 2640426357960732009299555)
              ·
                refine ⟨3960639536941098013949333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2640426357960732009299555 3960639536941098013949333)
                ·
                  refine ⟨185654978294113969403875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3960639536941098013949333 185654978294113969403875)
                  ·
                    rfl

theorem cell23_3254056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 6].length) (baseStart_3254056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254056 prefixEnd_3254056 := by exact prefixLift 3254056
  have htrace : WordTrace (prefixWord ++ tailWord_3254056) baseStart_3254056 baseEnd_3254056 := by
    simpa [prefixWord, tailWord_3254056, baseEnd_3254056] using wordTrace_append hprefix tailTrace_3254056
  have hstable : (prefixWord ++ tailWord_3254056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254056).length < 2 ^ (prefixWord ++ tailWord_3254056).sum := by decide
  have hdescent : baseEnd_3254056 < baseStart_3254056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254066 : List Nat := [3, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3]
def baseStart_3254066 : Nat := 118140960795 + 3254066 * 2 ^ 59
def prefixEnd_3254066 : Nat := 4983230072969 + 3 ^ 40 * 3254066 * 2
def baseEnd_3254066 : Nat := 1670899939453570685509829

theorem tailTrace_3254066 : CollatzResearch.WordTrace tailWord_3254066 prefixEnd_3254066 1670899939453570685509829 := by
  unfold tailWord_3254066
  simp only [CollatzResearch.WordTrace]
  refine ⟨29671384357270526768093513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79123691619388071381582701 29671384357270526768093513)
  ·
    refine ⟨22253538267952895076070135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29671384357270526768093513 22253538267952895076070135)
    ·
      refine ⟨33380307401929342614105203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22253538267952895076070135 33380307401929342614105203)
      ·
        refine ⟨50070461102894013921157805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33380307401929342614105203 50070461102894013921157805)
        ·
          refine ⟨18776422913585255220434177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50070461102894013921157805 18776422913585255220434177)
          ·
            refine ⟨14082317185188941415325633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18776422913585255220434177 14082317185188941415325633)
            ·
              refine ⟨10561737888891706061494225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14082317185188941415325633 10561737888891706061494225)
              ·
                refine ⟨7921303416668779546120669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10561737888891706061494225 7921303416668779546120669)
                ·
                  refine ⟨2970488781250792329795251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7921303416668779546120669 2970488781250792329795251)
                  ·
                    refine ⟨4455733171876188494692877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2970488781250792329795251 4455733171876188494692877)
                    ·
                      refine ⟨1670899939453570685509829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4455733171876188494692877 1670899939453570685509829)
                      ·
                        rfl

theorem cell23_3254066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_3254066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254066 prefixEnd_3254066 := by exact prefixLift 3254066
  have htrace : WordTrace (prefixWord ++ tailWord_3254066) baseStart_3254066 baseEnd_3254066 := by
    simpa [prefixWord, tailWord_3254066, baseEnd_3254066] using wordTrace_append hprefix tailTrace_3254066
  have hstable : (prefixWord ++ tailWord_3254066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254066).length < 2 ^ (prefixWord ++ tailWord_3254066).sum := by decide
  have hdescent : baseEnd_3254066 < baseStart_3254066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254083 : List Nat := [1, 1, 1, 3, 1, 5, 3, 3, 1, 1, 3]
def baseStart_3254083 : Nat := 118140960795 + 3254083 * 2 ^ 59
def prefixEnd_3254083 : Nat := 4983230072969 + 3 ^ 40 * 3254083 * 2
def baseEnd_3254083 : Nat := 1670908668624697118997251

theorem tailTrace_3254083 : CollatzResearch.WordTrace tailWord_3254083 prefixEnd_3254083 1670908668624697118997251 := by
  unfold tailWord_3254083
  simp only [CollatzResearch.WordTrace]
  refine ⟨118686157470020518975742903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79124104980013679317161935 118686157470020518975742903)
  ·
    refine ⟨178029236205030778463614355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118686157470020518975742903 178029236205030778463614355)
    ·
      refine ⟨267043854307546167695421533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178029236205030778463614355 267043854307546167695421533)
      ·
        refine ⟨100141445365329812885783075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267043854307546167695421533 100141445365329812885783075)
        ·
          refine ⟨150212168047994719328674613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100141445365329812885783075 150212168047994719328674613)
          ·
            refine ⟨14082390754499504937063245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150212168047994719328674613 14082390754499504937063245)
            ·
              refine ⟨5280896532937314351398717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14082390754499504937063245 5280896532937314351398717)
              ·
                refine ⟨1980336199851492881774519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5280896532937314351398717 1980336199851492881774519)
                ·
                  refine ⟨2970504299777239322661779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1980336199851492881774519 2970504299777239322661779)
                  ·
                    refine ⟨4455756449665858983992669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2970504299777239322661779 4455756449665858983992669)
                    ·
                      refine ⟨1670908668624697118997251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4455756449665858983992669 1670908668624697118997251)
                      ·
                        rfl

theorem cell23_3254083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 1, 1, 3].length) (baseStart_3254083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254083 prefixEnd_3254083 := by exact prefixLift 3254083
  have htrace : WordTrace (prefixWord ++ tailWord_3254083) baseStart_3254083 baseEnd_3254083 := by
    simpa [prefixWord, tailWord_3254083, baseEnd_3254083] using wordTrace_append hprefix tailTrace_3254083
  have hstable : (prefixWord ++ tailWord_3254083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254083).length < 2 ^ (prefixWord ++ tailWord_3254083).sum := by decide
  have hdescent : baseEnd_3254083 < baseStart_3254083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254089 : List Nat := [1, 2, 1, 1, 2, 4, 1, 5, 1, 1, 4]
def baseStart_3254089 : Nat := 118140960795 + 3254089 * 2 ^ 59
def prefixEnd_3254089 : Nat := 4983230072969 + 3 ^ 40 * 3254089 * 2
def baseEnd_3254089 : Nat := 1670911749508624095522223

theorem tailTrace_3254089 : CollatzResearch.WordTrace tailWord_3254089 prefixEnd_3254089 1670911749508624095522223 := by
  unfold tailWord_3254089
  simp only [CollatzResearch.WordTrace]
  refine ⟨118686376307998782000461321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79124250871999188000307547 118686376307998782000461321)
  ·
    refine ⟨89014782230999086500345991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118686376307998782000461321 89014782230999086500345991)
    ·
      refine ⟨133522173346498629750518987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89014782230999086500345991 133522173346498629750518987)
      ·
        refine ⟨200283260019747944625778481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133522173346498629750518987 200283260019747944625778481)
        ·
          refine ⟨150212445014810958469333861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200283260019747944625778481 150212445014810958469333861)
          ·
            refine ⟨28164833440277054713000099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150212445014810958469333861 28164833440277054713000099)
            ·
              refine ⟨42247250160415582069500149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28164833440277054713000099 42247250160415582069500149)
              ·
                refine ⟨3960679702538960819015639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42247250160415582069500149 3960679702538960819015639)
                ·
                  refine ⟨5941019553808441228523459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3960679702538960819015639 5941019553808441228523459)
                  ·
                    refine ⟨8911529330712661842785189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5941019553808441228523459 8911529330712661842785189)
                    ·
                      refine ⟨1670911749508624095522223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8911529330712661842785189 1670911749508624095522223)
                      ·
                        rfl

theorem cell23_3254089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 1, 4].length) (baseStart_3254089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254089 prefixEnd_3254089 := by exact prefixLift 3254089
  have htrace : WordTrace (prefixWord ++ tailWord_3254089) baseStart_3254089 baseEnd_3254089 := by
    simpa [prefixWord, tailWord_3254089, baseEnd_3254089] using wordTrace_append hprefix tailTrace_3254089
  have hstable : (prefixWord ++ tailWord_3254089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254089).length < 2 ^ (prefixWord ++ tailWord_3254089).sum := by decide
  have hdescent : baseEnd_3254089 < baseStart_3254089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254093 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 4, 3, 2]
def baseStart_3254093 : Nat := 118140960795 + 3254093 * 2 ^ 59
def prefixEnd_3254093 : Nat := 4983230072969 + 3 ^ 40 * 3254093 * 2
def baseEnd_3254093 : Nat := 1670913803431242079872205

theorem tailTrace_3254093 : CollatzResearch.WordTrace tailWord_3254093 prefixEnd_3254093 1670913803431242079872205 := by
  unfold tailWord_3254093
  simp only [CollatzResearch.WordTrace]
  refine ⟨118686522199984290683606933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79124348133322860455737955 118686522199984290683606933)
  ·
    refine ⟨5563430728124263625794075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 118686522199984290683606933 5563430728124263625794075)
    ·
      refine ⟨8345146092186395438691113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5563430728124263625794075 8345146092186395438691113)
      ·
        refine ⟨6258859569139796579018335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8345146092186395438691113 6258859569139796579018335)
        ·
          refine ⟨9388289353709694868527503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6258859569139796579018335 9388289353709694868527503)
          ·
            refine ⟨14082434030564542302791255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9388289353709694868527503 14082434030564542302791255)
            ·
              refine ⟨21123651045846813454186883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14082434030564542302791255 21123651045846813454186883)
              ·
                refine ⟨31685476568770220181280325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21123651045846813454186883 31685476568770220181280325)
                ·
                  refine ⟨5941026856644416283990061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31685476568770220181280325 5941026856644416283990061)
                  ·
                    refine ⟨2227885071241656106496273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5941026856644416283990061 2227885071241656106496273)
                    ·
                      refine ⟨1670913803431242079872205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2227885071241656106496273 1670913803431242079872205)
                      ·
                        rfl

theorem cell23_3254093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_3254093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254093 prefixEnd_3254093 := by exact prefixLift 3254093
  have htrace : WordTrace (prefixWord ++ tailWord_3254093) baseStart_3254093 baseEnd_3254093 := by
    simpa [prefixWord, tailWord_3254093, baseEnd_3254093] using wordTrace_append hprefix tailTrace_3254093
  have hstable : (prefixWord ++ tailWord_3254093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254093).length < 2 ^ (prefixWord ++ tailWord_3254093).sum := by decide
  have hdescent : baseEnd_3254093 < baseStart_3254093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254112 : List Nat := [2, 1, 1, 3, 3, 2, 1, 10]
def baseStart_3254112 : Nat := 118140960795 + 3254112 * 2 ^ 59
def prefixEnd_3254112 : Nat := 4983230072969 + 3 ^ 40 * 3254112 * 2
def baseEnd_3254112 : Nat := 61886057761617685390171

theorem tailTrace_3254112 : CollatzResearch.WordTrace tailWord_3254112 prefixEnd_3254112 61886057761617685390171 := by
  unfold tailWord_3254112
  simp only [CollatzResearch.WordTrace]
  refine ⟨59343607593457728464274295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79124810124610304619032393 59343607593457728464274295)
  ·
    refine ⟨89015411390186592696411443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59343607593457728464274295 89015411390186592696411443)
    ·
      refine ⟨133523117085279889044617165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89015411390186592696411443 133523117085279889044617165)
      ·
        refine ⟨50071168906979958391731437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133523117085279889044617165 50071168906979958391731437)
        ·
          refine ⟨18776688340117484396899289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50071168906979958391731437 18776688340117484396899289)
          ·
            refine ⟨14082516255088113297674467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18776688340117484396899289 14082516255088113297674467)
            ·
              refine ⟨21123774382632169946511701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14082516255088113297674467 21123774382632169946511701)
              ·
                refine ⟨61886057761617685390171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21123774382632169946511701 61886057761617685390171)
                ·
                  rfl

theorem cell23_3254112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 10].length) (baseStart_3254112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254112 prefixEnd_3254112 := by exact prefixLift 3254112
  have htrace : WordTrace (prefixWord ++ tailWord_3254112) baseStart_3254112 baseEnd_3254112 := by
    simpa [prefixWord, tailWord_3254112, baseEnd_3254112] using wordTrace_append hprefix tailTrace_3254112
  have hstable : (prefixWord ++ tailWord_3254112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254112).length < 2 ^ (prefixWord ++ tailWord_3254112).sum := by decide
  have hdescent : baseEnd_3254112 < baseStart_3254112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254119 : List Nat := [1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_3254119 : Nat := 118140960795 + 3254119 * 2 ^ 59
def prefixEnd_3254119 : Nat := 4983230072969 + 3 ^ 40 * 3254119 * 2
def baseEnd_3254119 : Nat := 1670927153928258978147085

theorem tailTrace_3254119 : CollatzResearch.WordTrace tailWord_3254119 prefixEnd_3254119 1670927153928258978147085 := by
  unfold tailWord_3254119
  simp only [CollatzResearch.WordTrace]
  refine ⟨118687470497890097124053411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79124980331926731416035607 118687470497890097124053411)
  ·
    refine ⟨178031205746835145686080117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118687470497890097124053411 178031205746835145686080117)
    ·
      refine ⟨16690425538765794908070011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178031205746835145686080117 16690425538765794908070011)
      ·
        refine ⟨25035638308148692362105017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16690425538765794908070011 25035638308148692362105017)
        ·
          refine ⟨18776728731111519271578763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25035638308148692362105017 18776728731111519271578763)
          ·
            refine ⟨28165093096667278907368145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18776728731111519271578763 28165093096667278907368145)
            ·
              refine ⟨21123819822500459180526109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28165093096667278907368145 21123819822500459180526109)
              ·
                refine ⟨7921432433437672192697291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21123819822500459180526109 7921432433437672192697291)
                ·
                  refine ⟨11882148650156508289045937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7921432433437672192697291 11882148650156508289045937)
                  ·
                    refine ⟨8911611487617381216784453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11882148650156508289045937 8911611487617381216784453)
                    ·
                      refine ⟨1670927153928258978147085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8911611487617381216784453 1670927153928258978147085)
                      ·
                        rfl

theorem cell23_3254119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_3254119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254119 prefixEnd_3254119 := by exact prefixLift 3254119
  have htrace : WordTrace (prefixWord ++ tailWord_3254119) baseStart_3254119 baseEnd_3254119 := by
    simpa [prefixWord, tailWord_3254119, baseEnd_3254119] using wordTrace_append hprefix tailTrace_3254119
  have hstable : (prefixWord ++ tailWord_3254119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254119).length < 2 ^ (prefixWord ++ tailWord_3254119).sum := by decide
  have hdescent : baseEnd_3254119 < baseStart_3254119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254173 : List Nat := [1, 4, 2, 1, 2, 2, 2, 3, 2, 1, 3]
def baseStart_3254173 : Nat := 118140960795 + 3254173 * 2 ^ 59
def prefixEnd_3254173 : Nat := 4983230072969 + 3 ^ 40 * 3254173 * 2
def baseEnd_3254173 : Nat := 1670954881883601766871837

theorem tailTrace_3254173 : CollatzResearch.WordTrace tailWord_3254173 prefixEnd_3254173 1670954881883601766871837 := by
  unfold tailWord_3254173
  simp only [CollatzResearch.WordTrace]
  refine ⟨118689440039694464346519173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79126293359796309564346115 118689440039694464346519173)
  ·
    refine ⟨22254270007442712064972345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118689440039694464346519173 22254270007442712064972345)
    ·
      refine ⟨16690702505582034048729259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22254270007442712064972345 16690702505582034048729259)
      ·
        refine ⟨25036053758373051073093889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16690702505582034048729259 25036053758373051073093889)
        ·
          refine ⟨18777040318779788304820417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25036053758373051073093889 18777040318779788304820417)
          ·
            refine ⟨14082780239084841228615313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18777040318779788304820417 14082780239084841228615313)
            ·
              refine ⟨10562085179313630921461485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14082780239084841228615313 10562085179313630921461485)
              ·
                refine ⟨3960781942242611595548057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10562085179313630921461485 3960781942242611595548057)
                ·
                  refine ⟨2970586456681958696661043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3960781942242611595548057 2970586456681958696661043)
                  ·
                    refine ⟨4455879685022938044991565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2970586456681958696661043 4455879685022938044991565)
                    ·
                      refine ⟨1670954881883601766871837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4455879685022938044991565 1670954881883601766871837)
                      ·
                        rfl

theorem cell23_3254173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_3254173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254173 prefixEnd_3254173 := by exact prefixLift 3254173
  have htrace : WordTrace (prefixWord ++ tailWord_3254173) baseStart_3254173 baseEnd_3254173 := by
    simpa [prefixWord, tailWord_3254173, baseEnd_3254173] using wordTrace_append hprefix tailTrace_3254173
  have hstable : (prefixWord ++ tailWord_3254173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254173).length < 2 ^ (prefixWord ++ tailWord_3254173).sum := by decide
  have hdescent : baseEnd_3254173 < baseStart_3254173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254183 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 3, 3, 2]
def baseStart_3254183 : Nat := 118140960795 + 3254183 * 2 ^ 59
def prefixEnd_3254183 : Nat := 4983230072969 + 3 ^ 40 * 3254183 * 2
def baseEnd_3254183 : Nat := 1670960016690146727746791

theorem tailTrace_3254183 : CollatzResearch.WordTrace tailWord_3254183 prefixEnd_3254183 1670960016690146727746791 := by
  unfold tailWord_3254183
  simp only [CollatzResearch.WordTrace]
  refine ⟨118689804769658236054383203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79126536513105490702922135 118689804769658236054383203)
  ·
    refine ⟨178034707154487354081574805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118689804769658236054383203 178034707154487354081574805)
    ·
      refine ⟨8345376897866594722573819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 178034707154487354081574805 8345376897866594722573819)
      ·
        refine ⟨12518065346799892083860729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8345376897866594722573819 12518065346799892083860729)
        ·
          refine ⟨9388549010099919062895547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12518065346799892083860729 9388549010099919062895547)
          ·
            refine ⟨14082823515149878594343321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9388549010099919062895547 14082823515149878594343321)
            ·
              refine ⟨10562117636362408945757491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14082823515149878594343321 10562117636362408945757491)
              ·
                refine ⟨15843176454543613418636237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10562117636362408945757491 15843176454543613418636237)
                ·
                  refine ⟨5941191170453855031988589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15843176454543613418636237 5941191170453855031988589)
                  ·
                    refine ⟨2227946688920195636995721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5941191170453855031988589 2227946688920195636995721)
                    ·
                      refine ⟨1670960016690146727746791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2227946688920195636995721 1670960016690146727746791)
                      ·
                        rfl

theorem cell23_3254183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_3254183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254183 prefixEnd_3254183 := by exact prefixLift 3254183
  have htrace : WordTrace (prefixWord ++ tailWord_3254183) baseStart_3254183 baseEnd_3254183 := by
    simpa [prefixWord, tailWord_3254183, baseEnd_3254183] using wordTrace_append hprefix tailTrace_3254183
  have hstable : (prefixWord ++ tailWord_3254183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254183).length < 2 ^ (prefixWord ++ tailWord_3254183).sum := by decide
  have hdescent : baseEnd_3254183 < baseStart_3254183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254213 : List Nat := [1, 3, 1, 1, 1, 1, 1, 8, 2, 2, 2]
def baseStart_3254213 : Nat := 118140960795 + 3254213 * 2 ^ 59
def prefixEnd_3254213 : Nat := 4983230072969 + 3 ^ 40 * 3254213 * 2
def baseEnd_3254213 : Nat := 1670975421109781610371653

theorem tailTrace_3254213 : CollatzResearch.WordTrace tailWord_3254213 prefixEnd_3254213 1670975421109781610371653 := by
  unfold tailWord_3254213
  simp only [CollatzResearch.WordTrace]
  refine ⟨118690898959549551177975293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79127265973033034118650195 118690898959549551177975293)
  ·
    refine ⟨44509087109831081691740735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118690898959549551177975293 44509087109831081691740735)
    ·
      refine ⟨66763630664746622537611103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44509087109831081691740735 66763630664746622537611103)
      ·
        refine ⟨100145445997119933806416655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66763630664746622537611103 100145445997119933806416655)
        ·
          refine ⟨150218168995679900709624983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100145445997119933806416655 150218168995679900709624983)
          ·
            refine ⟨225327253493519851064437475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150218168995679900709624983 225327253493519851064437475)
            ·
              refine ⟨337990880240279776596656213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225327253493519851064437475 337990880240279776596656213)
              ·
                refine ⟨3960830627815778631992065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 337990880240279776596656213 3960830627815778631992065)
                ·
                  refine ⟨2970622970861833973994049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3960830627815778631992065 2970622970861833973994049)
                  ·
                    refine ⟨2227967228146375480495537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2970622970861833973994049 2227967228146375480495537)
                    ·
                      refine ⟨1670975421109781610371653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2227967228146375480495537 1670975421109781610371653)
                      ·
                        rfl

theorem cell23_3254213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 2, 2].length) (baseStart_3254213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254213 prefixEnd_3254213 := by exact prefixLift 3254213
  have htrace : WordTrace (prefixWord ++ tailWord_3254213) baseStart_3254213 baseEnd_3254213 := by
    simpa [prefixWord, tailWord_3254213, baseEnd_3254213] using wordTrace_append hprefix tailTrace_3254213
  have hstable : (prefixWord ++ tailWord_3254213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254213).length < 2 ^ (prefixWord ++ tailWord_3254213).sum := by decide
  have hdescent : baseEnd_3254213 < baseStart_3254213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254219 : List Nat := [1, 1, 1, 1, 3, 4, 4, 1, 7]
def baseStart_3254219 : Nat := 118140960795 + 3254219 * 2 ^ 59
def prefixEnd_3254219 : Nat := 4983230072969 + 3 ^ 40 * 3254219 * 2
def baseEnd_3254219 : Nat := 185664277999300954099625

theorem tailTrace_3254219 : CollatzResearch.WordTrace tailWord_3254219 prefixEnd_3254219 185664277999300954099625 := by
  unfold tailWord_3254219
  simp only [CollatzResearch.WordTrace]
  refine ⟨118691117797527814202693711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79127411865018542801795807 118691117797527814202693711)
  ·
    refine ⟨178036676696291721304040567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118691117797527814202693711 178036676696291721304040567)
    ·
      refine ⟨267055015044437581956060851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178036676696291721304040567 267055015044437581956060851)
      ·
        refine ⟨400582522566656372934091277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267055015044437581956060851 400582522566656372934091277)
        ·
          refine ⟨150218445962496139850284229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400582522566656372934091277 150218445962496139850284229)
          ·
            refine ⟨28165958617968026221928293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150218445962496139850284229 28165958617968026221928293)
            ·
              refine ⟨5281117240869004916611555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28165958617968026221928293 5281117240869004916611555)
              ·
                refine ⟨7921675861303507374917333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5281117240869004916611555 7921675861303507374917333)
                ·
                  refine ⟨185664277999300954099625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7921675861303507374917333 185664277999300954099625)
                  ·
                    rfl

theorem cell23_3254219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 7].length) (baseStart_3254219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254219 prefixEnd_3254219 := by exact prefixLift 3254219
  have htrace : WordTrace (prefixWord ++ tailWord_3254219) baseStart_3254219 baseEnd_3254219 := by
    simpa [prefixWord, tailWord_3254219, baseEnd_3254219] using wordTrace_append hprefix tailTrace_3254219
  have hstable : (prefixWord ++ tailWord_3254219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254219).length < 2 ^ (prefixWord ++ tailWord_3254219).sum := by decide
  have hdescent : baseEnd_3254219 < baseStart_3254219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254286 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4]
def baseStart_3254286 : Nat := 118140960795 + 3254286 * 2 ^ 59
def prefixEnd_3254286 : Nat := 4983230072969 + 3 ^ 40 * 3254286 * 2
def baseEnd_3254286 : Nat := 1671012905197559824758817

theorem tailTrace_3254286 : CollatzResearch.WordTrace tailWord_3254286 prefixEnd_3254286 1671012905197559824758817 := by
  unfold tailWord_3254286
  simp only [CollatzResearch.WordTrace]
  refine ⟨14836695186035635580672839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79129040992190056430255141 14836695186035635580672839)
  ·
    refine ⟨22255042779053453371009259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14836695186035635580672839 22255042779053453371009259)
    ·
      refine ⟨33382564168580180056513889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22255042779053453371009259 33382564168580180056513889)
      ·
        refine ⟨25036923126435135042385417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33382564168580180056513889 25036923126435135042385417)
        ·
          refine ⟨18777692344826351281789063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25036923126435135042385417 18777692344826351281789063)
          ·
            refine ⟨28166538517239526922683595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18777692344826351281789063 28166538517239526922683595)
            ·
              refine ⟨42249807775859290384025393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28166538517239526922683595 42249807775859290384025393)
              ·
                refine ⟨31687355831894467788019045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42249807775859290384025393 31687355831894467788019045)
                ·
                  refine ⟨5941379218480212710253571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31687355831894467788019045 5941379218480212710253571)
                  ·
                    refine ⟨8912068827720319065380357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5941379218480212710253571 8912068827720319065380357)
                    ·
                      refine ⟨1671012905197559824758817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8912068827720319065380357 1671012905197559824758817)
                      ·
                        rfl

theorem cell23_3254286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_3254286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254286 prefixEnd_3254286 := by exact prefixLift 3254286
  have htrace : WordTrace (prefixWord ++ tailWord_3254286) baseStart_3254286 baseEnd_3254286 := by
    simpa [prefixWord, tailWord_3254286, baseEnd_3254286] using wordTrace_append hprefix tailTrace_3254286
  have hstable : (prefixWord ++ tailWord_3254286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254286).length < 2 ^ (prefixWord ++ tailWord_3254286).sum := by decide
  have hdescent : baseEnd_3254286 < baseStart_3254286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254296 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 5, 4]
def baseStart_3254296 : Nat := 118140960795 + 3254296 * 2 ^ 59
def prefixEnd_3254296 : Nat := 4983230072969 + 3 ^ 40 * 3254296 * 2
def baseEnd_3254296 : Nat := 557006013334701595211257

theorem tailTrace_3254296 : CollatzResearch.WordTrace tailWord_3254296 prefixEnd_3254296 557006013334701595211257 := by
  unfold tailWord_3254296
  simp only [CollatzResearch.WordTrace]
  refine ⟨59346963109124428176623371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79129284145499237568831161 59346963109124428176623371)
  ·
    refine ⟨89020444663686642264935057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59346963109124428176623371 89020444663686642264935057)
    ·
      refine ⟨66765333497764981698701293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89020444663686642264935057 66765333497764981698701293)
      ·
        refine ⟨25037000061661868137012985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66765333497764981698701293 25037000061661868137012985)
        ·
          refine ⟨18777750046246401102759739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25037000061661868137012985 18777750046246401102759739)
          ·
            refine ⟨28166625069369601654139609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18777750046246401102759739 28166625069369601654139609)
            ·
              refine ⟨21124968802027201240604707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28166625069369601654139609 21124968802027201240604707)
              ·
                refine ⟨31687453203040801860907061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21124968802027201240604707 31687453203040801860907061)
                ·
                  refine ⟨2970698737785075174460037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31687453203040801860907061 2970698737785075174460037)
                  ·
                    refine ⟨557006013334701595211257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2970698737785075174460037 557006013334701595211257)
                    ·
                      rfl

theorem cell23_3254296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 5, 4].length) (baseStart_3254296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254296 prefixEnd_3254296 := by exact prefixLift 3254296
  have htrace : WordTrace (prefixWord ++ tailWord_3254296) baseStart_3254296 baseEnd_3254296 := by
    simpa [prefixWord, tailWord_3254296, baseEnd_3254296] using wordTrace_append hprefix tailTrace_3254296
  have hstable : (prefixWord ++ tailWord_3254296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254296).length < 2 ^ (prefixWord ++ tailWord_3254296).sum := by decide
  have hdescent : baseEnd_3254296 < baseStart_3254296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254373 : List Nat := [1, 3, 1, 3, 2, 3, 1, 3, 1, 5]
def baseStart_3254373 : Nat := 118140960795 + 3254373 * 2 ^ 59
def prefixEnd_3254373 : Nat := 4983230072969 + 3 ^ 40 * 3254373 * 2
def baseEnd_3254373 : Nat := 557019192671500328123639

theorem tailTrace_3254373 : CollatzResearch.WordTrace tailWord_3254373 prefixEnd_3254373 557019192671500328123639 := by
  unfold tailWord_3254373
  simp only [CollatzResearch.WordTrace]
  refine ⟨118696734638969898503799773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79131156425979932335866515 118696734638969898503799773)
  ·
    refine ⟨44511275489613711938924915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118696734638969898503799773 44511275489613711938924915)
    ·
      refine ⟨66766913234420567908387373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44511275489613711938924915 66766913234420567908387373)
      ·
        refine ⟨25037592462907712965645265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66766913234420567908387373 25037592462907712965645265)
        ·
          refine ⟨18778194347180784724233949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25037592462907712965645265 18778194347180784724233949)
          ·
            refine ⟨7041822880192794271587731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18778194347180784724233949 7041822880192794271587731)
            ·
              refine ⟨10562734320289191407381597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7041822880192794271587731 10562734320289191407381597)
              ·
                refine ⟨3961025370108446777768099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10562734320289191407381597 3961025370108446777768099)
                ·
                  refine ⟨5941538055162670166652149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3961025370108446777768099 5941538055162670166652149)
                  ·
                    refine ⟨557019192671500328123639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5941538055162670166652149 557019192671500328123639)
                    ·
                      rfl

theorem cell23_3254373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 5].length) (baseStart_3254373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254373 prefixEnd_3254373 := by exact prefixLift 3254373
  have htrace : WordTrace (prefixWord ++ tailWord_3254373) baseStart_3254373 baseEnd_3254373 := by
    simpa [prefixWord, tailWord_3254373, baseEnd_3254373] using wordTrace_append hprefix tailTrace_3254373
  have hstable : (prefixWord ++ tailWord_3254373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254373).length < 2 ^ (prefixWord ++ tailWord_3254373).sum := by decide
  have hdescent : baseEnd_3254373 < baseStart_3254373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254396 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 3, 1, 5]
def baseStart_3254396 : Nat := 118140960795 + 3254396 * 2 ^ 59
def prefixEnd_3254396 : Nat := 4983230072969 + 3 ^ 40 * 3254396 * 2
def baseEnd_3254396 : Nat := 1671069388069554394383311

theorem tailTrace_3254396 : CollatzResearch.WordTrace tailWord_3254396 prefixEnd_3254396 1671069388069554394383311 := by
  unfold tailWord_3254396
  simp only [CollatzResearch.WordTrace]
  refine ⟨59348786758943286715943521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79131715678591048954591361 59348786758943286715943521)
  ·
    refine ⟨44511590069207465036957641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59348786758943286715943521 44511590069207465036957641)
    ·
      refine ⟨33383692551905598777718231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44511590069207465036957641 33383692551905598777718231)
      ·
        refine ⟨50075538827858398166577347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33383692551905598777718231 50075538827858398166577347)
        ·
          refine ⟨75113308241787597249866021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50075538827858398166577347 75113308241787597249866021)
          ·
            refine ⟨14083745295335174484349879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75113308241787597249866021 14083745295335174484349879)
            ·
              refine ⟨21125617943002761726524819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14083745295335174484349879 21125617943002761726524819)
              ·
                refine ⟨31688426914504142589787229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21125617943002761726524819 31688426914504142589787229)
                ·
                  refine ⟨11883160092939053471170211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31688426914504142589787229 11883160092939053471170211)
                  ·
                    refine ⟨17824740139408580206755317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11883160092939053471170211 17824740139408580206755317)
                    ·
                      refine ⟨1671069388069554394383311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17824740139408580206755317 1671069388069554394383311)
                      ·
                        rfl

theorem cell23_3254396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_3254396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254396 prefixEnd_3254396 := by exact prefixLift 3254396
  have htrace : WordTrace (prefixWord ++ tailWord_3254396) baseStart_3254396 baseEnd_3254396 := by
    simpa [prefixWord, tailWord_3254396, baseEnd_3254396] using wordTrace_append hprefix tailTrace_3254396
  have hstable : (prefixWord ++ tailWord_3254396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254396).length < 2 ^ (prefixWord ++ tailWord_3254396).sum := by decide
  have hdescent : baseEnd_3254396 < baseStart_3254396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254403 : List Nat := [1, 1, 1, 3, 3, 5, 1, 1, 1, 6]
def baseStart_3254403 : Nat := 118140960795 + 3254403 * 2 ^ 59
def prefixEnd_3254403 : Nat := 4983230072969 + 3 ^ 40 * 3254403 * 2
def baseEnd_3254403 : Nat := 557024327478045288998593

theorem tailTrace_3254403 : CollatzResearch.WordTrace tailWord_3254403 prefixEnd_3254403 557024327478045288998593 := by
  unfold tailWord_3254403
  simp only [CollatzResearch.WordTrace]
  refine ⟨118697828828861213627391863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79131885885907475751594575 118697828828861213627391863)
  ·
    refine ⟨178046743243291820441087795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118697828828861213627391863 178046743243291820441087795)
    ·
      refine ⟨267070114864937730661631693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178046743243291820441087795 267070114864937730661631693)
      ·
        refine ⟨100151293074351648998111885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267070114864937730661631693 100151293074351648998111885)
        ·
          refine ⟨37556734902881868374291957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100151293074351648998111885 37556734902881868374291957)
          ·
            refine ⟨3520943897145175160089871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37556734902881868374291957 3520943897145175160089871)
            ·
              refine ⟨5281415845717762740134807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3520943897145175160089871 5281415845717762740134807)
              ·
                refine ⟨7922123768576644110202211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5281415845717762740134807 7922123768576644110202211)
                ·
                  refine ⟨11883185652864966165303317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7922123768576644110202211 11883185652864966165303317)
                  ·
                    refine ⟨557024327478045288998593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11883185652864966165303317 557024327478045288998593)
                    ·
                      rfl

theorem cell23_3254403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 6].length) (baseStart_3254403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254403 prefixEnd_3254403 := by exact prefixLift 3254403
  have htrace : WordTrace (prefixWord ++ tailWord_3254403) baseStart_3254403 baseEnd_3254403 := by
    simpa [prefixWord, tailWord_3254403, baseEnd_3254403] using wordTrace_append hprefix tailTrace_3254403
  have hstable : (prefixWord ++ tailWord_3254403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254403).length < 2 ^ (prefixWord ++ tailWord_3254403).sum := by decide
  have hdescent : baseEnd_3254403 < baseStart_3254403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254410 : List Nat := [3, 1, 2, 3, 1, 3, 2, 2, 1, 1, 4]
def baseStart_3254410 : Nat := 118140960795 + 3254410 * 2 ^ 59
def prefixEnd_3254410 : Nat := 4983230072969 + 3 ^ 40 * 3254410 * 2
def baseEnd_3254410 : Nat := 1671076576798717339608247

theorem tailTrace_3254410 : CollatzResearch.WordTrace tailWord_3254410 prefixEnd_3254410 1671076576798717339608247 := by
  unfold tailWord_3254410
  simp only [CollatzResearch.WordTrace]
  refine ⟨29674521034958963455724171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79132056093223902548597789 29674521034958963455724171)
  ·
    refine ⟨44511781552438445183586257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29674521034958963455724171 44511781552438445183586257)
    ·
      refine ⟨33383836164328833887689693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44511781552438445183586257 33383836164328833887689693)
      ·
        refine ⟨12518938561623312707883635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33383836164328833887689693 12518938561623312707883635)
        ·
          refine ⟨18778407842434969061825453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12518938561623312707883635 18778407842434969061825453)
          ·
            refine ⟨7041902940913113398184545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18778407842434969061825453 7041902940913113398184545)
            ·
              refine ⟨5281427205684835048638409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7041902940913113398184545 5281427205684835048638409)
              ·
                refine ⟨3961070404263626286478807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5281427205684835048638409 3961070404263626286478807)
                ·
                  refine ⟨5941605606395439429718211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3961070404263626286478807 5941605606395439429718211)
                  ·
                    refine ⟨8912408409593159144577317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5941605606395439429718211 8912408409593159144577317)
                    ·
                      refine ⟨1671076576798717339608247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8912408409593159144577317 1671076576798717339608247)
                      ·
                        rfl

theorem cell23_3254410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_3254410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254410 prefixEnd_3254410 := by exact prefixLift 3254410
  have htrace : WordTrace (prefixWord ++ tailWord_3254410) baseStart_3254410 baseEnd_3254410 := by
    simpa [prefixWord, tailWord_3254410, baseEnd_3254410] using wordTrace_append hprefix tailTrace_3254410
  have hstable : (prefixWord ++ tailWord_3254410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254410).length < 2 ^ (prefixWord ++ tailWord_3254410).sum := by decide
  have hdescent : baseEnd_3254410 < baseStart_3254410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254540 : List Nat := [2, 2, 1, 2, 2, 2, 4, 3, 5]
def baseStart_3254540 : Nat := 118140960795 + 3254540 * 2 ^ 59
def prefixEnd_3254540 : Nat := 4983230072969 + 3 ^ 40 * 3254540 * 2
def baseEnd_3254540 : Nat := 185682592142644647886961

theorem tailTrace_3254540 : CollatzResearch.WordTrace tailWord_3254540 prefixEnd_3254540 185682592142644647886961 := by
  unfold tailWord_3254540
  simp only [CollatzResearch.WordTrace]
  refine ⟨59351412814682443012564537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79135217086243257350086049 59351412814682443012564537)
  ·
    refine ⟨44513559611011832259423403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59351412814682443012564537 44513559611011832259423403)
    ·
      refine ⟨66770339416517748389135105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44513559611011832259423403 66770339416517748389135105)
      ·
        refine ⟨50077754562388311291851329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66770339416517748389135105 50077754562388311291851329)
        ·
          refine ⟨37558315921791233468888497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50077754562388311291851329 37558315921791233468888497)
          ·
            refine ⟨28168736941343425101666373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37558315921791233468888497 28168736941343425101666373)
            ·
              refine ⟨5281638176501892206562445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28168736941343425101666373 5281638176501892206562445)
              ·
                refine ⟨1980614316188209577460917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5281638176501892206562445 1980614316188209577460917)
                ·
                  refine ⟨185682592142644647886961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1980614316188209577460917 185682592142644647886961)
                  ·
                    rfl

theorem cell23_3254540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 5].length) (baseStart_3254540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254540 prefixEnd_3254540 := by exact prefixLift 3254540
  have htrace : WordTrace (prefixWord ++ tailWord_3254540) baseStart_3254540 baseEnd_3254540 := by
    simpa [prefixWord, tailWord_3254540, baseEnd_3254540] using wordTrace_append hprefix tailTrace_3254540
  have hstable : (prefixWord ++ tailWord_3254540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254540).length < 2 ^ (prefixWord ++ tailWord_3254540).sum := by decide
  have hdescent : baseEnd_3254540 < baseStart_3254540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254590 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_3254590 : Nat := 118140960795 + 3254590 * 2 ^ 59
def prefixEnd_3254590 : Nat := 4983230072969 + 3 ^ 40 * 3254590 * 2
def baseEnd_3254590 : Nat := 1671169003316526635357419

theorem tailTrace_3254590 : CollatzResearch.WordTrace tailWord_3254590 prefixEnd_3254590 1671169003316526635357419 := by
  unfold tailWord_3254590
  simp only [CollatzResearch.WordTrace]
  refine ⟨14838081159897968070556153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79136432852789163042966149 14838081159897968070556153)
  ·
    refine ⟨11128560869923476052917115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14838081159897968070556153 11128560869923476052917115)
    ·
      refine ⟨16692841304885214079375673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11128560869923476052917115 16692841304885214079375673)
      ·
        refine ⟨12519630978663910559531755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16692841304885214079375673 12519630978663910559531755)
        ·
          refine ⟨18779446467995865839297633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12519630978663910559531755 18779446467995865839297633)
          ·
            refine ⟨14084584850996899379473225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18779446467995865839297633 14084584850996899379473225)
            ·
              refine ⟨10563438638247674534604919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14084584850996899379473225 10563438638247674534604919)
              ·
                refine ⟨15845157957371511801907379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10563438638247674534604919 15845157957371511801907379)
                ·
                  refine ⟨23767736936057267702861069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15845157957371511801907379 23767736936057267702861069)
                  ·
                    refine ⟨8912901351021475388572901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23767736936057267702861069 8912901351021475388572901)
                    ·
                      refine ⟨1671169003316526635357419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8912901351021475388572901 1671169003316526635357419)
                      ·
                        rfl

theorem cell23_3254590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_3254590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254590 prefixEnd_3254590 := by exact prefixLift 3254590
  have htrace : WordTrace (prefixWord ++ tailWord_3254590) baseStart_3254590 baseEnd_3254590 := by
    simpa [prefixWord, tailWord_3254590, baseEnd_3254590] using wordTrace_append hprefix tailTrace_3254590
  have hstable : (prefixWord ++ tailWord_3254590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254590).length < 2 ^ (prefixWord ++ tailWord_3254590).sum := by decide
  have hdescent : baseEnd_3254590 < baseStart_3254590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254610 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3]
def baseStart_3254610 : Nat := 118140960795 + 3254610 * 2 ^ 59
def prefixEnd_3254610 : Nat := 4983230072969 + 3 ^ 40 * 3254610 * 2
def baseEnd_3254610 : Nat := 1671179272929616557107327

theorem tailTrace_3254610 : CollatzResearch.WordTrace tailWord_3254610 prefixEnd_3254610 1671179272929616557107327 := by
  unfold tailWord_3254610
  simp only [CollatzResearch.WordTrace]
  refine ⟨29676344684777821995044321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79136919159407525320118189 29676344684777821995044321)
  ·
    refine ⟨22257258513583366496283241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29676344684777821995044321 22257258513583366496283241)
    ·
      refine ⟨16692943885187524872212431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22257258513583366496283241 16692943885187524872212431)
      ·
        refine ⟨25039415827781287308318647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16692943885187524872212431 25039415827781287308318647)
        ·
          refine ⟨37559123741671930962477971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25039415827781287308318647 37559123741671930962477971)
          ·
            refine ⟨56338685612507896443716957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37559123741671930962477971 56338685612507896443716957)
            ·
              refine ⟨21127007104690461166393859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56338685612507896443716957 21127007104690461166393859)
              ·
                refine ⟨31690510657035691749590789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21127007104690461166393859 31690510657035691749590789)
                ·
                  refine ⟨5941970748194192203048273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31690510657035691749590789 5941970748194192203048273)
                  ·
                    refine ⟨4456478061145644152286205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5941970748194192203048273 4456478061145644152286205)
                    ·
                      refine ⟨1671179272929616557107327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4456478061145644152286205 1671179272929616557107327)
                      ·
                        rfl

theorem cell23_3254610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_3254610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254610 prefixEnd_3254610 := by exact prefixLift 3254610
  have htrace : WordTrace (prefixWord ++ tailWord_3254610) baseStart_3254610 baseEnd_3254610 := by
    simpa [prefixWord, tailWord_3254610, baseEnd_3254610] using wordTrace_append hprefix tailTrace_3254610
  have hstable : (prefixWord ++ tailWord_3254610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254610).length < 2 ^ (prefixWord ++ tailWord_3254610).sum := by decide
  have hdescent : baseEnd_3254610 < baseStart_3254610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254643 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 3, 5]
def baseStart_3254643 : Nat := 118140960795 + 3254643 * 2 ^ 59
def prefixEnd_3254643 : Nat := 4983230072969 + 3 ^ 40 * 3254643 * 2
def baseEnd_3254643 : Nat := 557065405930404975998225

theorem tailTrace_3254643 : CollatzResearch.WordTrace tailWord_3254643 prefixEnd_3254643 557065405930404975998225 := by
  unfold tailWord_3254643
  simp only [CollatzResearch.WordTrace]
  refine ⟨118706582347991734616128583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79137721565327823077419055 118706582347991734616128583)
  ·
    refine ⟨178059873521987601924192875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118706582347991734616128583 178059873521987601924192875)
    ·
      refine ⟨267089810282981402886289313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178059873521987601924192875 267089810282981402886289313)
      ·
        refine ⟨200317357712236052164716985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267089810282981402886289313 200317357712236052164716985)
        ·
          refine ⟨150238018284177039123537739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200317357712236052164716985 150238018284177039123537739)
          ·
            refine ⟨225357027426265558685306609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150238018284177039123537739 225357027426265558685306609)
            ·
              refine ⟨169017770569699169013979957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225357027426265558685306609 169017770569699169013979957)
              ·
                refine ⟨15845415990909297095060621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169017770569699169013979957 15845415990909297095060621)
                ·
                  refine ⟨5942030996590986410647733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15845415990909297095060621 5942030996590986410647733)
                  ·
                    refine ⟨557065405930404975998225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5942030996590986410647733 557065405930404975998225)
                    ·
                      rfl

theorem cell23_3254643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 5].length) (baseStart_3254643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254643 prefixEnd_3254643 := by exact prefixLift 3254643
  have htrace : WordTrace (prefixWord ++ tailWord_3254643) baseStart_3254643 baseEnd_3254643 := by
    simpa [prefixWord, tailWord_3254643, baseEnd_3254643] using wordTrace_append hprefix tailTrace_3254643
  have hstable : (prefixWord ++ tailWord_3254643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254643).length < 2 ^ (prefixWord ++ tailWord_3254643).sum := by decide
  have hdescent : baseEnd_3254643 < baseStart_3254643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254667 : List Nat := [1, 1, 1, 1, 4, 4, 2, 2, 2, 3, 2]
def baseStart_3254667 : Nat := 118140960795 + 3254667 * 2 ^ 59
def prefixEnd_3254667 : Nat := 4983230072969 + 3 ^ 40 * 3254667 * 2
def baseEnd_3254667 : Nat := 1671208541326922834094565

theorem tailTrace_3254667 : CollatzResearch.WordTrace tailWord_3254667 prefixEnd_3254667 1671208541326922834094565 := by
  unfold tailWord_3254667
  simp only [CollatzResearch.WordTrace]
  refine ⟨118707457699904786715002255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79138305133269857810001503 118707457699904786715002255)
  ·
    refine ⟨178061186549857180072503383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118707457699904786715002255 178061186549857180072503383)
    ·
      refine ⟨267091779824785770108755075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178061186549857180072503383 267091779824785770108755075)
      ·
        refine ⟨400637669737178655163132613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267091779824785770108755075 400637669737178655163132613)
        ·
          refine ⟨75119563075720997843087365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 400637669737178655163132613 75119563075720997843087365)
          ·
            refine ⟨14084918076697687095578881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75119563075720997843087365 14084918076697687095578881)
            ·
              refine ⟨10563688557523265321684161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14084918076697687095578881 10563688557523265321684161)
              ·
                refine ⟨7922766418142448991263121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10563688557523265321684161 7922766418142448991263121)
                ·
                  refine ⟨5942074813606836743447341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7922766418142448991263121 5942074813606836743447341)
                  ·
                    refine ⟨2228278055102563778792753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5942074813606836743447341 2228278055102563778792753)
                    ·
                      refine ⟨1671208541326922834094565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2228278055102563778792753 1671208541326922834094565)
                      ·
                        rfl

theorem cell23_3254667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 3, 2].length) (baseStart_3254667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254667 prefixEnd_3254667 := by exact prefixLift 3254667
  have htrace : WordTrace (prefixWord ++ tailWord_3254667) baseStart_3254667 baseEnd_3254667 := by
    simpa [prefixWord, tailWord_3254667, baseEnd_3254667] using wordTrace_append hprefix tailTrace_3254667
  have hstable : (prefixWord ++ tailWord_3254667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254667).length < 2 ^ (prefixWord ++ tailWord_3254667).sum := by decide
  have hdescent : baseEnd_3254667 < baseStart_3254667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254723 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 6]
def baseStart_3254723 : Nat := 118140960795 + 3254723 * 2 ^ 59
def prefixEnd_3254723 : Nat := 4983230072969 + 3 ^ 40 * 3254723 * 2
def baseEnd_3254723 : Nat := 1671237296243574614994307

theorem tailTrace_3254723 : CollatzResearch.WordTrace tailWord_3254723 prefixEnd_3254723 1671237296243574614994307 := by
  unfold tailWord_3254723
  simp only [CollatzResearch.WordTrace]
  refine ⟨118709500187701908279040823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79139666791801272186027215 118709500187701908279040823)
  ·
    refine ⟨178064250281552862418561235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118709500187701908279040823 178064250281552862418561235)
    ·
      refine ⟨267096375422329293627841853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178064250281552862418561235 267096375422329293627841853)
      ·
        refine ⟨100161140783373485110440695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267096375422329293627841853 100161140783373485110440695)
        ·
          refine ⟨150241711175060227665661043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100161140783373485110440695 150241711175060227665661043)
          ·
            refine ⟨225362566762590341498491565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150241711175060227665661043 225362566762590341498491565)
            ·
              refine ⟨84510962535971378061934337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225362566762590341498491565 84510962535971378061934337)
              ·
                refine ⟨63383221901978533546450753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84510962535971378061934337 63383221901978533546450753)
                ·
                  refine ⟨47537416426483900159838065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63383221901978533546450753 47537416426483900159838065)
                  ·
                    refine ⟨35653062319862925119878549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47537416426483900159838065 35653062319862925119878549)
                    ·
                      refine ⟨1671237296243574614994307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35653062319862925119878549 1671237296243574614994307)
                      ·
                        rfl

theorem cell23_3254723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_3254723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254723 prefixEnd_3254723 := by exact prefixLift 3254723
  have htrace : WordTrace (prefixWord ++ tailWord_3254723) baseStart_3254723 baseEnd_3254723 := by
    simpa [prefixWord, tailWord_3254723, baseEnd_3254723] using wordTrace_append hprefix tailTrace_3254723
  have hstable : (prefixWord ++ tailWord_3254723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254723).length < 2 ^ (prefixWord ++ tailWord_3254723).sum := by decide
  have hdescent : baseEnd_3254723 < baseStart_3254723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254724 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 4, 4]
def baseStart_3254724 : Nat := 118140960795 + 3254724 * 2 ^ 59
def prefixEnd_3254724 : Nat := 4983230072969 + 3 ^ 40 * 3254724 * 2
def baseEnd_3254724 : Nat := 557079269908076370360601

theorem tailTrace_3254724 : CollatzResearch.WordTrace tailWord_3254724 prefixEnd_3254724 557079269908076370360601 := by
  unfold tailWord_3254724
  simp only [CollatzResearch.WordTrace]
  refine ⟨59354768330349142724913613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79139691107132190299884817 59354768330349142724913613)
  ·
    refine ⟨22258038123880928521842605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59354768330349142724913613 22258038123880928521842605)
    ·
      refine ⟨8346764296455348195690977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22258038123880928521842605 8346764296455348195690977)
      ·
        refine ⟨6260073222341511146768233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8346764296455348195690977 6260073222341511146768233)
        ·
          refine ⟨4695054916756133360076175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6260073222341511146768233 4695054916756133360076175)
          ·
            refine ⟨7042582375134200040114263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4695054916756133360076175 7042582375134200040114263)
            ·
              refine ⟨10563873562701300060171395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7042582375134200040114263 10563873562701300060171395)
              ·
                refine ⟨15845810344051950090257093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10563873562701300060171395 15845810344051950090257093)
                ·
                  refine ⟨2971089439509740641923205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15845810344051950090257093 2971089439509740641923205)
                  ·
                    refine ⟨557079269908076370360601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2971089439509740641923205 557079269908076370360601)
                    ·
                      rfl

theorem cell23_3254724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_3254724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254724 prefixEnd_3254724 := by exact prefixLift 3254724
  have htrace : WordTrace (prefixWord ++ tailWord_3254724) baseStart_3254724 baseEnd_3254724 := by
    simpa [prefixWord, tailWord_3254724, baseEnd_3254724] using wordTrace_append hprefix tailTrace_3254724
  have hstable : (prefixWord ++ tailWord_3254724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254724).length < 2 ^ (prefixWord ++ tailWord_3254724).sum := by decide
  have hdescent : baseEnd_3254724 < baseStart_3254724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254754 : List Nat := [3, 3, 3, 2, 1, 1, 1, 9]
def baseStart_3254754 : Nat := 118140960795 + 3254754 * 2 ^ 59
def prefixEnd_3254754 : Nat := 4983230072969 + 3 ^ 40 * 3254754 * 2
def baseEnd_3254754 : Nat := 61898267190513481248395

theorem tailTrace_3254754 : CollatzResearch.WordTrace tailWord_3254754 prefixEnd_3254754 61898267190513481248395 := by
  unfold tailWord_3254754
  simp only [CollatzResearch.WordTrace]
  refine ⟨29677657712647400143354829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79140420567059733715612877 29677657712647400143354829)
  ·
    refine ⟨11129121642242775053758061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29677657712647400143354829 11129121642242775053758061)
    ·
      refine ⟨4173420615841040645159273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11129121642242775053758061 4173420615841040645159273)
      ·
        refine ⟨3130065461880780483869455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4173420615841040645159273 3130065461880780483869455)
        ·
          refine ⟨4695098192821170725804183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3130065461880780483869455 4695098192821170725804183)
          ·
            refine ⟨7042647289231756088706275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4695098192821170725804183 7042647289231756088706275)
            ·
              refine ⟨10563970933847634133059413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7042647289231756088706275 10563970933847634133059413)
              ·
                refine ⟨61898267190513481248395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10563970933847634133059413 61898267190513481248395)
                ·
                  rfl

theorem cell23_3254754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 9].length) (baseStart_3254754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254754 prefixEnd_3254754 := by exact prefixLift 3254754
  have htrace : WordTrace (prefixWord ++ tailWord_3254754) baseStart_3254754 baseEnd_3254754 := by
    simpa [prefixWord, tailWord_3254754, baseEnd_3254754] using wordTrace_append hprefix tailTrace_3254754
  have hstable : (prefixWord ++ tailWord_3254754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254754).length < 2 ^ (prefixWord ++ tailWord_3254754).sum := by decide
  have hdescent : baseEnd_3254754 < baseStart_3254754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254760 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_3254760 : Nat := 118140960795 + 3254760 * 2 ^ 59
def prefixEnd_3254760 : Nat := 4983230072969 + 3 ^ 40 * 3254760 * 2
def baseEnd_3254760 : Nat := 1671256295027790970231637

theorem tailTrace_3254760 : CollatzResearch.WordTrace tailWord_3254760 prefixEnd_3254760 1671256295027790970231637 := by
  unfold tailWord_3254760
  simp only [CollatzResearch.WordTrace]
  refine ⟨59355424844283931799068867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79140566459045242398758489 59355424844283931799068867)
  ·
    refine ⟨89033137266425897698603301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59355424844283931799068867 89033137266425897698603301)
    ·
      refine ⟨16693713237454855818488119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89033137266425897698603301 16693713237454855818488119)
      ·
        refine ⟨25040569856182283727732179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16693713237454855818488119 25040569856182283727732179)
        ·
          refine ⟨37560854784273425591598269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25040569856182283727732179 37560854784273425591598269)
          ·
            refine ⟨14085320544102534596849351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37560854784273425591598269 14085320544102534596849351)
            ·
              refine ⟨21127980816153801895274027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14085320544102534596849351 21127980816153801895274027)
              ·
                refine ⟨31691971224230702842911041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21127980816153801895274027 31691971224230702842911041)
                ·
                  refine ⟨23768978418173027132183281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31691971224230702842911041 23768978418173027132183281)
                  ·
                    refine ⟨17826733813629770349137461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23768978418173027132183281 17826733813629770349137461)
                    ·
                      refine ⟨1671256295027790970231637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17826733813629770349137461 1671256295027790970231637)
                      ·
                        rfl

theorem cell23_3254760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_3254760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254760 prefixEnd_3254760 := by exact prefixLift 3254760
  have htrace : WordTrace (prefixWord ++ tailWord_3254760) baseStart_3254760 baseEnd_3254760 := by
    simpa [prefixWord, tailWord_3254760, baseEnd_3254760] using wordTrace_append hprefix tailTrace_3254760
  have hstable : (prefixWord ++ tailWord_3254760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254760).length < 2 ^ (prefixWord ++ tailWord_3254760).sum := by decide
  have hdescent : baseEnd_3254760 < baseStart_3254760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254765 : List Nat := [1, 5, 1, 3, 1, 3, 1, 3, 1, 2, 2]
def baseStart_3254765 : Nat := 118140960795 + 3254765 * 2 ^ 59
def prefixEnd_3254765 : Nat := 4983230072969 + 3 ^ 40 * 3254765 * 2
def baseEnd_3254765 : Nat := 1671258862431063450669115

theorem tailTrace_3254765 : CollatzResearch.WordTrace tailWord_3254765 prefixEnd_3254765 1671258862431063450669115 := by
  unfold tailWord_3254765
  simp only [CollatzResearch.WordTrace]
  refine ⟨118711032053549749452069749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79140688035699832968046499 118711032053549749452069749)
  ·
    refine ⟨11129159255020289011131539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118711032053549749452069749 11129159255020289011131539)
    ·
      refine ⟨16693738882530433516697309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11129159255020289011131539 16693738882530433516697309)
      ·
        refine ⟨6260152080948912568761491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16693738882530433516697309 6260152080948912568761491)
        ·
          refine ⟨9390228121423368853142237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6260152080948912568761491 9390228121423368853142237)
          ·
            refine ⟨3521335545533763319928339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9390228121423368853142237 3521335545533763319928339)
            ·
              refine ⟨5282003318300644979892509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3521335545533763319928339 5282003318300644979892509)
              ·
                refine ⟨1980751244362741867459691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5282003318300644979892509 1980751244362741867459691)
                ·
                  refine ⟨2971126866544112801189537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1980751244362741867459691 2971126866544112801189537)
                  ·
                    refine ⟨2228345149908084600892153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2971126866544112801189537 2228345149908084600892153)
                    ·
                      refine ⟨1671258862431063450669115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2228345149908084600892153 1671258862431063450669115)
                      ·
                        rfl

theorem cell23_3254765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_3254765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254765 prefixEnd_3254765 := by exact prefixLift 3254765
  have htrace : WordTrace (prefixWord ++ tailWord_3254765) baseStart_3254765 baseEnd_3254765 := by
    simpa [prefixWord, tailWord_3254765, baseEnd_3254765] using wordTrace_append hprefix tailTrace_3254765
  have hstable : (prefixWord ++ tailWord_3254765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254765).length < 2 ^ (prefixWord ++ tailWord_3254765).sum := by decide
  have hdescent : baseEnd_3254765 < baseStart_3254765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254798 : List Nat := [4, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3]
def baseStart_3254798 : Nat := 118140960795 + 3254798 * 2 ^ 59
def prefixEnd_3254798 : Nat := 4983230072969 + 3 ^ 40 * 3254798 * 2
def baseEnd_3254798 : Nat := 1671275807292661821556463

theorem tailTrace_3254798 : CollatzResearch.WordTrace tailWord_3254798 prefixEnd_3254798 1671275807292661821556463 := by
  unfold tailWord_3254798
  simp only [CollatzResearch.WordTrace]
  refine ⟨14839029457803774511002631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79141490441620130725347365 14839029457803774511002631)
  ·
    refine ⟨22258544186705661766503947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14839029457803774511002631 22258544186705661766503947)
    ·
      refine ⟨33387816280058492649755921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22258544186705661766503947 33387816280058492649755921)
      ·
        refine ⟨25040862210043869487316941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33387816280058492649755921 25040862210043869487316941)
        ·
          refine ⟨9390323328766451057743853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25040862210043869487316941 9390323328766451057743853)
          ·
            refine ⟨3521371248287419146653945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9390323328766451057743853 3521371248287419146653945)
            ·
              refine ⟨2641028436215564359990459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3521371248287419146653945 2641028436215564359990459)
              ·
                refine ⟨3961542654323346539985689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2641028436215564359990459 3961542654323346539985689)
                ·
                  refine ⟨2971156990742509904989267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3961542654323346539985689 2971156990742509904989267)
                  ·
                    refine ⟨4456735486113764857483901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2971156990742509904989267 4456735486113764857483901)
                    ·
                      refine ⟨1671275807292661821556463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4456735486113764857483901 1671275807292661821556463)
                      ·
                        rfl

theorem cell23_3254798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_3254798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254798 prefixEnd_3254798 := by exact prefixLift 3254798
  have htrace : WordTrace (prefixWord ++ tailWord_3254798) baseStart_3254798 baseEnd_3254798 := by
    simpa [prefixWord, tailWord_3254798, baseEnd_3254798] using wordTrace_append hprefix tailTrace_3254798
  have hstable : (prefixWord ++ tailWord_3254798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254798).length < 2 ^ (prefixWord ++ tailWord_3254798).sum := by decide
  have hdescent : baseEnd_3254798 < baseStart_3254798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254810 : List Nat := [3, 1, 1, 3, 1, 1, 2, 4, 7]
def baseStart_3254810 : Nat := 118140960795 + 3254810 * 2 ^ 59
def prefixEnd_3254810 : Nat := 4983230072969 + 3 ^ 40 * 3254810 * 2
def baseEnd_3254810 : Nat := 185697996562279530511823

theorem tailTrace_3254810 : CollatzResearch.WordTrace tailWord_3254810 prefixEnd_3254810 185697996562279530511823 := by
  unfold tailWord_3254810
  simp only [CollatzResearch.WordTrace]
  refine ⟨29678168334596680534364471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79141782225591148091638589 29678168334596680534364471)
  ·
    refine ⟨44517252501895020801546707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29678168334596680534364471 44517252501895020801546707)
    ·
      refine ⟨66775878752842531202320061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44517252501895020801546707 66775878752842531202320061)
      ·
        refine ⟨25040954532315949200870023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66775878752842531202320061 25040954532315949200870023)
        ·
          refine ⟨37561431798473923801305035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25040954532315949200870023 37561431798473923801305035)
          ·
            refine ⟨56342147697710885701957553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37561431798473923801305035 56342147697710885701957553)
            ·
              refine ⟨42256610773283164276468165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56342147697710885701957553 42256610773283164276468165)
              ·
                refine ⟨7923114519990593301837781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42256610773283164276468165 7923114519990593301837781)
                ·
                  refine ⟨185697996562279530511823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7923114519990593301837781 185697996562279530511823)
                  ·
                    rfl

theorem cell23_3254810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 7].length) (baseStart_3254810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254810 prefixEnd_3254810 := by exact prefixLift 3254810
  have htrace : WordTrace (prefixWord ++ tailWord_3254810) baseStart_3254810 baseEnd_3254810 := by
    simpa [prefixWord, tailWord_3254810, baseEnd_3254810] using wordTrace_append hprefix tailTrace_3254810
  have hstable : (prefixWord ++ tailWord_3254810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254810).length < 2 ^ (prefixWord ++ tailWord_3254810).sum := by decide
  have hdescent : baseEnd_3254810 < baseStart_3254810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254837 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 2, 3, 3]
def baseStart_3254837 : Nat := 118140960795 + 3254837 * 2 ^ 59
def prefixEnd_3254837 : Nat := 4983230072969 + 3 ^ 40 * 3254837 * 2
def baseEnd_3254837 : Nat := 1671295833038187168968783

theorem tailTrace_3254837 : CollatzResearch.WordTrace tailWord_3254837 prefixEnd_3254837 1671295833038187168968783 := by
  unfold tailWord_3254837
  simp only [CollatzResearch.WordTrace]
  refine ⟨118713658109288905748690765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79142438739525937165793843 118713658109288905748690765)
  ·
    refine ⟨44517621790983339655759037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118713658109288905748690765 44517621790983339655759037)
    ·
      refine ⟨16694108171618752370909639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44517621790983339655759037 16694108171618752370909639)
      ·
        refine ⟨25041162257428128556364459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16694108171618752370909639 25041162257428128556364459)
        ·
          refine ⟨37561743386142192834546689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25041162257428128556364459 37561743386142192834546689)
          ·
            refine ⟨28171307539606644625910017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37561743386142192834546689 28171307539606644625910017)
            ·
              refine ⟨21128480654704983469432513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28171307539606644625910017 21128480654704983469432513)
              ·
                refine ⟨15846360491028737602074385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21128480654704983469432513 15846360491028737602074385)
                ·
                  refine ⟨11884770368271553201555789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15846360491028737602074385 11884770368271553201555789)
                  ·
                    refine ⟨4456788888101832450583421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11884770368271553201555789 4456788888101832450583421)
                    ·
                      refine ⟨1671295833038187168968783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4456788888101832450583421 1671295833038187168968783)
                      ·
                        rfl

theorem cell23_3254837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_3254837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254837 prefixEnd_3254837 := by exact prefixLift 3254837
  have htrace : WordTrace (prefixWord ++ tailWord_3254837) baseStart_3254837 baseEnd_3254837 := by
    simpa [prefixWord, tailWord_3254837, baseEnd_3254837] using wordTrace_append hprefix tailTrace_3254837
  have hstable : (prefixWord ++ tailWord_3254837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254837).length < 2 ^ (prefixWord ++ tailWord_3254837).sum := by decide
  have hdescent : baseEnd_3254837 < baseStart_3254837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254838 : List Nat := [5, 1, 2, 1, 2, 1, 1, 4, 2, 2, 2]
def baseStart_3254838 : Nat := 118140960795 + 3254838 * 2 ^ 59
def prefixEnd_3254838 : Nat := 4983230072969 + 3 ^ 40 * 3254838 * 2
def baseEnd_3254838 : Nat := 1671296346518841665056279

theorem tailTrace_3254838 : CollatzResearch.WordTrace tailWord_3254838 prefixEnd_3254838 1671296346518841665056279 := by
  unfold tailWord_3254838
  simp only [CollatzResearch.WordTrace]
  refine ⟨7419605911392830182467323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79142463054856855279651445 7419605911392830182467323)
  ·
    refine ⟨11129408867089245273700985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7419605911392830182467323 11129408867089245273700985)
    ·
      refine ⟨8347056650316933955275739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11129408867089245273700985 8347056650316933955275739)
      ·
        refine ⟨12520584975475400932913609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8347056650316933955275739 12520584975475400932913609)
        ·
          refine ⟨9390438731606550699685207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12520584975475400932913609 9390438731606550699685207)
          ·
            refine ⟨14085658097409826049527811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9390438731606550699685207 14085658097409826049527811)
            ·
              refine ⟨21128487146114739074291717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14085658097409826049527811 21128487146114739074291717)
              ·
                refine ⟨3961591339896513576429697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21128487146114739074291717 3961591339896513576429697)
                ·
                  refine ⟨2971193504922385182322273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3961591339896513576429697 2971193504922385182322273)
                  ·
                    refine ⟨2228395128691788886741705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2971193504922385182322273 2228395128691788886741705)
                    ·
                      refine ⟨1671296346518841665056279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2228395128691788886741705 1671296346518841665056279)
                      ·
                        rfl

theorem cell23_3254838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_3254838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254838 prefixEnd_3254838 := by exact prefixLift 3254838
  have htrace : WordTrace (prefixWord ++ tailWord_3254838) baseStart_3254838 baseEnd_3254838 := by
    simpa [prefixWord, tailWord_3254838, baseEnd_3254838] using wordTrace_append hprefix tailTrace_3254838
  have hstable : (prefixWord ++ tailWord_3254838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254838).length < 2 ^ (prefixWord ++ tailWord_3254838).sum := by decide
  have hdescent : baseEnd_3254838 < baseStart_3254838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254844 : List Nat := [2, 2, 2, 2, 3, 2, 1, 4, 5]
def baseStart_3254844 : Nat := 118140960795 + 3254844 * 2 ^ 59
def prefixEnd_3254844 : Nat := 4983230072969 + 3 ^ 40 * 3254844 * 2
def baseEnd_3254844 : Nat := 185699936378085404620139

theorem tailTrace_3254844 : CollatzResearch.WordTrace tailWord_3254844 prefixEnd_3254844 185699936378085404620139 := by
  unfold tailWord_3254844
  simp only [CollatzResearch.WordTrace]
  refine ⟨59356956710131772972097793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79142608946842363962797057 59356956710131772972097793)
  ·
    refine ⟨44517717532598829729073345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59356956710131772972097793 44517717532598829729073345)
    ·
      refine ⟨33388288149449122296805009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44517717532598829729073345 33388288149449122296805009)
      ·
        refine ⟨25041216112086841722603757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33388288149449122296805009 25041216112086841722603757)
        ·
          refine ⟨9390456042032565645976409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25041216112086841722603757 9390456042032565645976409)
          ·
            refine ⟨7042842031524424234482307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9390456042032565645976409 7042842031524424234482307)
            ·
              refine ⟨10564263047286636351723461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7042842031524424234482307 10564263047286636351723461)
              ·
                refine ⟨1980799321366244315948149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10564263047286636351723461 1980799321366244315948149)
                ·
                  refine ⟨185699936378085404620139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1980799321366244315948149 185699936378085404620139)
                  ·
                    rfl

theorem cell23_3254844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 5].length) (baseStart_3254844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254844 prefixEnd_3254844 := by exact prefixLift 3254844
  have htrace : WordTrace (prefixWord ++ tailWord_3254844) baseStart_3254844 baseEnd_3254844 := by
    simpa [prefixWord, tailWord_3254844, baseEnd_3254844] using wordTrace_append hprefix tailTrace_3254844
  have hstable : (prefixWord ++ tailWord_3254844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254844).length < 2 ^ (prefixWord ++ tailWord_3254844).sum := by decide
  have hdescent : baseEnd_3254844 < baseStart_3254844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254847 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 1, 7, 2]
def baseStart_3254847 : Nat := 118140960795 + 3254847 * 2 ^ 59
def prefixEnd_3254847 : Nat := 4983230072969 + 3 ^ 40 * 3254847 * 2
def baseEnd_3254847 : Nat := 1671300967844732129843737

theorem tailTrace_3254847 : CollatzResearch.WordTrace tailWord_3254847 prefixEnd_3254847 1671300967844732129843737 := by
  unfold tailWord_3254847
  simp only [CollatzResearch.WordTrace]
  refine ⟨118714022839252677456554795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79142681892835118304369863 118714022839252677456554795)
  ·
    refine ⟨178071034258879016184832193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118714022839252677456554795 178071034258879016184832193)
    ·
      refine ⟨133553275694159262138624145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178071034258879016184832193 133553275694159262138624145)
      ·
        refine ⟨100164956770619446603968109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133553275694159262138624145 100164956770619446603968109)
        ·
          refine ⟨37561858788982292476488041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100164956770619446603968109 37561858788982292476488041)
          ·
            refine ⟨28171394091736719357366031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37561858788982292476488041 28171394091736719357366031)
            ·
              refine ⟨42257091137605079036049047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28171394091736719357366031 42257091137605079036049047)
              ·
                refine ⟨63385636706407618554073571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42257091137605079036049047 63385636706407618554073571)
                ·
                  refine ⟨95078455059611427831110357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63385636706407618554073571 95078455059611427831110357)
                  ·
                    refine ⟨2228401290459642839791649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 95078455059611427831110357 2228401290459642839791649)
                    ·
                      refine ⟨1671300967844732129843737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2228401290459642839791649 1671300967844732129843737)
                      ·
                        rfl

theorem cell23_3254847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 7, 2].length) (baseStart_3254847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254847 prefixEnd_3254847 := by exact prefixLift 3254847
  have htrace : WordTrace (prefixWord ++ tailWord_3254847) baseStart_3254847 baseEnd_3254847 := by
    simpa [prefixWord, tailWord_3254847, baseEnd_3254847] using wordTrace_append hprefix tailTrace_3254847
  have hstable : (prefixWord ++ tailWord_3254847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254847).length < 2 ^ (prefixWord ++ tailWord_3254847).sum := by decide
  have hdescent : baseEnd_3254847 < baseStart_3254847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254887 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 7, 4]
def baseStart_3254887 : Nat := 118140960795 + 3254887 * 2 ^ 59
def prefixEnd_3254887 : Nat := 4983230072969 + 3 ^ 40 * 3254887 * 2
def baseEnd_3254887 : Nat := 557107169023637324447851

theorem tailTrace_3254887 : CollatzResearch.WordTrace tailWord_3254887 prefixEnd_3254887 557107169023637324447851 := by
  unfold tailWord_3254887
  simp only [CollatzResearch.WordTrace]
  refine ⟨118715481759107764288010915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79143654506071842858673943 118715481759107764288010915)
  ·
    refine ⟨178073222638661646432016373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118715481759107764288010915 178073222638661646432016373)
    ·
      refine ⟨16694364622374529353001535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178073222638661646432016373 16694364622374529353001535)
      ·
        refine ⟨25041546933561794029502303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16694364622374529353001535 25041546933561794029502303)
        ·
          refine ⟨37562320400342691044253455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25041546933561794029502303 37562320400342691044253455)
          ·
            refine ⟨56343480600514036566380183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37562320400342691044253455 56343480600514036566380183)
            ·
              refine ⟨84515220900771054849570275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56343480600514036566380183 84515220900771054849570275)
              ·
                refine ⟨126772831351156582274355413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84515220900771054849570275 126772831351156582274355413)
                ·
                  refine ⟨2971238234792732397055205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 126772831351156582274355413 2971238234792732397055205)
                  ·
                    refine ⟨557107169023637324447851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2971238234792732397055205 557107169023637324447851)
                    ·
                      rfl

theorem cell23_3254887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_3254887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254887 prefixEnd_3254887 := by exact prefixLift 3254887
  have htrace : WordTrace (prefixWord ++ tailWord_3254887) baseStart_3254887 baseEnd_3254887 := by
    simpa [prefixWord, tailWord_3254887, baseEnd_3254887] using wordTrace_append hprefix tailTrace_3254887
  have hstable : (prefixWord ++ tailWord_3254887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254887).length < 2 ^ (prefixWord ++ tailWord_3254887).sum := by decide
  have hdescent : baseEnd_3254887 < baseStart_3254887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254984 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 3, 1, 4]
def baseStart_3254984 : Nat := 118140960795 + 3254984 * 2 ^ 59
def prefixEnd_3254984 : Nat := 4983230072969 + 3 ^ 40 * 3254984 * 2
def baseEnd_3254984 : Nat := 1671371314694398093830607

theorem tailTrace_3254984 : CollatzResearch.WordTrace tailWord_3254984 prefixEnd_3254984 1671371314694398093830607 := by
  unfold tailWord_3254984
  simp only [CollatzResearch.WordTrace]
  refine ⟨59359509819878174927146003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79146013093170899902861337 59359509819878174927146003)
  ·
    refine ⟨89039264729817262390719005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59359509819878174927146003 89039264729817262390719005)
    ·
      refine ⟨33389724273681473396519627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89039264729817262390719005 33389724273681473396519627)
      ·
        refine ⟨50084586410522210094779441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33389724273681473396519627 50084586410522210094779441)
        ·
          refine ⟨37563439807891657571084581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50084586410522210094779441 37563439807891657571084581)
          ·
            refine ⟨7043144963979685794578359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37563439807891657571084581 7043144963979685794578359)
            ·
              refine ⟨10564717445969528691867539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7043144963979685794578359 10564717445969528691867539)
              ·
                refine ⟨15847076168954293037801309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10564717445969528691867539 15847076168954293037801309)
                ·
                  refine ⟨5942653563357859889175491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15847076168954293037801309 5942653563357859889175491)
                  ·
                    refine ⟨8913980345036789833763237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5942653563357859889175491 8913980345036789833763237)
                    ·
                      refine ⟨1671371314694398093830607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8913980345036789833763237 1671371314694398093830607)
                      ·
                        rfl

theorem cell23_3254984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_3254984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254984 prefixEnd_3254984 := by exact prefixLift 3254984
  have htrace : WordTrace (prefixWord ++ tailWord_3254984) baseStart_3254984 baseEnd_3254984 := by
    simpa [prefixWord, tailWord_3254984, baseEnd_3254984] using wordTrace_append hprefix tailTrace_3254984
  have hstable : (prefixWord ++ tailWord_3254984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254984).length < 2 ^ (prefixWord ++ tailWord_3254984).sum := by decide
  have hdescent : baseEnd_3254984 < baseStart_3254984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3254988 : List Nat := [2, 2, 1, 5, 1, 2, 2, 1, 2, 3, 2]
def baseStart_3254988 : Nat := 118140960795 + 3254988 * 2 ^ 59
def prefixEnd_3254988 : Nat := 4983230072969 + 3 ^ 40 * 3254988 * 2
def baseEnd_3254988 : Nat := 1671373368617016078180589

theorem tailTrace_3254988 : CollatzResearch.WordTrace tailWord_3254988 prefixEnd_3254988 1671373368617016078180589 := by
  unfold tailWord_3254988
  simp only [CollatzResearch.WordTrace]
  refine ⟨59359582765870929268718809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79146110354494572358291745 59359582765870929268718809)
  ·
    refine ⟨44519687074403196951539107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59359582765870929268718809 44519687074403196951539107)
    ·
      refine ⟨66779530611604795427308661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44519687074403196951539107 66779530611604795427308661)
      ·
        refine ⟨6260580994837949571310187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66779530611604795427308661 6260580994837949571310187)
        ·
          refine ⟨9390871492256924356965281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6260580994837949571310187 9390871492256924356965281)
          ·
            refine ⟨7043153619192693267723961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9390871492256924356965281 7043153619192693267723961)
            ·
              refine ⟨5282365214394519950792971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7043153619192693267723961 5282365214394519950792971)
              ·
                refine ⟨7923547821591779926189457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5282365214394519950792971 7923547821591779926189457)
                ·
                  refine ⟨5942660866193834944642093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7923547821591779926189457 5942660866193834944642093)
                  ·
                    refine ⟨2228497824822688104240785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5942660866193834944642093 2228497824822688104240785)
                    ·
                      refine ⟨1671373368617016078180589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2228497824822688104240785 1671373368617016078180589)
                      ·
                        rfl

theorem cell23_3254988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_3254988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3254988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3254988 prefixEnd_3254988 := by exact prefixLift 3254988
  have htrace : WordTrace (prefixWord ++ tailWord_3254988) baseStart_3254988 baseEnd_3254988 := by
    simpa [prefixWord, tailWord_3254988, baseEnd_3254988] using wordTrace_append hprefix tailTrace_3254988
  have hstable : (prefixWord ++ tailWord_3254988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3254988).length < 2 ^ (prefixWord ++ tailWord_3254988).sum := by decide
  have hdescent : baseEnd_3254988 < baseStart_3254988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3254988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255001 : List Nat := [1, 2, 1, 2, 3, 2, 5, 1, 1, 1, 4]
def baseStart_3255001 : Nat := 118140960795 + 3255001 * 2 ^ 59
def prefixEnd_3255001 : Nat := 4983230072969 + 3 ^ 40 * 3255001 * 2
def baseEnd_3255001 : Nat := 1671380043865524527318029

theorem tailTrace_3255001 : CollatzResearch.WordTrace tailWord_3255001 prefixEnd_3255001 1671380043865524527318029 := by
  unfold tailWord_3255001
  simp only [CollatzResearch.WordTrace]
  refine ⟨118719639680694761757660857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79146426453796507838440571 118719639680694761757660857)
  ·
    refine ⟨89039729760521071318245643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118719639680694761757660857 89039729760521071318245643)
    ·
      refine ⟨133559594640781606977368465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89039729760521071318245643 133559594640781606977368465)
      ·
        refine ⟨100169695980586205233026349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133559594640781606977368465 100169695980586205233026349)
        ·
          refine ⟨37563635992719826962384881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100169695980586205233026349 37563635992719826962384881)
          ·
            refine ⟨28172726994539870221788661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37563635992719826962384881 28172726994539870221788661)
            ·
              refine ⟨2641193155738112833292687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28172726994539870221788661 2641193155738112833292687)
              ·
                refine ⟨3961789733607169249939031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2641193155738112833292687 3961789733607169249939031)
                ·
                  refine ⟨5942684600410753874908547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3961789733607169249939031 5942684600410753874908547)
                  ·
                    refine ⟨8914026900616130812362821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5942684600410753874908547 8914026900616130812362821)
                    ·
                      refine ⟨1671380043865524527318029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8914026900616130812362821 1671380043865524527318029)
                      ·
                        rfl

theorem cell23_3255001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 1, 1, 4].length) (baseStart_3255001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255001 prefixEnd_3255001 := by exact prefixLift 3255001
  have htrace : WordTrace (prefixWord ++ tailWord_3255001) baseStart_3255001 baseEnd_3255001 := by
    simpa [prefixWord, tailWord_3255001, baseEnd_3255001] using wordTrace_append hprefix tailTrace_3255001
  have hstable : (prefixWord ++ tailWord_3255001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255001).length < 2 ^ (prefixWord ++ tailWord_3255001).sum := by decide
  have hdescent : baseEnd_3255001 < baseStart_3255001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255011 : List Nat := [1, 1, 1, 7, 1, 1, 1, 4, 2, 4]
def baseStart_3255011 : Nat := 118140960795 + 3255011 * 2 ^ 59
def prefixEnd_3255011 : Nat := 4983230072969 + 3 ^ 40 * 3255011 * 2
def baseEnd_3255011 : Nat := 557128392890689829397661

theorem tailTrace_3255011 : CollatzResearch.WordTrace tailWord_3255011 prefixEnd_3255011 557128392890689829397661 := by
  unfold tailWord_3255011
  simp only [CollatzResearch.WordTrace]
  refine ⟨118720004410658533465524887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79146669607105688977016591 118720004410658533465524887)
  ·
    refine ⟨178080006615987800198287331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118720004410658533465524887 178080006615987800198287331)
    ·
      refine ⟨267120009923981700297430997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178080006615987800198287331 267120009923981700297430997)
      ·
        refine ⟨6260625232593321100721039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 267120009923981700297430997 6260625232593321100721039)
        ·
          refine ⟨9390937848889981651081559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6260625232593321100721039 9390937848889981651081559)
          ·
            refine ⟨14086406773334972476622339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9390937848889981651081559 14086406773334972476622339)
            ·
              refine ⟨21129610160002458714933509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14086406773334972476622339 21129610160002458714933509)
              ·
                refine ⟨3961801905000461009050033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21129610160002458714933509 3961801905000461009050033)
                ·
                  refine ⟨2971351428750345756787525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3961801905000461009050033 2971351428750345756787525)
                  ·
                    refine ⟨557128392890689829397661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2971351428750345756787525 557128392890689829397661)
                    ·
                      rfl

theorem cell23_3255011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 4].length) (baseStart_3255011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255011 prefixEnd_3255011 := by exact prefixLift 3255011
  have htrace : WordTrace (prefixWord ++ tailWord_3255011) baseStart_3255011 baseEnd_3255011 := by
    simpa [prefixWord, tailWord_3255011, baseEnd_3255011] using wordTrace_append hprefix tailTrace_3255011
  have hstable : (prefixWord ++ tailWord_3255011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255011).length < 2 ^ (prefixWord ++ tailWord_3255011).sum := by decide
  have hdescent : baseEnd_3255011 < baseStart_3255011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255034 : List Nat := [3, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3]
def baseStart_3255034 : Nat := 118140960795 + 3255034 * 2 ^ 59
def prefixEnd_3255034 : Nat := 4983230072969 + 3 ^ 40 * 3255034 * 2
def baseEnd_3255034 : Nat := 1671396988727122898205377

theorem tailTrace_3255034 : CollatzResearch.WordTrace tailWord_3255034 prefixEnd_3255034 1671396988727122898205377 := by
  unfold tailWord_3255034
  simp only [CollatzResearch.WordTrace]
  refine ⟨29680210822393802098403039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79147228859716805595741437 29680210822393802098403039)
  ·
    refine ⟨44520316233590703147604559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29680210822393802098403039 44520316233590703147604559)
    ·
      refine ⟨66780474350386054721406839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44520316233590703147604559 66780474350386054721406839)
      ·
        refine ⟨100170711525579082082110259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66780474350386054721406839 100170711525579082082110259)
        ·
          refine ⟨150256067288368623123165389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100170711525579082082110259 150256067288368623123165389)
          ·
            refine ⟨56346025233138233671187021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150256067288368623123165389 56346025233138233671187021)
            ·
              refine ⟨21129759462426837626695133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56346025233138233671187021 21129759462426837626695133)
              ·
                refine ⟨7923659798410064110010675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21129759462426837626695133 7923659798410064110010675)
                ·
                  refine ⟨11885489697615096165016013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7923659798410064110010675 11885489697615096165016013)
                  ·
                    refine ⟨4457058636605661061881005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11885489697615096165016013 4457058636605661061881005)
                    ·
                      refine ⟨1671396988727122898205377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4457058636605661061881005 1671396988727122898205377)
                      ·
                        rfl

theorem cell23_3255034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3].length) (baseStart_3255034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255034 prefixEnd_3255034 := by exact prefixLift 3255034
  have htrace : WordTrace (prefixWord ++ tailWord_3255034) baseStart_3255034 baseEnd_3255034 := by
    simpa [prefixWord, tailWord_3255034, baseEnd_3255034] using wordTrace_append hprefix tailTrace_3255034
  have hstable : (prefixWord ++ tailWord_3255034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255034).length < 2 ^ (prefixWord ++ tailWord_3255034).sum := by decide
  have hdescent : baseEnd_3255034 < baseStart_3255034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255037 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 2, 7]
def baseStart_3255037 : Nat := 118140960795 + 3255037 * 2 ^ 59
def prefixEnd_3255037 : Nat := 4983230072969 + 3 ^ 40 * 3255037 * 2
def baseEnd_3255037 : Nat := 557132843056362128822621

theorem tailTrace_3255037 : CollatzResearch.WordTrace tailWord_3255037 prefixEnd_3255037 557132843056362128822621 := by
  unfold tailWord_3255037
  simp only [CollatzResearch.WordTrace]
  refine ⟨118720952708564339905971365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79147301805709559937314243 118720952708564339905971365)
  ·
    refine ⟨22260178632855813732369631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118720952708564339905971365 22260178632855813732369631)
    ·
      refine ⟨33390267949283720598554447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22260178632855813732369631 33390267949283720598554447)
      ·
        refine ⟨50085401923925580897831671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33390267949283720598554447 50085401923925580897831671)
        ·
          refine ⟨75128102885888371346747507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50085401923925580897831671 75128102885888371346747507)
          ·
            refine ⟨112692154328832557020121261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75128102885888371346747507 112692154328832557020121261)
            ·
              refine ⟨42259557873312208882545473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112692154328832557020121261 42259557873312208882545473)
              ·
                refine ⟨31694668404984156661909105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42259557873312208882545473 31694668404984156661909105)
                ·
                  refine ⟨23771001303738117496431829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31694668404984156661909105 23771001303738117496431829)
                  ·
                    refine ⟨557132843056362128822621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23771001303738117496431829 557132843056362128822621)
                    ·
                      rfl

theorem cell23_3255037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_3255037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255037 prefixEnd_3255037 := by exact prefixLift 3255037
  have htrace : WordTrace (prefixWord ++ tailWord_3255037) baseStart_3255037 baseEnd_3255037 := by
    simpa [prefixWord, tailWord_3255037, baseEnd_3255037] using wordTrace_append hprefix tailTrace_3255037
  have hstable : (prefixWord ++ tailWord_3255037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255037).length < 2 ^ (prefixWord ++ tailWord_3255037).sum := by decide
  have hdescent : baseEnd_3255037 < baseStart_3255037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255068 : List Nat := [2, 2, 3, 1, 1, 3, 3, 2, 2, 1, 3]
def baseStart_3255068 : Nat := 118140960795 + 3255068 * 2 ^ 59
def prefixEnd_3255068 : Nat := 4983230072969 + 3 ^ 40 * 3255068 * 2
def baseEnd_3255068 : Nat := 1671414447069375765180221

theorem tailTrace_3255068 : CollatzResearch.WordTrace tailWord_3255068 prefixEnd_3255068 1671414447069375765180221 := by
  unfold tailWord_3255068
  simp only [CollatzResearch.WordTrace]
  refine ⟨59361041685726016100174929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79148055580968021466899905 59361041685726016100174929)
  ·
    refine ⟨44520781264294512075131197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59361041685726016100174929 44520781264294512075131197)
    ·
      refine ⟨16695292974110442028174199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44520781264294512075131197 16695292974110442028174199)
      ·
        refine ⟨25042939461165663042261299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16695292974110442028174199 25042939461165663042261299)
        ·
          refine ⟨37564409191748494563391949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25042939461165663042261299 37564409191748494563391949)
          ·
            refine ⟨14086653446905685461271981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37564409191748494563391949 14086653446905685461271981)
            ·
              refine ⟨5282495042589632047976993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14086653446905685461271981 5282495042589632047976993)
              ·
                refine ⟨3961871281942224035982745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5282495042589632047976993 3961871281942224035982745)
                ·
                  refine ⟨2971403461456668026987059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3961871281942224035982745 2971403461456668026987059)
                  ·
                    refine ⟨4457105192185002040480589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2971403461456668026987059 4457105192185002040480589)
                    ·
                      refine ⟨1671414447069375765180221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4457105192185002040480589 1671414447069375765180221)
                      ·
                        rfl

theorem cell23_3255068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_3255068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255068 prefixEnd_3255068 := by exact prefixLift 3255068
  have htrace : WordTrace (prefixWord ++ tailWord_3255068) baseStart_3255068 baseEnd_3255068 := by
    simpa [prefixWord, tailWord_3255068, baseEnd_3255068] using wordTrace_append hprefix tailTrace_3255068
  have hstable : (prefixWord ++ tailWord_3255068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255068).length < 2 ^ (prefixWord ++ tailWord_3255068).sum := by decide
  have hdescent : baseEnd_3255068 < baseStart_3255068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255161 : List Nat := [1, 2, 1, 3, 2, 4, 2, 1, 2, 5]
def baseStart_3255161 : Nat := 118140960795 + 3255161 * 2 ^ 59
def prefixEnd_3255161 : Nat := 4983230072969 + 3 ^ 40 * 3255161 * 2
def baseEnd_3255161 : Nat := 557154066923414633772431

theorem tailTrace_3255161 : CollatzResearch.WordTrace tailWord_3255161 prefixEnd_3255161 557154066923414633772431 := by
  unfold tailWord_3255161
  simp only [CollatzResearch.WordTrace]
  refine ⟨118725475360115109083485337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79150316906743406055656891 118725475360115109083485337)
  ·
    refine ⟨89044106520086331812614003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118725475360115109083485337 89044106520086331812614003)
    ·
      refine ⟨133566159780129497718921005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89044106520086331812614003 133566159780129497718921005)
      ·
        refine ⟨50087309917548561644595377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133566159780129497718921005 50087309917548561644595377)
        ·
          refine ⟨37565482438161421233446533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50087309917548561644595377 37565482438161421233446533)
          ·
            refine ⟨7043527957155266481271225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37565482438161421233446533 7043527957155266481271225)
            ·
              refine ⟨5282645967866449860953419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7043527957155266481271225 5282645967866449860953419)
              ·
                refine ⟨7923968951799674791430129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5282645967866449860953419 7923968951799674791430129)
                ·
                  refine ⟨5942976713849756093572597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7923968951799674791430129 5942976713849756093572597)
                  ·
                    refine ⟨557154066923414633772431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5942976713849756093572597 557154066923414633772431)
                    ·
                      rfl

theorem cell23_3255161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 5].length) (baseStart_3255161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255161 prefixEnd_3255161 := by exact prefixLift 3255161
  have htrace : WordTrace (prefixWord ++ tailWord_3255161) baseStart_3255161 baseEnd_3255161 := by
    simpa [prefixWord, tailWord_3255161, baseEnd_3255161] using wordTrace_append hprefix tailTrace_3255161
  have hstable : (prefixWord ++ tailWord_3255161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255161).length < 2 ^ (prefixWord ++ tailWord_3255161).sum := by decide
  have hdescent : baseEnd_3255161 < baseStart_3255161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255164 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 1, 3, 4]
def baseStart_3255164 : Nat := 118140960795 + 3255164 * 2 ^ 59
def prefixEnd_3255164 : Nat := 4983230072969 + 3 ^ 40 * 3255164 * 2
def baseEnd_3255164 : Nat := 1671463741212207389579779

theorem tailTrace_3255164 : CollatzResearch.WordTrace tailWord_3255164 prefixEnd_3255164 1671463741212207389579779 := by
  unfold tailWord_3255164
  simp only [CollatzResearch.WordTrace]
  refine ⟨59362792389552120297922273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79150389852736160397229697 59362792389552120297922273)
  ·
    refine ⟨44522094292164090223441705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59362792389552120297922273 44522094292164090223441705)
    ·
      refine ⟨33391570719123067667581279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44522094292164090223441705 33391570719123067667581279)
      ·
        refine ⟨50087356078684601501371919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33391570719123067667581279 50087356078684601501371919)
        ·
          refine ⟨75131034118026902252057879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50087356078684601501371919 75131034118026902252057879)
          ·
            refine ⟨112696551177040353378086819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75131034118026902252057879 112696551177040353378086819)
            ·
              refine ⟨169044826765560530067130229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112696551177040353378086819 169044826765560530067130229)
              ·
                refine ⟨15847952509271299693793459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169044826765560530067130229 15847952509271299693793459)
                ·
                  refine ⟨23771928763906949540690189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15847952509271299693793459 23771928763906949540690189)
                  ·
                    refine ⟨8914473286465106077758821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23771928763906949540690189 8914473286465106077758821)
                    ·
                      refine ⟨1671463741212207389579779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8914473286465106077758821 1671463741212207389579779)
                      ·
                        rfl

theorem cell23_3255164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_3255164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255164 prefixEnd_3255164 := by exact prefixLift 3255164
  have htrace : WordTrace (prefixWord ++ tailWord_3255164) baseStart_3255164 baseEnd_3255164 := by
    simpa [prefixWord, tailWord_3255164, baseEnd_3255164] using wordTrace_append hprefix tailTrace_3255164
  have hstable : (prefixWord ++ tailWord_3255164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255164).length < 2 ^ (prefixWord ++ tailWord_3255164).sum := by decide
  have hdescent : baseEnd_3255164 < baseStart_3255164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255191 : List Nat := [1, 1, 3, 3, 1, 2, 2, 3, 3, 4]
def baseStart_3255191 : Nat := 118140960795 + 3255191 * 2 ^ 59
def prefixEnd_3255191 : Nat := 4983230072969 + 3 ^ 40 * 3255191 * 2
def baseEnd_3255191 : Nat := 557159201729959594647385

theorem tailTrace_3255191 : CollatzResearch.WordTrace tailWord_3255191 prefixEnd_3255191 557159201729959594647385 := by
  unfold tailWord_3255191
  simp only [CollatzResearch.WordTrace]
  refine ⟨118726569550006424207077427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79151046366670949471384951 118726569550006424207077427)
  ·
    refine ⟨178089854325009636310616141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118726569550006424207077427 178089854325009636310616141)
    ·
      refine ⟨66783695371878613616481053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178089854325009636310616141 66783695371878613616481053)
      ·
        refine ⟨25043885764454480106180395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66783695371878613616481053 25043885764454480106180395)
        ·
          refine ⟨37565828646681720159270593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25043885764454480106180395 37565828646681720159270593)
          ·
            refine ⟨28174371485011290119452945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37565828646681720159270593 28174371485011290119452945)
            ·
              refine ⟨21130778613758467589589709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28174371485011290119452945 21130778613758467589589709)
              ·
                refine ⟨7924041980159425346096141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21130778613758467589589709 7924041980159425346096141)
                ·
                  refine ⟨2971515742559784504786053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7924041980159425346096141 2971515742559784504786053)
                  ·
                    refine ⟨557159201729959594647385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2971515742559784504786053 557159201729959594647385)
                    ·
                      rfl

theorem cell23_3255191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 4].length) (baseStart_3255191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255191 prefixEnd_3255191 := by exact prefixLift 3255191
  have htrace : WordTrace (prefixWord ++ tailWord_3255191) baseStart_3255191 baseEnd_3255191 := by
    simpa [prefixWord, tailWord_3255191, baseEnd_3255191] using wordTrace_append hprefix tailTrace_3255191
  have hstable : (prefixWord ++ tailWord_3255191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255191).length < 2 ^ (prefixWord ++ tailWord_3255191).sum := by decide
  have hdescent : baseEnd_3255191 < baseStart_3255191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255225 : List Nat := [1, 2, 1, 4, 2, 3, 2, 3, 1, 4]
def baseStart_3255225 : Nat := 118140960795 + 3255225 * 2 ^ 59
def prefixEnd_3255225 : Nat := 4983230072969 + 3 ^ 40 * 3255225 * 2
def baseEnd_3255225 : Nat := 557165021177377216972333

theorem tailTrace_3255225 : CollatzResearch.WordTrace tailWord_3255225 prefixEnd_3255225 557165021177377216972333 := by
  unfold tailWord_3255225
  simp only [CollatzResearch.WordTrace]
  refine ⟨118727809631883248013815129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79151873087922165342543419 118727809631883248013815129)
  ·
    refine ⟨89045857223912436010361347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118727809631883248013815129 89045857223912436010361347)
    ·
      refine ⟨133568785835868654015542021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89045857223912436010361347 133568785835868654015542021)
      ·
        refine ⟨25044147344225372627914129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133568785835868654015542021 25044147344225372627914129)
        ·
          refine ⟨18783110508169029470935597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25044147344225372627914129 18783110508169029470935597)
          ·
            refine ⟨7043666440563386051600849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18783110508169029470935597 7043666440563386051600849)
            ·
              refine ⟨5282749830422539538700637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7043666440563386051600849 5282749830422539538700637)
              ·
                refine ⟨1981031186408452327012739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5282749830422539538700637 1981031186408452327012739)
                ·
                  refine ⟨2971546779612678490519109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1981031186408452327012739 2971546779612678490519109)
                  ·
                    refine ⟨557165021177377216972333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2971546779612678490519109 557165021177377216972333)
                    ·
                      rfl

theorem cell23_3255225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 1, 4].length) (baseStart_3255225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255225 prefixEnd_3255225 := by exact prefixLift 3255225
  have htrace : WordTrace (prefixWord ++ tailWord_3255225) baseStart_3255225 baseEnd_3255225 := by
    simpa [prefixWord, tailWord_3255225, baseEnd_3255225] using wordTrace_append hprefix tailTrace_3255225
  have hstable : (prefixWord ++ tailWord_3255225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255225).length < 2 ^ (prefixWord ++ tailWord_3255225).sum := by decide
  have hdescent : baseEnd_3255225 < baseStart_3255225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255241 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 5, 5, 2]
def baseStart_3255241 : Nat := 118140960795 + 3255241 * 2 ^ 59
def prefixEnd_3255241 : Nat := 4983230072969 + 3 ^ 40 * 3255241 * 2
def baseEnd_3255241 : Nat := 1671503279222603588316925

theorem tailTrace_3255241 : CollatzResearch.WordTrace tailWord_3255241 prefixEnd_3255241 1671503279222603588316925 := by
  unfold tailWord_3255241
  simp only [CollatzResearch.WordTrace]
  refine ⟨118728393199825282746397577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79152262133216855164265051 118728393199825282746397577)
  ·
    refine ⟨89046294899868962059798183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118728393199825282746397577 89046294899868962059798183)
    ·
      refine ⟨133569442349803443089697275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89046294899868962059798183 133569442349803443089697275)
      ·
        refine ⟨200354163524705164634545913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133569442349803443089697275 200354163524705164634545913)
        ·
          refine ⟨150265622643528873475909435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200354163524705164634545913 150265622643528873475909435)
          ·
            refine ⟨225398433965293310213864153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150265622643528873475909435 225398433965293310213864153)
            ·
              refine ⟨169048825473969982660398115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225398433965293310213864153 169048825473969982660398115)
              ·
                refine ⟨253573238210954973990597173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169048825473969982660398115 253573238210954973990597173)
                ·
                  refine ⟨23772491082277028811618485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 253573238210954973990597173 23772491082277028811618485)
                  ·
                    refine ⟨2228671038963471451089233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23772491082277028811618485 2228671038963471451089233)
                    ·
                      refine ⟨1671503279222603588316925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2228671038963471451089233 1671503279222603588316925)
                      ·
                        rfl

theorem cell23_3255241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 5, 2].length) (baseStart_3255241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255241 prefixEnd_3255241 := by exact prefixLift 3255241
  have htrace : WordTrace (prefixWord ++ tailWord_3255241) baseStart_3255241 baseEnd_3255241 := by
    simpa [prefixWord, tailWord_3255241, baseEnd_3255241] using wordTrace_append hprefix tailTrace_3255241
  have hstable : (prefixWord ++ tailWord_3255241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255241).length < 2 ^ (prefixWord ++ tailWord_3255241).sum := by decide
  have hdescent : baseEnd_3255241 < baseStart_3255241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255258 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2]
def baseStart_3255258 : Nat := 118140960795 + 3255258 * 2 ^ 59
def prefixEnd_3255258 : Nat := 4983230072969 + 3 ^ 40 * 3255258 * 2
def baseEnd_3255258 : Nat := 1671512008393730021804347

theorem tailTrace_3255258 : CollatzResearch.WordTrace tailWord_3255258 prefixEnd_3255258 1671512008393730021804347 := by
  unfold tailWord_3255258
  simp only [CollatzResearch.WordTrace]
  refine ⟨29682253310190923662441607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79152675493842463099844285 29682253310190923662441607)
  ·
    refine ⟨44523379965286385493662411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29682253310190923662441607 44523379965286385493662411)
    ·
      refine ⟨66785069947929578240493617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44523379965286385493662411 66785069947929578240493617)
      ·
        refine ⟨50088802460947183680370213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66785069947929578240493617 50088802460947183680370213)
        ·
          refine ⟨9391650461427596940069415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50088802460947183680370213 9391650461427596940069415)
          ·
            refine ⟨14087475692141395410104123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9391650461427596940069415 14087475692141395410104123)
            ·
              refine ⟨21131213538212093115156185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14087475692141395410104123 21131213538212093115156185)
              ·
                refine ⟨15848410153659069836367139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21131213538212093115156185 15848410153659069836367139)
                ·
                  refine ⟨23772615230488604754550709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15848410153659069836367139 23772615230488604754550709)
                  ·
                    refine ⟨2228682677858306695739129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23772615230488604754550709 2228682677858306695739129)
                    ·
                      refine ⟨1671512008393730021804347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2228682677858306695739129 1671512008393730021804347)
                      ·
                        rfl

theorem cell23_3255258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2].length) (baseStart_3255258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255258 prefixEnd_3255258 := by exact prefixLift 3255258
  have htrace : WordTrace (prefixWord ++ tailWord_3255258) baseStart_3255258 baseEnd_3255258 := by
    simpa [prefixWord, tailWord_3255258, baseEnd_3255258] using wordTrace_append hprefix tailTrace_3255258
  have hstable : (prefixWord ++ tailWord_3255258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255258).length < 2 ^ (prefixWord ++ tailWord_3255258).sum := by decide
  have hdescent : baseEnd_3255258 < baseStart_3255258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255291 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 3]
def baseStart_3255291 : Nat := 118140960795 + 3255291 * 2 ^ 59
def prefixEnd_3255291 : Nat := 4983230072969 + 3 ^ 40 * 3255291 * 2
def baseEnd_3255291 : Nat := 1671528953255328392691695

theorem tailTrace_3255291 : CollatzResearch.WordTrace tailWord_3255291 prefixEnd_3255291 1671528953255328392691695 := by
  unfold tailWord_3255291
  simp only [CollatzResearch.WordTrace]
  refine ⟨118730216849644141285717727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79153477899762760857145151 118730216849644141285717727)
  ·
    refine ⟨178095325274466211928576591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118730216849644141285717727 178095325274466211928576591)
    ·
      refine ⟨267142987911699317892864887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178095325274466211928576591 267142987911699317892864887)
      ·
        refine ⟨400714481867548976839297331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267142987911699317892864887 400714481867548976839297331)
        ·
          refine ⟨601071722801323465258945997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400714481867548976839297331 601071722801323465258945997)
          ·
            refine ⟨225401896050496299472104749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 601071722801323465258945997 225401896050496299472104749)
            ·
              refine ⟨84525711018936112302039281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225401896050496299472104749 84525711018936112302039281)
              ·
                refine ⟨63394283264202084226529461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84525711018936112302039281 63394283264202084226529461)
                ·
                  refine ⟨5943214056018945396237137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63394283264202084226529461 5943214056018945396237137)
                  ·
                    refine ⟨4457410542014209047177853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5943214056018945396237137 4457410542014209047177853)
                    ·
                      refine ⟨1671528953255328392691695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4457410542014209047177853 1671528953255328392691695)
                      ·
                        rfl

theorem cell23_3255291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 3].length) (baseStart_3255291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255291 prefixEnd_3255291 := by exact prefixLift 3255291
  have htrace : WordTrace (prefixWord ++ tailWord_3255291) baseStart_3255291 baseEnd_3255291 := by
    simpa [prefixWord, tailWord_3255291, baseEnd_3255291] using wordTrace_append hprefix tailTrace_3255291
  have hstable : (prefixWord ++ tailWord_3255291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255291).length < 2 ^ (prefixWord ++ tailWord_3255291).sum := by decide
  have hdescent : baseEnd_3255291 < baseStart_3255291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255325 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 3, 2, 3]
def baseStart_3255325 : Nat := 118140960795 + 3255325 * 2 ^ 59
def prefixEnd_3255325 : Nat := 4983230072969 + 3 ^ 40 * 3255325 * 2
def baseEnd_3255325 : Nat := 1671546411597581259666539

theorem tailTrace_3255325 : CollatzResearch.WordTrace tailWord_3255325 prefixEnd_3255325 1671546411597581259666539 := by
  unfold tailWord_3255325
  simp only [CollatzResearch.WordTrace]
  refine ⟨118731456931520965092455429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79154304621013976728303619 118731456931520965092455429)
  ·
    refine ⟨22262148174660180954835393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118731456931520965092455429 22262148174660180954835393)
    ·
      refine ⟨16696611130995135716126545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22262148174660180954835393 16696611130995135716126545)
      ·
        refine ⟨12522458348246351787094909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16696611130995135716126545 12522458348246351787094909)
        ·
          refine ⟨4695921880592381920160591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12522458348246351787094909 4695921880592381920160591)
          ·
            refine ⟨7043882820888572880240887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4695921880592381920160591 7043882820888572880240887)
            ·
              refine ⟨10565824231332859320361331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7043882820888572880240887 10565824231332859320361331)
              ·
                refine ⟨15848736346999288980541997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10565824231332859320361331 15848736346999288980541997)
                ·
                  refine ⟨5943276130124733367703249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15848736346999288980541997 5943276130124733367703249)
                  ·
                    refine ⟨4457457097593550025777437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5943276130124733367703249 4457457097593550025777437)
                    ·
                      refine ⟨1671546411597581259666539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4457457097593550025777437 1671546411597581259666539)
                      ·
                        rfl

theorem cell23_3255325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_3255325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255325 prefixEnd_3255325 := by exact prefixLift 3255325
  have htrace : WordTrace (prefixWord ++ tailWord_3255325) baseStart_3255325 baseEnd_3255325 := by
    simpa [prefixWord, tailWord_3255325, baseEnd_3255325] using wordTrace_append hprefix tailTrace_3255325
  have hstable : (prefixWord ++ tailWord_3255325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255325).length < 2 ^ (prefixWord ++ tailWord_3255325).sum := by decide
  have hdescent : baseEnd_3255325 < baseStart_3255325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255335 : List Nat := [1, 1, 7, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_3255335 : Nat := 118140960795 + 3255335 * 2 ^ 59
def prefixEnd_3255335 : Nat := 4983230072969 + 3 ^ 40 * 3255335 * 2
def baseEnd_3255335 : Nat := 1671551546404126220541493

theorem tailTrace_3255335 : CollatzResearch.WordTrace tailWord_3255335 prefixEnd_3255335 1671551546404126220541493 := by
  unfold tailWord_3255335
  simp only [CollatzResearch.WordTrace]
  refine ⟨118731821661484736800319459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79154547774323157866879639 118731821661484736800319459)
  ·
    refine ⟨178097732492227105200479189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118731821661484736800319459 178097732492227105200479189)
    ·
      refine ⟨4174165605286572778136231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 178097732492227105200479189 4174165605286572778136231)
      ·
        refine ⟨6261248407929859167204347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4174165605286572778136231 6261248407929859167204347)
        ·
          refine ⟨9391872611894788750806521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6261248407929859167204347 9391872611894788750806521)
          ·
            refine ⟨7043904458921091563104891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9391872611894788750806521 7043904458921091563104891)
            ·
              refine ⟨10565856688381637344657337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7043904458921091563104891 10565856688381637344657337)
              ·
                refine ⟨7924392516286228008493003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10565856688381637344657337 7924392516286228008493003)
                ·
                  refine ⟨11886588774429342012739505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7924392516286228008493003 11886588774429342012739505)
                  ·
                    refine ⟨8914941580822006509554629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11886588774429342012739505 8914941580822006509554629)
                    ·
                      refine ⟨1671551546404126220541493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8914941580822006509554629 1671551546404126220541493)
                      ·
                        rfl

theorem cell23_3255335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_3255335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255335 prefixEnd_3255335 := by exact prefixLift 3255335
  have htrace : WordTrace (prefixWord ++ tailWord_3255335) baseStart_3255335 baseEnd_3255335 := by
    simpa [prefixWord, tailWord_3255335, baseEnd_3255335] using wordTrace_append hprefix tailTrace_3255335
  have hstable : (prefixWord ++ tailWord_3255335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255335).length < 2 ^ (prefixWord ++ tailWord_3255335).sum := by decide
  have hdescent : baseEnd_3255335 < baseStart_3255335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255342 : List Nat := [4, 1, 3, 1, 1, 1, 5, 1, 1, 2, 3]
def baseStart_3255342 : Nat := 118140960795 + 3255342 * 2 ^ 59
def prefixEnd_3255342 : Nat := 4983230072969 + 3 ^ 40 * 3255342 * 2
def baseEnd_3255342 : Nat := 1671555140768707693153961

theorem tailTrace_3255342 : CollatzResearch.WordTrace tailWord_3255342 prefixEnd_3255342 1671555140768707693153961 := by
  unfold tailWord_3255342
  simp only [CollatzResearch.WordTrace]
  refine ⟨14841509621557422124478035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79154717981639584663882853 14841509621557422124478035)
  ·
    refine ⟨22262264432336133186717053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14841509621557422124478035 22262264432336133186717053)
    ·
      refine ⟨8348349162126049945018895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22262264432336133186717053 8348349162126049945018895)
      ·
        refine ⟨12522523743189074917528343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8348349162126049945018895 12522523743189074917528343)
        ·
          refine ⟨18783785614783612376292515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12522523743189074917528343 18783785614783612376292515)
          ·
            refine ⟨28175678422175418564438773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18783785614783612376292515 28175678422175418564438773)
            ·
              refine ⟨2641469852078945490416135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28175678422175418564438773 2641469852078945490416135)
              ·
                refine ⟨3962204778118418235624203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2641469852078945490416135 3962204778118418235624203)
                ·
                  refine ⟨5943307167177627353436305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3962204778118418235624203 5943307167177627353436305)
                  ·
                    refine ⟨4457480375383220515077229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5943307167177627353436305 4457480375383220515077229)
                    ·
                      refine ⟨1671555140768707693153961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4457480375383220515077229 1671555140768707693153961)
                      ·
                        rfl

theorem cell23_3255342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_3255342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255342 prefixEnd_3255342 := by exact prefixLift 3255342
  have htrace : WordTrace (prefixWord ++ tailWord_3255342) baseStart_3255342 baseEnd_3255342 := by
    simpa [prefixWord, tailWord_3255342, baseEnd_3255342] using wordTrace_append hprefix tailTrace_3255342
  have hstable : (prefixWord ++ tailWord_3255342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255342).length < 2 ^ (prefixWord ++ tailWord_3255342).sum := by decide
  have hdescent : baseEnd_3255342 < baseStart_3255342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255356 : List Nat := [2, 2, 2, 2, 2, 4, 2, 2, 1, 2, 2]
def baseStart_3255356 : Nat := 118140960795 + 3255356 * 2 ^ 59
def prefixEnd_3255356 : Nat := 4983230072969 + 3 ^ 40 * 3255356 * 2
def baseEnd_3255356 : Nat := 1671562329497870638378897

theorem tailTrace_3255356 : CollatzResearch.WordTrace tailWord_3255356 prefixEnd_3255356 1671562329497870638378897 := by
  unfold tailWord_3255356
  simp only [CollatzResearch.WordTrace]
  refine ⟨59366293797204328693416961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79155058396272438257889281 59366293797204328693416961)
  ·
    refine ⟨44524720347903246520062721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59366293797204328693416961 44524720347903246520062721)
    ·
      refine ⟨33393540260927434890047041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44524720347903246520062721 33393540260927434890047041)
      ·
        refine ⟨25045155195695576167535281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33393540260927434890047041 25045155195695576167535281)
        ·
          refine ⟨18783866396771682125651461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25045155195695576167535281 18783866396771682125651461)
          ·
            refine ⟨3521974949394690398559649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18783866396771682125651461 3521974949394690398559649)
            ·
              refine ⟨2641481212046017798919737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3521974949394690398559649 2641481212046017798919737)
              ·
                refine ⟨1981110909034513349189803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2641481212046017798919737 1981110909034513349189803)
                ·
                  refine ⟨2971666363551770023784705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1981110909034513349189803 2971666363551770023784705)
                  ·
                    refine ⟨2228749772663827517838529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2971666363551770023784705 2228749772663827517838529)
                    ·
                      refine ⟨1671562329497870638378897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2228749772663827517838529 1671562329497870638378897)
                      ·
                        rfl

theorem cell23_3255356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_3255356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255356 prefixEnd_3255356 := by exact prefixLift 3255356
  have htrace : WordTrace (prefixWord ++ tailWord_3255356) baseStart_3255356 baseEnd_3255356 := by
    simpa [prefixWord, tailWord_3255356, baseEnd_3255356] using wordTrace_append hprefix tailTrace_3255356
  have hstable : (prefixWord ++ tailWord_3255356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255356).length < 2 ^ (prefixWord ++ tailWord_3255356).sum := by decide
  have hdescent : baseEnd_3255356 < baseStart_3255356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255358 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 2, 7]
def baseStart_3255358 : Nat := 118140960795 + 3255358 * 2 ^ 59
def prefixEnd_3255358 : Nat := 4983230072969 + 3 ^ 40 * 3255358 * 2
def baseEnd_3255358 : Nat := 557187785486393210184629

theorem tailTrace_3255358 : CollatzResearch.WordTrace tailWord_3255358 prefixEnd_3255358 557187785486393210184629 := by
  unfold tailWord_3255358
  simp only [CollatzResearch.WordTrace]
  refine ⟨14841582567550176466050841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79155107026934274485604485 14841582567550176466050841)
  ·
    refine ⟨11131186925662632349538131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14841582567550176466050841 11131186925662632349538131)
    ·
      refine ⟨16696780388493948524307197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11131186925662632349538131 16696780388493948524307197)
      ·
        refine ⟨6261292645685230696615199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16696780388493948524307197 6261292645685230696615199)
        ·
          refine ⟨9391938968527846044922799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6261292645685230696615199 9391938968527846044922799)
          ·
            refine ⟨14087908452791769067384199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9391938968527846044922799 14087908452791769067384199)
            ·
              refine ⟨21131862679187653601076299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14087908452791769067384199 21131862679187653601076299)
              ·
                refine ⟨31697794018781480401614449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21131862679187653601076299 31697794018781480401614449)
                ·
                  refine ⟨23773345514086110301210837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31697794018781480401614449 23773345514086110301210837)
                  ·
                    refine ⟨557187785486393210184629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23773345514086110301210837 557187785486393210184629)
                    ·
                      rfl

theorem cell23_3255358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_3255358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255358 prefixEnd_3255358 := by exact prefixLift 3255358
  have htrace : WordTrace (prefixWord ++ tailWord_3255358) baseStart_3255358 baseEnd_3255358 := by
    simpa [prefixWord, tailWord_3255358, baseEnd_3255358] using wordTrace_append hprefix tailTrace_3255358
  have hstable : (prefixWord ++ tailWord_3255358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255358).length < 2 ^ (prefixWord ++ tailWord_3255358).sum := by decide
  have hdescent : baseEnd_3255358 < baseStart_3255358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255391 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 4]
def baseStart_3255391 : Nat := 118140960795 + 3255391 * 2 ^ 59
def prefixEnd_3255391 : Nat := 4983230072969 + 3 ^ 40 * 3255391 * 2
def baseEnd_3255391 : Nat := 1671580301320778001441235

theorem tailTrace_3255391 : CollatzResearch.WordTrace tailWord_3255391 prefixEnd_3255391 1671580301320778001441235 := by
  unfold tailWord_3255391
  simp only [CollatzResearch.WordTrace]
  refine ⟨118733864149281858364358027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79155909432854572242905351 118733864149281858364358027)
  ·
    refine ⟨178100796223922787546537041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118733864149281858364358027 178100796223922787546537041)
    ·
      refine ⟨133575597167942090659902781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178100796223922787546537041 133575597167942090659902781)
      ·
        refine ⟨50090848937978283997463543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133575597167942090659902781 50090848937978283997463543)
        ·
          refine ⟨75136273406967425996195315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50090848937978283997463543 75136273406967425996195315)
          ·
            refine ⟨112704410110451138994292973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75136273406967425996195315 112704410110451138994292973)
            ·
              refine ⟨42264153791419177122859865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112704410110451138994292973 42264153791419177122859865)
              ·
                refine ⟨31698115343564382842144899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42264153791419177122859865 31698115343564382842144899)
                ·
                  refine ⟨47547173015346574263217349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31698115343564382842144899 47547173015346574263217349)
                  ·
                    refine ⟨8915094940377482674353253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47547173015346574263217349 8915094940377482674353253)
                    ·
                      refine ⟨1671580301320778001441235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8915094940377482674353253 1671580301320778001441235)
                      ·
                        rfl

theorem cell23_3255391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_3255391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255391 prefixEnd_3255391 := by exact prefixLift 3255391
  have htrace : WordTrace (prefixWord ++ tailWord_3255391) baseStart_3255391 baseEnd_3255391 := by
    simpa [prefixWord, tailWord_3255391, baseEnd_3255391] using wordTrace_append hprefix tailTrace_3255391
  have hstable : (prefixWord ++ tailWord_3255391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255391).length < 2 ^ (prefixWord ++ tailWord_3255391).sum := by decide
  have hdescent : baseEnd_3255391 < baseStart_3255391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255395 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 4, 2, 2]
def baseStart_3255395 : Nat := 118140960795 + 3255395 * 2 ^ 59
def prefixEnd_3255395 : Nat := 4983230072969 + 3 ^ 40 * 3255395 * 2
def baseEnd_3255395 : Nat := 1671582355243395985791217

theorem tailTrace_3255395 : CollatzResearch.WordTrace tailWord_3255395 prefixEnd_3255395 1671582355243395985791217 := by
  unfold tailWord_3255395
  simp only [CollatzResearch.WordTrace]
  refine ⟨118734010041267367047503639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79156006694178244698335759 118734010041267367047503639)
  ·
    refine ⟨178101015061901050571255459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118734010041267367047503639 178101015061901050571255459)
    ·
      refine ⟨267151522592851575856883189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178101015061901050571255459 267151522592851575856883189)
      ·
        refine ⟨25045455243079835236582799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 267151522592851575856883189 25045455243079835236582799)
        ·
          refine ⟨37568182864619752854874199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25045455243079835236582799 37568182864619752854874199)
          ·
            refine ⟨56352274296929629282311299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37568182864619752854874199 56352274296929629282311299)
            ·
              refine ⟨84528411445394443923466949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56352274296929629282311299 84528411445394443923466949)
              ·
                refine ⟨15849077146011458235650053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84528411445394443923466949 15849077146011458235650053)
                ·
                  refine ⟨2971701964877148419184385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15849077146011458235650053 2971701964877148419184385)
                  ·
                    refine ⟨2228776473657861314388289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2971701964877148419184385 2228776473657861314388289)
                    ·
                      refine ⟨1671582355243395985791217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2228776473657861314388289 1671582355243395985791217)
                      ·
                        rfl

theorem cell23_3255395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_3255395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255395 prefixEnd_3255395 := by exact prefixLift 3255395
  have htrace : WordTrace (prefixWord ++ tailWord_3255395) baseStart_3255395 baseEnd_3255395 := by
    simpa [prefixWord, tailWord_3255395, baseEnd_3255395] using wordTrace_append hprefix tailTrace_3255395
  have hstable : (prefixWord ++ tailWord_3255395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255395).length < 2 ^ (prefixWord ++ tailWord_3255395).sum := by decide
  have hdescent : baseEnd_3255395 < baseStart_3255395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255399 : List Nat := [1, 1, 5, 1, 1, 5, 2, 1, 1, 3, 2]
def baseStart_3255399 : Nat := 118140960795 + 3255399 * 2 ^ 59
def prefixEnd_3255399 : Nat := 4983230072969 + 3 ^ 40 * 3255399 * 2
def baseEnd_3255399 : Nat := 1671584409166013970141199

theorem tailTrace_3255399 : CollatzResearch.WordTrace tailWord_3255399 prefixEnd_3255399 1671584409166013970141199 := by
  unfold tailWord_3255399
  simp only [CollatzResearch.WordTrace]
  refine ⟨118734155933252875730649251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79156103955501917153766167 118734155933252875730649251)
  ·
    refine ⟨178101233899879313595973877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118734155933252875730649251 178101233899879313595973877)
    ·
      refine ⟨16696990678113685649622551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178101233899879313595973877 16696990678113685649622551)
      ·
        refine ⟨25045486017170528474433827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16696990678113685649622551 25045486017170528474433827)
        ·
          refine ⟨37568229025755792711650741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25045486017170528474433827 37568229025755792711650741)
          ·
            refine ⟨3522021471164605566717257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37568229025755792711650741 3522021471164605566717257)
            ·
              refine ⟨2641516103373454175037943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3522021471164605566717257 2641516103373454175037943)
              ·
                refine ⟨3962274155060181262556915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2641516103373454175037943 3962274155060181262556915)
                ·
                  refine ⟨5943411232590271893835373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3962274155060181262556915 5943411232590271893835373)
                  ·
                    refine ⟨2228779212221351960188265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5943411232590271893835373 2228779212221351960188265)
                    ·
                      refine ⟨1671584409166013970141199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2228779212221351960188265 1671584409166013970141199)
                      ·
                        rfl

theorem cell23_3255399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_3255399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255399 prefixEnd_3255399 := by exact prefixLift 3255399
  have htrace : WordTrace (prefixWord ++ tailWord_3255399) baseStart_3255399 baseEnd_3255399 := by
    simpa [prefixWord, tailWord_3255399, baseEnd_3255399] using wordTrace_append hprefix tailTrace_3255399
  have hstable : (prefixWord ++ tailWord_3255399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255399).length < 2 ^ (prefixWord ++ tailWord_3255399).sum := by decide
  have hdescent : baseEnd_3255399 < baseStart_3255399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255429 : List Nat := [1, 3, 1, 1, 7, 1, 1, 1, 1, 4, 2]
def baseStart_3255429 : Nat := 118140960795 + 3255429 * 2 ^ 59
def prefixEnd_3255429 : Nat := 4983230072969 + 3 ^ 40 * 3255429 * 2
def baseEnd_3255429 : Nat := 1671599813585648852766061

theorem tailTrace_3255429 : CollatzResearch.WordTrace tailWord_3255429 prefixEnd_3255429 1671599813585648852766061 := by
  unfold tailWord_3255429
  simp only [CollatzResearch.WordTrace]
  refine ⟨118735250123144190854241341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79156833415429460569494227 118735250123144190854241341)
  ·
    refine ⟨44525718796179071570340503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118735250123144190854241341 44525718796179071570340503)
    ·
      refine ⟨66788578194268607355510755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44525718796179071570340503 66788578194268607355510755)
      ·
        refine ⟨100182867291402911033266133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66788578194268607355510755 100182867291402911033266133)
        ·
          refine ⟨2348035952142255727342175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 100182867291402911033266133 2348035952142255727342175)
          ·
            refine ⟨3522053928213383591013263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2348035952142255727342175 3522053928213383591013263)
            ·
              refine ⟨5283080892320075386519895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3522053928213383591013263 5283080892320075386519895)
              ·
                refine ⟨7924621338480113079779843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5283080892320075386519895 7924621338480113079779843)
                ·
                  refine ⟨11886932007720169619669765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7924621338480113079779843 11886932007720169619669765)
                  ·
                    refine ⟨2228799751447531803688081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11886932007720169619669765 2228799751447531803688081)
                    ·
                      refine ⟨1671599813585648852766061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2228799751447531803688081 1671599813585648852766061)
                      ·
                        rfl

theorem cell23_3255429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 1, 4, 2].length) (baseStart_3255429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255429 prefixEnd_3255429 := by exact prefixLift 3255429
  have htrace : WordTrace (prefixWord ++ tailWord_3255429) baseStart_3255429 baseEnd_3255429 := by
    simpa [prefixWord, tailWord_3255429, baseEnd_3255429] using wordTrace_append hprefix tailTrace_3255429
  have hstable : (prefixWord ++ tailWord_3255429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255429).length < 2 ^ (prefixWord ++ tailWord_3255429).sum := by decide
  have hdescent : baseEnd_3255429 < baseStart_3255429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255448 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 1, 7]
def baseStart_3255448 : Nat := 118140960795 + 3255448 * 2 ^ 59
def prefixEnd_3255448 : Nat := 4983230072969 + 3 ^ 40 * 3255448 * 2
def baseEnd_3255448 : Nat := 557203189906028092809491

theorem tailTrace_3255448 : CollatzResearch.WordTrace tailWord_3255448 prefixEnd_3255448 557203189906028092809491 := by
  unfold tailWord_3255448
  simp only [CollatzResearch.WordTrace]
  refine ⟨59367971555037678549591499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79157295406716904732788665 59367971555037678549591499)
  ·
    refine ⟨89051957332556517824387249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59367971555037678549591499 89051957332556517824387249)
    ·
      refine ⟨66788967999417388368290437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89051957332556517824387249 66788967999417388368290437)
      ·
        refine ⟨12522931499890760319054457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66788967999417388368290437 12522931499890760319054457)
        ·
          refine ⟨9392198624918070239290843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12522931499890760319054457 9392198624918070239290843)
          ·
            refine ⟨14088297937377105358936265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9392198624918070239290843 14088297937377105358936265)
            ·
              refine ⟨10566223453032829019202199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14088297937377105358936265 10566223453032829019202199)
              ·
                refine ⟨15849335179549243528803299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10566223453032829019202199 15849335179549243528803299)
                ·
                  refine ⟨23774002769323865293204949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15849335179549243528803299 23774002769323865293204949)
                  ·
                    refine ⟨557203189906028092809491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23774002769323865293204949 557203189906028092809491)
                    ·
                      rfl

theorem cell23_3255448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_3255448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255448 prefixEnd_3255448 := by exact prefixLift 3255448
  have htrace : WordTrace (prefixWord ++ tailWord_3255448) baseStart_3255448 baseEnd_3255448 := by
    simpa [prefixWord, tailWord_3255448, baseEnd_3255448] using wordTrace_append hprefix tailTrace_3255448
  have hstable : (prefixWord ++ tailWord_3255448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255448).length < 2 ^ (prefixWord ++ tailWord_3255448).sum := by decide
  have hdescent : baseEnd_3255448 < baseStart_3255448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255452 : List Nat := [2, 2, 3, 2, 1, 4, 1, 3, 5]
def baseStart_3255452 : Nat := 118140960795 + 3255452 * 2 ^ 59
def prefixEnd_3255452 : Nat := 4983230072969 + 3 ^ 40 * 3255452 * 2
def baseEnd_3255452 : Nat := 185734624848966918086495

theorem tailTrace_3255452 : CollatzResearch.WordTrace tailWord_3255452 prefixEnd_3255452 185734624848966918086495 := by
  unfold tailWord_3255452
  simp only [CollatzResearch.WordTrace]
  refine ⟨59368044501030432891164305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79157392668040577188219073 59368044501030432891164305)
  ·
    refine ⟨44526033375772824668373229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59368044501030432891164305 44526033375772824668373229)
    ·
      refine ⟨16697262515914809250639961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44526033375772824668373229 16697262515914809250639961)
      ·
        refine ⟨12522946886936106937979971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16697262515914809250639961 12522946886936106937979971)
        ·
          refine ⟨18784420330404160406969957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12522946886936106937979971 18784420330404160406969957)
          ·
            refine ⟨3522078811950780076306867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18784420330404160406969957 3522078811950780076306867)
            ·
              refine ⟨5283118217926170114460301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3522078811950780076306867 5283118217926170114460301)
              ·
                refine ⟨1981169331722313792922613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5283118217926170114460301 1981169331722313792922613)
                ·
                  refine ⟨185734624848966918086495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1981169331722313792922613 185734624848966918086495)
                  ·
                    rfl

theorem cell23_3255452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 5].length) (baseStart_3255452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255452 prefixEnd_3255452 := by exact prefixLift 3255452
  have htrace : WordTrace (prefixWord ++ tailWord_3255452) baseStart_3255452 baseEnd_3255452 := by
    simpa [prefixWord, tailWord_3255452, baseEnd_3255452] using wordTrace_append hprefix tailTrace_3255452
  have hstable : (prefixWord ++ tailWord_3255452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255452).length < 2 ^ (prefixWord ++ tailWord_3255452).sum := by decide
  have hdescent : baseEnd_3255452 < baseStart_3255452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255469 : List Nat := [1, 5, 2, 1, 3, 1, 3, 2, 5]
def baseStart_3255469 : Nat := 118140960795 + 3255469 * 2 ^ 59
def prefixEnd_3255469 : Nat := 4983230072969 + 3 ^ 40 * 3255469 * 2
def baseEnd_3255469 : Nat := 185735594756869855140653

theorem tailTrace_3255469 : CollatzResearch.WordTrace tailWord_3255469 prefixEnd_3255469 185735594756869855140653 := by
  unfold tailWord_3255469
  simp only [CollatzResearch.WordTrace]
  refine ⟨118736709042999277685697461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79157806028666185123798307 118736709042999277685697461)
  ·
    refine ⟨11131566472781182283034137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118736709042999277685697461 11131566472781182283034137)
    ·
      refine ⟨8348674854585886712275603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11131566472781182283034137 8348674854585886712275603)
      ·
        refine ⟨12523012281878830068413405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8348674854585886712275603 12523012281878830068413405)
        ·
          refine ⟨4696129605704561275655027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12523012281878830068413405 4696129605704561275655027)
          ·
            refine ⟨7044194408556841913482541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4696129605704561275655027 7044194408556841913482541)
            ·
              refine ⟨2641572903208815717555953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7044194408556841913482541 2641572903208815717555953)
              ·
                refine ⟨1981179677406611788166965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2641572903208815717555953 1981179677406611788166965)
                ·
                  refine ⟨185735594756869855140653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1981179677406611788166965 185735594756869855140653)
                  ·
                    rfl

theorem cell23_3255469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_3255469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255469 prefixEnd_3255469 := by exact prefixLift 3255469
  have htrace : WordTrace (prefixWord ++ tailWord_3255469) baseStart_3255469 baseEnd_3255469 := by
    simpa [prefixWord, tailWord_3255469, baseEnd_3255469] using wordTrace_append hprefix tailTrace_3255469
  have hstable : (prefixWord ++ tailWord_3255469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255469).length < 2 ^ (prefixWord ++ tailWord_3255469).sum := by decide
  have hdescent : baseEnd_3255469 < baseStart_3255469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255485 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 2, 4, 2]
def baseStart_3255485 : Nat := 118140960795 + 3255485 * 2 ^ 59
def prefixEnd_3255485 : Nat := 4983230072969 + 3 ^ 40 * 3255485 * 2
def baseEnd_3255485 : Nat := 1671628568502300633665803

theorem tailTrace_3255485 : CollatzResearch.WordTrace tailWord_3255485 prefixEnd_3255485 1671628568502300633665803 := by
  unfold tailWord_3255485
  simp only [CollatzResearch.WordTrace]
  refine ⟨118737292610941312418279909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79158195073960874945519939 118737292610941312418279909)
  ·
    refine ⟨22263242364551496078427483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118737292610941312418279909 22263242364551496078427483)
    ·
      refine ⟨33394863546827244117641225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22263242364551496078427483 33394863546827244117641225)
      ·
        refine ⟨25046147660120433088230919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33394863546827244117641225 25046147660120433088230919)
        ·
          refine ⟨37569221490180649632346379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25046147660120433088230919 37569221490180649632346379)
          ·
            refine ⟨56353832235270974448519569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37569221490180649632346379 56353832235270974448519569)
            ·
              refine ⟨42265374176453230836389677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56353832235270974448519569 42265374176453230836389677)
              ·
                refine ⟨15849515316169961563646129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42265374176453230836389677 15849515316169961563646129)
                ·
                  refine ⟨11887136487127471172734597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15849515316169961563646129 11887136487127471172734597)
                  ·
                    refine ⟨2228838091336400844887737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11887136487127471172734597 2228838091336400844887737)
                    ·
                      refine ⟨1671628568502300633665803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2228838091336400844887737 1671628568502300633665803)
                      ·
                        rfl

theorem cell23_3255485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_3255485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255485 prefixEnd_3255485 := by exact prefixLift 3255485
  have htrace : WordTrace (prefixWord ++ tailWord_3255485) baseStart_3255485 baseEnd_3255485 := by
    simpa [prefixWord, tailWord_3255485, baseEnd_3255485] using wordTrace_append hprefix tailTrace_3255485
  have hstable : (prefixWord ++ tailWord_3255485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255485).length < 2 ^ (prefixWord ++ tailWord_3255485).sum := by decide
  have hdescent : baseEnd_3255485 < baseStart_3255485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255491 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 10]
def baseStart_3255491 : Nat := 118140960795 + 3255491 * 2 ^ 59
def prefixEnd_3255491 : Nat := 4983230072969 + 3 ^ 40 * 3255491 * 2
def baseEnd_3255491 : Nat := 185736849931803067798975

theorem tailTrace_3255491 : CollatzResearch.WordTrace tailWord_3255491 prefixEnd_3255491 185736849931803067798975 := by
  unfold tailWord_3255491
  simp only [CollatzResearch.WordTrace]
  refine ⟨118737511448919575442998327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79158340965946383628665551 118737511448919575442998327)
  ·
    refine ⟨178106267173379363164497491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118737511448919575442998327 178106267173379363164497491)
    ·
      refine ⟨267159400760069044746746237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178106267173379363164497491 267159400760069044746746237)
      ·
        refine ⟨100184775285025891780029839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267159400760069044746746237 100184775285025891780029839)
        ·
          refine ⟨150277162927538837670044759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100184775285025891780029839 150277162927538837670044759)
          ·
            refine ⟨225415744391308256505067139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150277162927538837670044759 225415744391308256505067139)
            ·
              refine ⟨338123616586962384757600709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225415744391308256505067139 338123616586962384757600709)
              ·
                refine ⟨63398178110055447142050133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 338123616586962384757600709 63398178110055447142050133)
                ·
                  refine ⟨185736849931803067798975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 63398178110055447142050133 185736849931803067798975)
                  ·
                    rfl

theorem cell23_3255491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 10].length) (baseStart_3255491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255491 prefixEnd_3255491 := by exact prefixLift 3255491
  have htrace : WordTrace (prefixWord ++ tailWord_3255491) baseStart_3255491 baseEnd_3255491 := by
    simpa [prefixWord, tailWord_3255491, baseEnd_3255491] using wordTrace_append hprefix tailTrace_3255491
  have hstable : (prefixWord ++ tailWord_3255491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255491).length < 2 ^ (prefixWord ++ tailWord_3255491).sum := by decide
  have hdescent : baseEnd_3255491 < baseStart_3255491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255502 : List Nat := [4, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4]
def baseStart_3255502 : Nat := 118140960795 + 3255502 * 2 ^ 59
def prefixEnd_3255502 : Nat := 4983230072969 + 3 ^ 40 * 3255502 * 2
def baseEnd_3255502 : Nat := 1671637297673427067153225

theorem tailTrace_3255502 : CollatzResearch.WordTrace tailWord_3255502 prefixEnd_3255502 1671637297673427067153225 := by
  unfold tailWord_3255502
  simp only [CollatzResearch.WordTrace]
  refine ⟨14842239081484965540206095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79158608434586482881099173 14842239081484965540206095)
  ·
    refine ⟨22263358622227448310309143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14842239081484965540206095 22263358622227448310309143)
    ·
      refine ⟨33395037933341172465463715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22263358622227448310309143 33395037933341172465463715)
      ·
        refine ⟨50092556900011758698195573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33395037933341172465463715 50092556900011758698195573)
        ·
          refine ⟨4696177209376102377955835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50092556900011758698195573 4696177209376102377955835)
          ·
            refine ⟨7044265814064153566933753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4696177209376102377955835 7044265814064153566933753)
            ·
              refine ⟨5283199360548115175200315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7044265814064153566933753 5283199360548115175200315)
              ·
                refine ⟨7924799040822172762800473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5283199360548115175200315 7924799040822172762800473)
                ·
                  refine ⟨5943599280616629572100355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7924799040822172762800473 5943599280616629572100355)
                  ·
                    refine ⟨8915398920924944358150533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5943599280616629572100355 8915398920924944358150533)
                    ·
                      refine ⟨1671637297673427067153225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8915398920924944358150533 1671637297673427067153225)
                      ·
                        rfl

theorem cell23_3255502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_3255502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255502 prefixEnd_3255502 := by exact prefixLift 3255502
  have htrace : WordTrace (prefixWord ++ tailWord_3255502) baseStart_3255502 baseEnd_3255502 := by
    simpa [prefixWord, tailWord_3255502, baseEnd_3255502] using wordTrace_append hprefix tailTrace_3255502
  have hstable : (prefixWord ++ tailWord_3255502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255502).length < 2 ^ (prefixWord ++ tailWord_3255502).sum := by decide
  have hdescent : baseEnd_3255502 < baseStart_3255502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255528 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_3255528 : Nat := 118140960795 + 3255528 * 2 ^ 59
def prefixEnd_3255528 : Nat := 4983230072969 + 3 ^ 40 * 3255528 * 2
def baseEnd_3255528 : Nat := 1671650648170443965428105

theorem tailTrace_3255528 : CollatzResearch.WordTrace tailWord_3255528 prefixEnd_3255528 1671650648170443965428105 := by
  unfold tailWord_3255528
  simp only [CollatzResearch.WordTrace]
  refine ⟨59369430474892765381047619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79159240633190353841396825 59369430474892765381047619)
  ·
    refine ⟨89054145712339148071571429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59369430474892765381047619 89054145712339148071571429)
    ·
      refine ⟨16697652321063590263419643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89054145712339148071571429 16697652321063590263419643)
      ·
        refine ⟨25046478481595385395129465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16697652321063590263419643 25046478481595385395129465)
        ·
          refine ⟨18784858861196539046347099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25046478481595385395129465 18784858861196539046347099)
          ·
            refine ⟨28177288291794808569520649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18784858861196539046347099 28177288291794808569520649)
            ·
              refine ⟨21132966218846106427140487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28177288291794808569520649 21132966218846106427140487)
              ·
                refine ⟨31699449328269159640710731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21132966218846106427140487 31699449328269159640710731)
                ·
                  refine ⟨47549173992403739461066097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31699449328269159640710731 47549173992403739461066097)
                  ·
                    refine ⟨35661880494302804595799573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47549173992403739461066097 35661880494302804595799573)
                    ·
                      refine ⟨1671650648170443965428105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35661880494302804595799573 1671650648170443965428105)
                      ·
                        rfl

theorem cell23_3255528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_3255528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255528 prefixEnd_3255528 := by exact prefixLift 3255528
  have htrace : WordTrace (prefixWord ++ tailWord_3255528) baseStart_3255528 baseEnd_3255528 := by
    simpa [prefixWord, tailWord_3255528, baseEnd_3255528] using wordTrace_append hprefix tailTrace_3255528
  have hstable : (prefixWord ++ tailWord_3255528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255528).length < 2 ^ (prefixWord ++ tailWord_3255528).sum := by decide
  have hdescent : baseEnd_3255528 < baseStart_3255528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255545 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 1, 5, 2]
def baseStart_3255545 : Nat := 118140960795 + 3255545 * 2 ^ 59
def prefixEnd_3255545 : Nat := 4983230072969 + 3 ^ 40 * 3255545 * 2
def baseEnd_3255545 : Nat := 1671659377341570398915527

theorem tailTrace_3255545 : CollatzResearch.WordTrace tailWord_3255545 prefixEnd_3255545 1671659377341570398915527 := by
  unfold tailWord_3255545
  simp only [CollatzResearch.WordTrace]
  refine ⟨118739480990723942665464089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79159653993815961776976059 118739480990723942665464089)
  ·
    refine ⟨89054610743042956999098067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118739480990723942665464089 89054610743042956999098067)
    ·
      refine ⟨133581916114564435498647101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89054610743042956999098067 133581916114564435498647101)
      ·
        refine ⟨50093218542961663311992663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133581916114564435498647101 50093218542961663311992663)
        ·
          refine ⟨75139827814442494967988995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50093218542961663311992663 75139827814442494967988995)
          ·
            refine ⟨112709741721663742451983493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75139827814442494967988995 112709741721663742451983493)
            ·
              refine ⟨21133076572811951709746905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112709741721663742451983493 21133076572811951709746905)
              ·
                refine ⟨15849807429608963782310179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21133076572811951709746905 15849807429608963782310179)
                ·
                  refine ⟨23774711144413445673465269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15849807429608963782310179 23774711144413445673465269)
                  ·
                    refine ⟨2228879169788760531887369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23774711144413445673465269 2228879169788760531887369)
                    ·
                      refine ⟨1671659377341570398915527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2228879169788760531887369 1671659377341570398915527)
                      ·
                        rfl

theorem cell23_3255545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 5, 2].length) (baseStart_3255545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255545 prefixEnd_3255545 := by exact prefixLift 3255545
  have htrace : WordTrace (prefixWord ++ tailWord_3255545) baseStart_3255545 baseEnd_3255545 := by
    simpa [prefixWord, tailWord_3255545, baseEnd_3255545] using wordTrace_append hprefix tailTrace_3255545
  have hstable : (prefixWord ++ tailWord_3255545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255545).length < 2 ^ (prefixWord ++ tailWord_3255545).sum := by decide
  have hdescent : baseEnd_3255545 < baseStart_3255545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255569 : List Nat := [1, 2, 2, 1, 1, 4, 4, 3, 1, 1, 3]
def baseStart_3255569 : Nat := 118140960795 + 3255569 * 2 ^ 59
def prefixEnd_3255569 : Nat := 4983230072969 + 3 ^ 40 * 3255569 * 2
def baseEnd_3255569 : Nat := 1671671700877278305015417

theorem tailTrace_3255569 : CollatzResearch.WordTrace tailWord_3255569 prefixEnd_3255569 1671671700877278305015417 := by
  unfold tailWord_3255569
  simp only [CollatzResearch.WordTrace]
  refine ⟨118740356342636994764337761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79160237561757996509558507 118740356342636994764337761)
  ·
    refine ⟨89055267256977746073253321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118740356342636994764337761 89055267256977746073253321)
    ·
      refine ⟨66791450442733309554939991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89055267256977746073253321 66791450442733309554939991)
      ·
        refine ⟨100187175664099964332409987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66791450442733309554939991 100187175664099964332409987)
        ·
          refine ⟨150280763496149946498614981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100187175664099964332409987 150280763496149946498614981)
          ·
            refine ⟨28177643155528114968490309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150280763496149946498614981 28177643155528114968490309)
            ·
              refine ⟨5283308091661521556591933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28177643155528114968490309 5283308091661521556591933)
              ·
                refine ⟨1981240534373070583721975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5283308091661521556591933 1981240534373070583721975)
                ·
                  refine ⟨2971860801559605875582963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1981240534373070583721975 2971860801559605875582963)
                  ·
                    refine ⟨4457791202339408813374445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2971860801559605875582963 4457791202339408813374445)
                    ·
                      refine ⟨1671671700877278305015417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4457791202339408813374445 1671671700877278305015417)
                      ·
                        rfl

theorem cell23_3255569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 1, 1, 3].length) (baseStart_3255569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255569 prefixEnd_3255569 := by exact prefixLift 3255569
  have htrace : WordTrace (prefixWord ++ tailWord_3255569) baseStart_3255569 baseEnd_3255569 := by
    simpa [prefixWord, tailWord_3255569, baseEnd_3255569] using wordTrace_append hprefix tailTrace_3255569
  have hstable : (prefixWord ++ tailWord_3255569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255569).length < 2 ^ (prefixWord ++ tailWord_3255569).sum := by decide
  have hdescent : baseEnd_3255569 < baseStart_3255569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255602 : List Nat := [3, 2, 1, 1, 4, 3, 1, 1, 1, 6]
def baseStart_3255602 : Nat := 118140960795 + 3255602 * 2 ^ 59
def prefixEnd_3255602 : Nat := 4983230072969 + 3 ^ 40 * 3255602 * 2
def baseEnd_3255602 : Nat := 557229548579625558634255

theorem tailTrace_3255602 : CollatzResearch.WordTrace tailWord_3255602 prefixEnd_3255602 557229548579625558634255 := by
  unfold tailWord_3255602
  simp only [CollatzResearch.WordTrace]
  refine ⟨29685389987879360350072265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79161039967678294266859373 29685389987879360350072265)
  ·
    refine ⟨22264042490909520262554199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29685389987879360350072265 22264042490909520262554199)
    ·
      refine ⟨33396063736364280393831299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22264042490909520262554199 33396063736364280393831299)
      ·
        refine ⟨50094095604546420590746949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33396063736364280393831299 50094095604546420590746949)
        ·
          refine ⟨9392642925852453860765053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50094095604546420590746949 9392642925852453860765053)
          ·
            refine ⟨3522241097194670197786895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9392642925852453860765053 3522241097194670197786895)
            ·
              refine ⟨5283361645792005296680343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3522241097194670197786895 5283361645792005296680343)
              ·
                refine ⟨7925042468688007945020515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5283361645792005296680343 7925042468688007945020515)
                ·
                  refine ⟨11887563703032011917530773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7925042468688007945020515 11887563703032011917530773)
                  ·
                    refine ⟨557229548579625558634255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11887563703032011917530773 557229548579625558634255)
                    ·
                      rfl

theorem cell23_3255602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_3255602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255602 prefixEnd_3255602 := by exact prefixLift 3255602
  have htrace : WordTrace (prefixWord ++ tailWord_3255602) baseStart_3255602 baseEnd_3255602 := by
    simpa [prefixWord, tailWord_3255602, baseEnd_3255602] using wordTrace_append hprefix tailTrace_3255602
  have hstable : (prefixWord ++ tailWord_3255602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255602).length < 2 ^ (prefixWord ++ tailWord_3255602).sum := by decide
  have hdescent : baseEnd_3255602 < baseStart_3255602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255605 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_3255605 : Nat := 118140960795 + 3255605 * 2 ^ 59
def prefixEnd_3255605 : Nat := 4983230072969 + 3 ^ 40 * 3255605 * 2
def baseEnd_3255605 : Nat := 1671690186180840164165251

theorem tailTrace_3255605 : CollatzResearch.WordTrace tailWord_3255605 prefixEnd_3255605 1671690186180840164165251 := by
  unfold tailWord_3255605
  simp only [CollatzResearch.WordTrace]
  refine ⟨118741669370506572912648269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79161112913671048608432179 118741669370506572912648269)
  ·
    refine ⟨44528126013939964842243101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118741669370506572912648269 44528126013939964842243101)
    ·
      refine ⟨16698047255227486815841163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44528126013939964842243101 16698047255227486815841163)
      ·
        refine ⟨25047070882841230223761745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16698047255227486815841163 25047070882841230223761745)
        ·
          refine ⟨18785303162130922667821309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25047070882841230223761745 18785303162130922667821309)
          ·
            refine ⟨7044488685799096000432991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18785303162130922667821309 7044488685799096000432991)
            ·
              refine ⟨10566733028698644000649487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7044488685799096000432991 10566733028698644000649487)
              ·
                refine ⟨15850099543047966000974231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10566733028698644000649487 15850099543047966000974231)
                ·
                  refine ⟨23775149314571949001461347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15850099543047966000974231 23775149314571949001461347)
                  ·
                    refine ⟨35662723971857923502192021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23775149314571949001461347 35662723971857923502192021)
                    ·
                      refine ⟨1671690186180840164165251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35662723971857923502192021 1671690186180840164165251)
                      ·
                        rfl

theorem cell23_3255605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_3255605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255605 prefixEnd_3255605 := by exact prefixLift 3255605
  have htrace : WordTrace (prefixWord ++ tailWord_3255605) baseStart_3255605 baseEnd_3255605 := by
    simpa [prefixWord, tailWord_3255605, baseEnd_3255605] using wordTrace_append hprefix tailTrace_3255605
  have hstable : (prefixWord ++ tailWord_3255605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255605).length < 2 ^ (prefixWord ++ tailWord_3255605).sum := by decide
  have hdescent : baseEnd_3255605 < baseStart_3255605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255606 : List Nat := [5, 1, 2, 3, 1, 1, 2, 2, 1, 5]
def baseStart_3255606 : Nat := 118140960795 + 3255606 * 2 ^ 59
def prefixEnd_3255606 : Nat := 4983230072969 + 3 ^ 40 * 3255606 * 2
def baseEnd_3255606 : Nat := 557230233220498220084249

theorem tailTrace_3255606 : CollatzResearch.WordTrace tailWord_3255606 prefixEnd_3255606 557230233220498220084249 := by
  unfold tailWord_3255606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7421356615218934380214667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79161137229001966722289781 7421356615218934380214667)
  ·
    refine ⟨11132034922828401570322001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7421356615218934380214667 11132034922828401570322001)
    ·
      refine ⟨8349026192121301177741501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11132034922828401570322001 8349026192121301177741501)
      ·
        refine ⟨3130884822045487941653063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8349026192121301177741501 3130884822045487941653063)
        ·
          refine ⟨4696327233068231912479595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3130884822045487941653063 4696327233068231912479595)
          ·
            refine ⟨7044490849602347868719393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4696327233068231912479595 7044490849602347868719393)
            ·
              refine ⟨5283368137201760901539545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7044490849602347868719393 5283368137201760901539545)
              ·
                refine ⟨3962526102901320676154659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5283368137201760901539545 3962526102901320676154659)
                ·
                  refine ⟨5943789154351981014231989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3962526102901320676154659 5943789154351981014231989)
                  ·
                    refine ⟨557230233220498220084249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5943789154351981014231989 557230233220498220084249)
                    ·
                      rfl

theorem cell23_3255606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_3255606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255606 prefixEnd_3255606 := by exact prefixLift 3255606
  have htrace : WordTrace (prefixWord ++ tailWord_3255606) baseStart_3255606 baseEnd_3255606 := by
    simpa [prefixWord, tailWord_3255606, baseEnd_3255606] using wordTrace_append hprefix tailTrace_3255606
  have hstable : (prefixWord ++ tailWord_3255606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255606).length < 2 ^ (prefixWord ++ tailWord_3255606).sum := by decide
  have hdescent : baseEnd_3255606 < baseStart_3255606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255609 : List Nat := [1, 2, 1, 6, 2, 1, 2, 2, 1, 1, 4]
def baseStart_3255609 : Nat := 118140960795 + 3255609 * 2 ^ 59
def prefixEnd_3255609 : Nat := 4983230072969 + 3 ^ 40 * 3255609 * 2
def baseEnd_3255609 : Nat := 1671692240103458148515233

theorem tailTrace_3255609 : CollatzResearch.WordTrace tailWord_3255609 prefixEnd_3255609 1671692240103458148515233 := by
  unfold tailWord_3255609
  simp only [CollatzResearch.WordTrace]
  refine ⟨118741815262492081595793881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79161210174994721063862587 118741815262492081595793881)
  ·
    refine ⟨89056361446869061196845411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118741815262492081595793881 89056361446869061196845411)
    ·
      refine ⟨133584542170303591795268117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89056361446869061196845411 133584542170303591795268117)
      ·
        refine ⟨6261775414232980865403193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 133584542170303591795268117 6261775414232980865403193)
        ·
          refine ⟨4696331560674735649052395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6261775414232980865403193 4696331560674735649052395)
          ·
            refine ⟨7044497341012103473578593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4696331560674735649052395 7044497341012103473578593)
            ·
              refine ⟨5283373005759077605183945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7044497341012103473578593 5283373005759077605183945)
              ·
                refine ⟨3962529754319308203887959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5283373005759077605183945 3962529754319308203887959)
                ·
                  refine ⟨5943794631478962305831939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3962529754319308203887959 5943794631478962305831939)
                  ·
                    refine ⟨8915691947218443458747909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5943794631478962305831939 8915691947218443458747909)
                    ·
                      refine ⟨1671692240103458148515233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8915691947218443458747909 1671692240103458148515233)
                      ·
                        rfl

theorem cell23_3255609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_3255609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255609 prefixEnd_3255609 := by exact prefixLift 3255609
  have htrace : WordTrace (prefixWord ++ tailWord_3255609) baseStart_3255609 baseEnd_3255609 := by
    simpa [prefixWord, tailWord_3255609, baseEnd_3255609] using wordTrace_append hprefix tailTrace_3255609
  have hstable : (prefixWord ++ tailWord_3255609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255609).length < 2 ^ (prefixWord ++ tailWord_3255609).sum := by decide
  have hdescent : baseEnd_3255609 < baseStart_3255609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255612 : List Nat := [2, 2, 2, 2, 1, 3, 1, 4, 1, 2, 3]
def baseStart_3255612 : Nat := 118140960795 + 3255612 * 2 ^ 59
def prefixEnd_3255612 : Nat := 4983230072969 + 3 ^ 40 * 3255612 * 2
def baseEnd_3255612 : Nat := 1671693780545421636777719

theorem tailTrace_3255612 : CollatzResearch.WordTrace tailWord_3255612 prefixEnd_3255612 1671693780545421636777719 := by
  unfold tailWord_3255612
  simp only [CollatzResearch.WordTrace]
  refine ⟨59370962340740606554076545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79161283120987475405435393 59370962340740606554076545)
  ·
    refine ⟨44528221755555454915557409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59370962340740606554076545 44528221755555454915557409)
    ·
      refine ⟨33396166316666591186668057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44528221755555454915557409 33396166316666591186668057)
      ·
        refine ⟨25047124737499943390001043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33396166316666591186668057 25047124737499943390001043)
        ·
          refine ⟨37570687106249915085001565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25047124737499943390001043 37570687106249915085001565)
          ·
            refine ⟨14089007664843718156875587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37570687106249915085001565 14089007664843718156875587)
            ·
              refine ⟨21133511497265577235313381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14089007664843718156875587 21133511497265577235313381)
              ·
                refine ⟨3962533405737295731621259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21133511497265577235313381 3962533405737295731621259)
                ·
                  refine ⟨5943800108605943597431889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3962533405737295731621259 5943800108605943597431889)
                  ·
                    refine ⟨4457850081454457698073917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5943800108605943597431889 4457850081454457698073917)
                    ·
                      refine ⟨1671693780545421636777719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4457850081454457698073917 1671693780545421636777719)
                      ·
                        rfl

theorem cell23_3255612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_3255612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255612 prefixEnd_3255612 := by exact prefixLift 3255612
  have htrace : WordTrace (prefixWord ++ tailWord_3255612) baseStart_3255612 baseEnd_3255612 := by
    simpa [prefixWord, tailWord_3255612, baseEnd_3255612] using wordTrace_append hprefix tailTrace_3255612
  have hstable : (prefixWord ++ tailWord_3255612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255612).length < 2 ^ (prefixWord ++ tailWord_3255612).sum := by decide
  have hdescent : baseEnd_3255612 < baseStart_3255612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255615 : List Nat := [1, 1, 2, 2, 4, 2, 4, 7]
def baseStart_3255615 : Nat := 118140960795 + 3255615 * 2 ^ 59
def prefixEnd_3255615 : Nat := 4983230072969 + 3 ^ 40 * 3255615 * 2
def baseEnd_3255615 : Nat := 61914641518051300927415

theorem tailTrace_3255615 : CollatzResearch.WordTrace tailWord_3255615 prefixEnd_3255615 61914641518051300927415 := by
  unfold tailWord_3255615
  simp only [CollatzResearch.WordTrace]
  refine ⟨118742034100470344620512299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79161356066980229747008199 118742034100470344620512299)
  ·
    refine ⟨178113051150705516930768449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118742034100470344620512299 178113051150705516930768449)
    ·
      refine ⟨133584788363029137698076337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178113051150705516930768449 133584788363029137698076337)
      ·
        refine ⟨100188591272271853273557253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133584788363029137698076337 100188591272271853273557253)
        ·
          refine ⟨18785360863550972488791985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100188591272271853273557253 18785360863550972488791985)
          ·
            refine ⟨14089020647663229366593989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18785360863550972488791985 14089020647663229366593989)
            ·
              refine ⟨2641691371436855506236373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14089020647663229366593989 2641691371436855506236373)
              ·
                refine ⟨61914641518051300927415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2641691371436855506236373 61914641518051300927415)
                ·
                  rfl

theorem cell23_3255615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 7].length) (baseStart_3255615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255615 prefixEnd_3255615 := by exact prefixLift 3255615
  have htrace : WordTrace (prefixWord ++ tailWord_3255615) baseStart_3255615 baseEnd_3255615 := by
    simpa [prefixWord, tailWord_3255615, baseEnd_3255615] using wordTrace_append hprefix tailTrace_3255615
  have hstable : (prefixWord ++ tailWord_3255615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255615).length < 2 ^ (prefixWord ++ tailWord_3255615).sum := by decide
  have hdescent : baseEnd_3255615 < baseStart_3255615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255625 : List Nat := [1, 2, 1, 1, 2, 3, 2, 4, 1, 3, 3]
def baseStart_3255625 : Nat := 118140960795 + 3255625 * 2 ^ 59
def prefixEnd_3255625 : Nat := 4983230072969 + 3 ^ 40 * 3255625 * 2
def baseEnd_3255625 : Nat := 1671700455793930085915159

theorem tailTrace_3255625 : CollatzResearch.WordTrace tailWord_3255625 prefixEnd_3255625 1671700455793930085915159 := by
  unfold tailWord_3255625
  simp only [CollatzResearch.WordTrace]
  refine ⟨118742398830434116328376329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79161599220289410885584219 118742398830434116328376329)
  ·
    refine ⟨89056799122825587246282247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118742398830434116328376329 89056799122825587246282247)
    ·
      refine ⟨133585198684238380869423371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89056799122825587246282247 133585198684238380869423371)
      ·
        refine ⟨200377798026357571304135057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133585198684238380869423371 200377798026357571304135057)
        ·
          refine ⟨150283348519768178478101293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200377798026357571304135057 150283348519768178478101293)
          ·
            refine ⟨56356255694913066929287985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150283348519768178478101293 56356255694913066929287985)
            ·
              refine ⟨42267191771184800196965989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56356255694913066929287985 42267191771184800196965989)
              ·
                refine ⟨7925098457097150036931123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42267191771184800196965989 7925098457097150036931123)
                ·
                  refine ⟨11887647685645725055396685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7925098457097150036931123 11887647685645725055396685)
                  ·
                    refine ⟨4457867882117146895773757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11887647685645725055396685 4457867882117146895773757)
                    ·
                      refine ⟨1671700455793930085915159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4457867882117146895773757 1671700455793930085915159)
                      ·
                        rfl

theorem cell23_3255625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 3, 3].length) (baseStart_3255625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255625 prefixEnd_3255625 := by exact prefixLift 3255625
  have htrace : WordTrace (prefixWord ++ tailWord_3255625) baseStart_3255625 baseEnd_3255625 := by
    simpa [prefixWord, tailWord_3255625, baseEnd_3255625] using wordTrace_append hprefix tailTrace_3255625
  have hstable : (prefixWord ++ tailWord_3255625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255625).length < 2 ^ (prefixWord ++ tailWord_3255625).sum := by decide
  have hdescent : baseEnd_3255625 < baseStart_3255625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255642 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3]
def baseStart_3255642 : Nat := 118140960795 + 3255642 * 2 ^ 59
def prefixEnd_3255642 : Nat := 4983230072969 + 3 ^ 40 * 3255642 * 2
def baseEnd_3255642 : Nat := 1671709184965056519402581

theorem tailTrace_3255642 : CollatzResearch.WordTrace tailWord_3255642 prefixEnd_3255642 1671709184965056519402581 := by
  unfold tailWord_3255642
  simp only [CollatzResearch.WordTrace]
  refine ⟨29685754717843132057936295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79162012580915018821163453 29685754717843132057936295)
  ·
    refine ⟨44528632076764698086904443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29685754717843132057936295 44528632076764698086904443)
    ·
      refine ⟨66792948115147047130356665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44528632076764698086904443 66792948115147047130356665)
      ·
        refine ⟨50094711086360285347767499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66792948115147047130356665 50094711086360285347767499)
        ·
          refine ⟨75142066629540428021651249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50094711086360285347767499 75142066629540428021651249)
          ·
            refine ⟨56356549972155321016238437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75142066629540428021651249 56356549972155321016238437)
            ·
              refine ⟨10566853119779122690544707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56356549972155321016238437 10566853119779122690544707)
              ·
                refine ⟨15850279679668684035817061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10566853119779122690544707 15850279679668684035817061)
                ·
                  refine ⟨2971927439937878256715699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15850279679668684035817061 2971927439937878256715699)
                  ·
                    refine ⟨4457891159906817385073549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2971927439937878256715699 4457891159906817385073549)
                    ·
                      refine ⟨1671709184965056519402581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4457891159906817385073549 1671709184965056519402581)
                      ·
                        rfl

theorem cell23_3255642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_3255642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255642 prefixEnd_3255642 := by exact prefixLift 3255642
  have htrace : WordTrace (prefixWord ++ tailWord_3255642) baseStart_3255642 baseEnd_3255642 := by
    simpa [prefixWord, tailWord_3255642, baseEnd_3255642] using wordTrace_append hprefix tailTrace_3255642
  have hstable : (prefixWord ++ tailWord_3255642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255642).length < 2 ^ (prefixWord ++ tailWord_3255642).sum := by decide
  have hdescent : baseEnd_3255642 < baseStart_3255642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255685 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 2, 1, 5]
def baseStart_3255685 : Nat := 118140960795 + 3255685 * 2 ^ 59
def prefixEnd_3255685 : Nat := 4983230072969 + 3 ^ 40 * 3255685 * 2
def baseEnd_3255685 : Nat := 1671731264633199851164883

theorem tailTrace_3255685 : CollatzResearch.WordTrace tailWord_3255685 prefixEnd_3255685 1671731264633199851164883 := by
  unfold tailWord_3255685
  simp only [CollatzResearch.WordTrace]
  refine ⟨118744587210216746575560509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79163058140144497717040339 118744587210216746575560509)
  ·
    refine ⟨44529220203831279965835191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118744587210216746575560509 44529220203831279965835191)
    ·
      refine ⟨66793830305746919948752787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44529220203831279965835191 66793830305746919948752787)
      ·
        refine ⟨100190745458620379923129181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66793830305746919948752787 100190745458620379923129181)
        ·
          refine ⟨37571529546982642471173443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100190745458620379923129181 37571529546982642471173443)
          ·
            refine ⟨56357294320473963706760165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37571529546982642471173443 56357294320473963706760165)
            ·
              refine ⟨10566992685088868195017531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56357294320473963706760165 10566992685088868195017531)
              ·
                refine ⟨15850489027633302292526297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10566992685088868195017531 15850489027633302292526297)
                ·
                  refine ⟨11887866770724976719394723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15850489027633302292526297 11887866770724976719394723)
                  ·
                    refine ⟨17831800156087465079092085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11887866770724976719394723 17831800156087465079092085)
                    ·
                      refine ⟨1671731264633199851164883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17831800156087465079092085 1671731264633199851164883)
                      ·
                        rfl

theorem cell23_3255685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_3255685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255685 prefixEnd_3255685 := by exact prefixLift 3255685
  have htrace : WordTrace (prefixWord ++ tailWord_3255685) baseStart_3255685 baseEnd_3255685 := by
    simpa [prefixWord, tailWord_3255685, baseEnd_3255685] using wordTrace_append hprefix tailTrace_3255685
  have hstable : (prefixWord ++ tailWord_3255685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255685).length < 2 ^ (prefixWord ++ tailWord_3255685).sum := by decide
  have hdescent : baseEnd_3255685 < baseStart_3255685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255735 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 1, 7]
def baseStart_3255735 : Nat := 118140960795 + 3255735 * 2 ^ 59
def prefixEnd_3255735 : Nat := 4983230072969 + 3 ^ 40 * 3255735 * 2
def baseEnd_3255735 : Nat := 557252312888641551846551

theorem tailTrace_3255735 : CollatzResearch.WordTrace tailWord_3255735 prefixEnd_3255735 557252312888641551846551 := by
  unfold tailWord_3255735
  simp only [CollatzResearch.WordTrace]
  refine ⟨118746410860035605114880659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79164273906690403409920439 118746410860035605114880659)
  ·
    refine ⟨178119616290053407672320989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118746410860035605114880659 178119616290053407672320989)
    ·
      refine ⟨66794856108770027877120371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178119616290053407672320989 66794856108770027877120371)
      ·
        refine ⟨100192284163155041815680557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66794856108770027877120371 100192284163155041815680557)
        ·
          refine ⟨37572106561183140680880209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100192284163155041815680557 37572106561183140680880209)
          ·
            refine ⟨28179079920887355510660157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37572106561183140680880209 28179079920887355510660157)
            ·
              refine ⟨10567154970332758316497559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28179079920887355510660157 10567154970332758316497559)
              ·
                refine ⟨15850732455499137474746339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10567154970332758316497559 15850732455499137474746339)
                ·
                  refine ⟨23776098683248706212119509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15850732455499137474746339 23776098683248706212119509)
                  ·
                    refine ⟨557252312888641551846551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23776098683248706212119509 557252312888641551846551)
                    ·
                      rfl

theorem cell23_3255735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_3255735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255735 prefixEnd_3255735 := by exact prefixLift 3255735
  have htrace : WordTrace (prefixWord ++ tailWord_3255735) baseStart_3255735 baseEnd_3255735 := by
    simpa [prefixWord, tailWord_3255735, baseEnd_3255735] using wordTrace_append hprefix tailTrace_3255735
  have hstable : (prefixWord ++ tailWord_3255735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255735).length < 2 ^ (prefixWord ++ tailWord_3255735).sum := by decide
  have hdescent : baseEnd_3255735 < baseStart_3255735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255792 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 3]
def baseStart_3255792 : Nat := 118140960795 + 3255792 * 2 ^ 59
def prefixEnd_3255792 : Nat := 4983230072969 + 3 ^ 40 * 3255792 * 2
def baseEnd_3255792 : Nat := 1671786207063230932526891

theorem tailTrace_3255792 : CollatzResearch.WordTrace tailWord_3255792 prefixEnd_3255792 1671786207063230932526891 := by
  unfold tailWord_3255792
  simp only [CollatzResearch.WordTrace]
  refine ⟨59374244910414551924852815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79165659880552735899803753 59374244910414551924852815)
  ·
    refine ⟨89061367365621827887279223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59374244910414551924852815 89061367365621827887279223)
    ·
      refine ⟨133592051048432741830918835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89061367365621827887279223 133592051048432741830918835)
      ·
        refine ⟨200388076572649112746378253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133592051048432741830918835 200388076572649112746378253)
        ·
          refine ⟨75145528714743417279891845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200388076572649112746378253 75145528714743417279891845)
          ·
            refine ⟨14089786634014390739979721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75145528714743417279891845 14089786634014390739979721)
            ·
              refine ⟨10567339975510793054984791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14089786634014390739979721 10567339975510793054984791)
              ·
                refine ⟨15851009963266189582477187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10567339975510793054984791 15851009963266189582477187)
                ·
                  refine ⟨23776514944899284373715781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15851009963266189582477187 23776514944899284373715781)
                  ·
                    refine ⟨4458096552168615820071709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23776514944899284373715781 4458096552168615820071709)
                    ·
                      refine ⟨1671786207063230932526891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4458096552168615820071709 1671786207063230932526891)
                      ·
                        rfl

theorem cell23_3255792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 3].length) (baseStart_3255792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255792 prefixEnd_3255792 := by exact prefixLift 3255792
  have htrace : WordTrace (prefixWord ++ tailWord_3255792) baseStart_3255792 baseEnd_3255792 := by
    simpa [prefixWord, tailWord_3255792, baseEnd_3255792] using wordTrace_append hprefix tailTrace_3255792
  have hstable : (prefixWord ++ tailWord_3255792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255792).length < 2 ^ (prefixWord ++ tailWord_3255792).sum := by decide
  have hdescent : baseEnd_3255792 < baseStart_3255792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255799 : List Nat := [1, 1, 3, 1, 1, 1, 1, 9, 1, 4]
def baseStart_3255799 : Nat := 118140960795 + 3255799 * 2 ^ 59
def prefixEnd_3255799 : Nat := 4983230072969 + 3 ^ 40 * 3255799 * 2
def baseEnd_3255799 : Nat := 557263267142604135046453

theorem tailTrace_3255799 : CollatzResearch.WordTrace tailWord_3255799 prefixEnd_3255799 557263267142604135046453 := by
  unfold tailWord_3255799
  simp only [CollatzResearch.WordTrace]
  refine ⟨118748745131803744045210451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79165830087869162696806967 118748745131803744045210451)
  ·
    refine ⟨178123117697705616067815677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118748745131803744045210451 178123117697705616067815677)
    ·
      refine ⟨66796169136639606025430879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178123117697705616067815677 66796169136639606025430879)
      ·
        refine ⟨100194253704959409038146319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66796169136639606025430879 100194253704959409038146319)
        ·
          refine ⟨150291380557439113557219479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100194253704959409038146319 150291380557439113557219479)
          ·
            refine ⟨225437070836158670335829219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150291380557439113557219479 225437070836158670335829219)
            ·
              refine ⟨338155606254238005503743829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225437070836158670335829219 338155606254238005503743829)
              ·
                refine ⟨1981380505395925813498499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 338155606254238005503743829 1981380505395925813498499)
                ·
                  refine ⟨2972070758093888720247749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1981380505395925813498499 2972070758093888720247749)
                  ·
                    refine ⟨557263267142604135046453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2972070758093888720247749 557263267142604135046453)
                    ·
                      rfl

theorem cell23_3255799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 1, 4].length) (baseStart_3255799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255799 prefixEnd_3255799 := by exact prefixLift 3255799
  have htrace : WordTrace (prefixWord ++ tailWord_3255799) baseStart_3255799 baseEnd_3255799 := by
    simpa [prefixWord, tailWord_3255799, baseEnd_3255799] using wordTrace_append hprefix tailTrace_3255799
  have hstable : (prefixWord ++ tailWord_3255799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255799).length < 2 ^ (prefixWord ++ tailWord_3255799).sum := by decide
  have hdescent : baseEnd_3255799 < baseStart_3255799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255829 : List Nat := [1, 3, 2, 1, 3, 2, 4, 1, 6]
def baseStart_3255829 : Nat := 118140960795 + 3255829 * 2 ^ 59
def prefixEnd_3255829 : Nat := 4983230072969 + 3 ^ 40 * 3255829 * 2
def baseEnd_3255829 : Nat := 185756133983049698640469

theorem tailTrace_3255829 : CollatzResearch.WordTrace tailWord_3255829 prefixEnd_3255829 185756133983049698640469 := by
  unfold tailWord_3255829
  simp only [CollatzResearch.WordTrace]
  refine ⟨118749839321695059168802541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79166559547796706112535027 118749839321695059168802541)
  ·
    refine ⟨44531189745635647188300953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118749839321695059168802541 44531189745635647188300953)
    ·
      refine ⟨33398392309226735391225715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44531189745635647188300953 33398392309226735391225715)
      ·
        refine ⟨50097588463840103086838573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33398392309226735391225715 50097588463840103086838573)
        ·
          refine ⟨18786595673940038657564465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50097588463840103086838573 18786595673940038657564465)
          ·
            refine ⟨14089946755455028993173349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18786595673940038657564465 14089946755455028993173349)
            ·
              refine ⟨2641865016647817936220003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14089946755455028993173349 2641865016647817936220003)
              ·
                refine ⟨3962797524971726904330005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2641865016647817936220003 3962797524971726904330005)
                ·
                  refine ⟨185756133983049698640469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3962797524971726904330005 185756133983049698640469)
                  ·
                    rfl

theorem cell23_3255829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 6].length) (baseStart_3255829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255829 prefixEnd_3255829 := by exact prefixLift 3255829
  have htrace : WordTrace (prefixWord ++ tailWord_3255829) baseStart_3255829 baseEnd_3255829 := by
    simpa [prefixWord, tailWord_3255829, baseEnd_3255829] using wordTrace_append hprefix tailTrace_3255829
  have hstable : (prefixWord ++ tailWord_3255829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255829).length < 2 ^ (prefixWord ++ tailWord_3255829).sum := by decide
  have hdescent : baseEnd_3255829 < baseStart_3255829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255839 : List Nat := [1, 1, 2, 4, 1, 1, 2, 4, 3, 1, 3]
def baseStart_3255839 : Nat := 118140960795 + 3255839 * 2 ^ 59
def prefixEnd_3255839 : Nat := 4983230072969 + 3 ^ 40 * 3255839 * 2
def baseEnd_3255839 : Nat := 1671810340653992248639175

theorem tailTrace_3255839 : CollatzResearch.WordTrace tailWord_3255839 prefixEnd_3255839 1671810340653992248639175 := by
  unfold tailWord_3255839
  simp only [CollatzResearch.WordTrace]
  refine ⟨118750204051658830876666571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79166802701105887251111047 118750204051658830876666571)
  ·
    refine ⟨178125306077488246314999857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118750204051658830876666571 178125306077488246314999857)
    ·
      refine ⟨133593979558116184736249893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178125306077488246314999857 133593979558116184736249893)
      ·
        refine ⟨25048871167146784638046855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133593979558116184736249893 25048871167146784638046855)
        ·
          refine ⟨37573306750720176957070283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25048871167146784638046855 37573306750720176957070283)
          ·
            refine ⟨56359960126080265435605425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37573306750720176957070283 56359960126080265435605425)
            ·
              refine ⟨42269970094560199076704069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56359960126080265435605425 42269970094560199076704069)
              ·
                refine ⟨7925619392730037326882013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42269970094560199076704069 7925619392730037326882013)
                ·
                  refine ⟨2972107272273763997580755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7925619392730037326882013 2972107272273763997580755)
                  ·
                    refine ⟨4458160908410645996371133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2972107272273763997580755 4458160908410645996371133)
                    ·
                      refine ⟨1671810340653992248639175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4458160908410645996371133 1671810340653992248639175)
                      ·
                        rfl

theorem cell23_3255839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_3255839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255839 prefixEnd_3255839 := by exact prefixLift 3255839
  have htrace : WordTrace (prefixWord ++ tailWord_3255839) baseStart_3255839 baseEnd_3255839 := by
    simpa [prefixWord, tailWord_3255839, baseEnd_3255839] using wordTrace_append hprefix tailTrace_3255839
  have hstable : (prefixWord ++ tailWord_3255839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255839).length < 2 ^ (prefixWord ++ tailWord_3255839).sum := by decide
  have hdescent : baseEnd_3255839 < baseStart_3255839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255856 : List Nat := [2, 1, 1, 1, 2, 3, 1, 7, 1, 1, 3]
def baseStart_3255856 : Nat := 118140960795 + 3255856 * 2 ^ 59
def prefixEnd_3255856 : Nat := 4983230072969 + 3 ^ 40 * 3255856 * 2
def baseEnd_3255856 : Nat := 1671819069825118682126597

theorem tailTrace_3255856 : CollatzResearch.WordTrace tailWord_3255856 prefixEnd_3255856 1671819069825118682126597 := by
  unfold tailWord_3255856
  simp only [CollatzResearch.WordTrace]
  refine ⟨59375412046298621390017711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79167216061731495186690281 59375412046298621390017711)
  ·
    refine ⟨89063118069447932085026567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59375412046298621390017711 89063118069447932085026567)
    ·
      refine ⟨133594677104171898127539851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89063118069447932085026567 133594677104171898127539851)
      ·
        refine ⟨200392015656257847191309777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133594677104171898127539851 200392015656257847191309777)
        ·
          refine ⟨150294011742193385393482333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200392015656257847191309777 150294011742193385393482333)
          ·
            refine ⟨56360254403322519522555875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150294011742193385393482333 56360254403322519522555875)
            ·
              refine ⟨84540381604983779283833813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56360254403322519522555875 84540381604983779283833813)
              ·
                refine ⟨1981415193866807326964855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 84540381604983779283833813 1981415193866807326964855)
                ·
                  refine ⟨2972122790800210990447283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1981415193866807326964855 2972122790800210990447283)
                  ·
                    refine ⟨4458184186200316485670925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2972122790800210990447283 4458184186200316485670925)
                    ·
                      refine ⟨1671819069825118682126597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4458184186200316485670925 1671819069825118682126597)
                      ·
                        rfl

theorem cell23_3255856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 1, 1, 3].length) (baseStart_3255856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255856 prefixEnd_3255856 := by exact prefixLift 3255856
  have htrace : WordTrace (prefixWord ++ tailWord_3255856) baseStart_3255856 baseEnd_3255856 := by
    simpa [prefixWord, tailWord_3255856, baseEnd_3255856] using wordTrace_append hprefix tailTrace_3255856
  have hstable : (prefixWord ++ tailWord_3255856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255856).length < 2 ^ (prefixWord ++ tailWord_3255856).sum := by decide
  have hdescent : baseEnd_3255856 < baseStart_3255856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255873 : List Nat := [1, 2, 5, 1, 1, 1, 3, 4, 1, 1, 3]
def baseStart_3255873 : Nat := 118140960795 + 3255873 * 2 ^ 59
def prefixEnd_3255873 : Nat := 4983230072969 + 3 ^ 40 * 3255873 * 2
def baseEnd_3255873 : Nat := 1671827798996245115614019

theorem tailTrace_3255873 : CollatzResearch.WordTrace tailWord_3255873 prefixEnd_3255873 1671827798996245115614019 := by
  unfold tailWord_3255873
  simp only [CollatzResearch.WordTrace]
  refine ⟨118751444133535654683404273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79167629422357103122269515 118751444133535654683404273)
  ·
    refine ⟨89063583100151741012553205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118751444133535654683404273 89063583100151741012553205)
    ·
      refine ⟨8349710915639225719926863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89063583100151741012553205 8349710915639225719926863)
      ·
        refine ⟨12524566373458838579890295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8349710915639225719926863 12524566373458838579890295)
        ·
          refine ⟨18786849560188257869835443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12524566373458838579890295 18786849560188257869835443)
          ·
            refine ⟨28180274340282386804753165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18786849560188257869835443 28180274340282386804753165)
            ·
              refine ⟨10567602877605895051782437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28180274340282386804753165 10567602877605895051782437)
              ·
                refine ⟨1981425539551105322209207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10567602877605895051782437 1981425539551105322209207)
                ·
                  refine ⟨2972138309326657983313811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1981425539551105322209207 2972138309326657983313811)
                  ·
                    refine ⟨4458207463989986974970717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2972138309326657983313811 4458207463989986974970717)
                    ·
                      refine ⟨1671827798996245115614019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4458207463989986974970717 1671827798996245115614019)
                      ·
                        rfl

theorem cell23_3255873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_3255873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255873 prefixEnd_3255873 := by exact prefixLift 3255873
  have htrace : WordTrace (prefixWord ++ tailWord_3255873) baseStart_3255873 baseEnd_3255873 := by
    simpa [prefixWord, tailWord_3255873, baseEnd_3255873] using wordTrace_append hprefix tailTrace_3255873
  have hstable : (prefixWord ++ tailWord_3255873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255873).length < 2 ^ (prefixWord ++ tailWord_3255873).sum := by decide
  have hdescent : baseEnd_3255873 < baseStart_3255873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255882 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 3, 1, 5]
def baseStart_3255882 : Nat := 118140960795 + 3255882 * 2 ^ 59
def prefixEnd_3255882 : Nat := 4983230072969 + 3 ^ 40 * 3255882 * 2
def baseEnd_3255882 : Nat := 1671832420322135580401477

theorem tailTrace_3255882 : CollatzResearch.WordTrace tailWord_3255882 prefixEnd_3255882 1671832420322135580401477 := by
  unfold tailWord_3255882
  simp only [CollatzResearch.WordTrace]
  refine ⟨29687943097625762305120475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79167848260335366146987933 29687943097625762305120475)
  ·
    refine ⟨44531914646438643457680713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29687943097625762305120475 44531914646438643457680713)
    ·
      refine ⟨33398935984828982593260535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44531914646438643457680713 33398935984828982593260535)
      ·
        refine ⟨50098403977243473889890803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33398935984828982593260535 50098403977243473889890803)
        ·
          refine ⟨75147605965865210834836205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50098403977243473889890803 75147605965865210834836205)
          ·
            refine ⟨28180352237199454063063577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75147605965865210834836205 28180352237199454063063577)
            ·
              refine ⟨21135264177899590547297683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28180352237199454063063577 21135264177899590547297683)
              ·
                refine ⟨31702896266849385820946525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21135264177899590547297683 31702896266849385820946525)
                ·
                  refine ⟨11888586100068519682854947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31702896266849385820946525 11888586100068519682854947)
                  ·
                    refine ⟨17832879150102779524282421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11888586100068519682854947 17832879150102779524282421)
                    ·
                      refine ⟨1671832420322135580401477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17832879150102779524282421 1671832420322135580401477)
                      ·
                        rfl

theorem cell23_3255882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_3255882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255882 prefixEnd_3255882 := by exact prefixLift 3255882
  have htrace : WordTrace (prefixWord ++ tailWord_3255882) baseStart_3255882 baseEnd_3255882 := by
    simpa [prefixWord, tailWord_3255882, baseEnd_3255882] using wordTrace_append hprefix tailTrace_3255882
  have hstable : (prefixWord ++ tailWord_3255882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255882).length < 2 ^ (prefixWord ++ tailWord_3255882).sum := by decide
  have hdescent : baseEnd_3255882 < baseStart_3255882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255889 : List Nat := [1, 2, 2, 1, 3, 2, 1, 5, 2, 4]
def baseStart_3255889 : Nat := 118140960795 + 3255889 * 2 ^ 59
def prefixEnd_3255889 : Nat := 4983230072969 + 3 ^ 40 * 3255889 * 2
def baseEnd_3255889 : Nat := 557278671562239017671315

theorem tailTrace_3255889 : CollatzResearch.WordTrace tailWord_3255889 prefixEnd_3255889 557278671562239017671315 := by
  unfold tailWord_3255889
  simp only [CollatzResearch.WordTrace]
  refine ⟨118752027701477689415986721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79168018467651792943991147 118752027701477689415986721)
  ·
    refine ⟨89064020776108267061990041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118752027701477689415986721 89064020776108267061990041)
    ·
      refine ⟨66798015582081200296492531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89064020776108267061990041 66798015582081200296492531)
      ·
        refine ⟨100197023373121800444738797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66798015582081200296492531 100197023373121800444738797)
        ·
          refine ⟨37573883764920675166777049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100197023373121800444738797 37573883764920675166777049)
          ·
            refine ⟨28180412823690506375082787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37573883764920675166777049 28180412823690506375082787)
            ·
              refine ⟨42270619235535759562624181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28180412823690506375082787 42270619235535759562624181)
              ·
                refine ⟨3962870553331477458996017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42270619235535759562624181 3962870553331477458996017)
                ·
                  refine ⟨2972152914998608094247013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3962870553331477458996017 2972152914998608094247013)
                  ·
                    refine ⟨557278671562239017671315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2972152914998608094247013 557278671562239017671315)
                    ·
                      rfl

theorem cell23_3255889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 4].length) (baseStart_3255889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255889 prefixEnd_3255889 := by exact prefixLift 3255889
  have htrace : WordTrace (prefixWord ++ tailWord_3255889) baseStart_3255889 baseEnd_3255889 := by
    simpa [prefixWord, tailWord_3255889, baseEnd_3255889] using wordTrace_append hprefix tailTrace_3255889
  have hstable : (prefixWord ++ tailWord_3255889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255889).length < 2 ^ (prefixWord ++ tailWord_3255889).sum := by decide
  have hdescent : baseEnd_3255889 < baseStart_3255889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255909 : List Nat := [1, 3, 1, 3, 3, 1, 2, 2, 1, 2, 4]
def baseStart_3255909 : Nat := 118140960795 + 3255909 * 2 ^ 59
def prefixEnd_3255909 : Nat := 4983230072969 + 3 ^ 40 * 3255909 * 2
def baseEnd_3255909 : Nat := 1671846284299806974763853

theorem tailTrace_3255909 : CollatzResearch.WordTrace tailWord_3255909 prefixEnd_3255909 1671846284299806974763853 := by
  unfold tailWord_3255909
  simp only [CollatzResearch.WordTrace]
  refine ⟨118752757161405232831714781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79168504774270155221143187 118752757161405232831714781)
  ·
    refine ⟨44532283935526962311893043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118752757161405232831714781 44532283935526962311893043)
    ·
      refine ⟨66798425903290443467839565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44532283935526962311893043 66798425903290443467839565)
      ·
        refine ⟨25049409713733916300439837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66798425903290443467839565 25049409713733916300439837)
        ·
          refine ⟨9393528642650218612664939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25049409713733916300439837 9393528642650218612664939)
          ·
            refine ⟨14090292963975327918997409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9393528642650218612664939 14090292963975327918997409)
            ·
              refine ⟨10567719722981495939248057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14090292963975327918997409 10567719722981495939248057)
              ·
                refine ⟨7925789792236121954436043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10567719722981495939248057 7925789792236121954436043)
                ·
                  refine ⟨11888684688354182931654065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7925789792236121954436043 11888684688354182931654065)
                  ·
                    refine ⟨8916513516265637198740549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11888684688354182931654065 8916513516265637198740549)
                    ·
                      refine ⟨1671846284299806974763853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8916513516265637198740549 1671846284299806974763853)
                      ·
                        rfl

theorem cell23_3255909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_3255909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255909 prefixEnd_3255909 := by exact prefixLift 3255909
  have htrace : WordTrace (prefixWord ++ tailWord_3255909) baseStart_3255909 baseEnd_3255909 := by
    simpa [prefixWord, tailWord_3255909, baseEnd_3255909] using wordTrace_append hprefix tailTrace_3255909
  have hstable : (prefixWord ++ tailWord_3255909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255909).length < 2 ^ (prefixWord ++ tailWord_3255909).sum := by decide
  have hdescent : baseEnd_3255909 < baseStart_3255909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255913 : List Nat := [1, 2, 1, 1, 1, 4, 3, 5, 1, 2, 2]
def baseStart_3255913 : Nat := 118140960795 + 3255913 * 2 ^ 59
def prefixEnd_3255913 : Nat := 4983230072969 + 3 ^ 40 * 3255913 * 2
def baseEnd_3255913 : Nat := 1671848338222424959113835

theorem tailTrace_3255913 : CollatzResearch.WordTrace tailWord_3255913 prefixEnd_3255913 1671848338222424959113835 := by
  unfold tailWord_3255913
  simp only [CollatzResearch.WordTrace]
  refine ⟨118752903053390741514860393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79168602035593827676573595 118752903053390741514860393)
  ·
    refine ⟨89064677290043056136145295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118752903053390741514860393 89064677290043056136145295)
    ·
      refine ⟨133597015935064584204217943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89064677290043056136145295 133597015935064584204217943)
      ·
        refine ⟨200395523902596876306326915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133597015935064584204217943 200395523902596876306326915)
        ·
          refine ⟨300593285853895314459490373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200395523902596876306326915 300593285853895314459490373)
          ·
            refine ⟨56361241097605371461154445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 300593285853895314459490373 56361241097605371461154445)
            ·
              refine ⟨21135465411602014297932917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56361241097605371461154445 21135465411602014297932917)
              ·
                refine ⟨1981449882337688840431211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21135465411602014297932917 1981449882337688840431211)
                ·
                  refine ⟨2972174823506533260646817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1981449882337688840431211 2972174823506533260646817)
                  ·
                    refine ⟨2229131117629899945485113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2972174823506533260646817 2229131117629899945485113)
                    ·
                      refine ⟨1671848338222424959113835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2229131117629899945485113 1671848338222424959113835)
                      ·
                        rfl

theorem cell23_3255913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 1, 2, 2].length) (baseStart_3255913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255913 prefixEnd_3255913 := by exact prefixLift 3255913
  have htrace : WordTrace (prefixWord ++ tailWord_3255913) baseStart_3255913 baseEnd_3255913 := by
    simpa [prefixWord, tailWord_3255913, baseEnd_3255913] using wordTrace_append hprefix tailTrace_3255913
  have hstable : (prefixWord ++ tailWord_3255913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255913).length < 2 ^ (prefixWord ++ tailWord_3255913).sum := by decide
  have hdescent : baseEnd_3255913 < baseStart_3255913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255946 : List Nat := [3, 1, 2, 3, 2, 1, 3, 1, 1, 3, 3]
def baseStart_3255946 : Nat := 118140960795 + 3255946 * 2 ^ 59
def prefixEnd_3255946 : Nat := 4983230072969 + 3 ^ 40 * 3255946 * 2
def baseEnd_3255946 : Nat := 1671865283084023330001183

theorem tailTrace_3255946 : CollatzResearch.WordTrace tailWord_3255946 prefixEnd_3255946 1671865283084023330001183 := by
  unfold tailWord_3255946
  simp only [CollatzResearch.WordTrace]
  refine ⟨29688526665567797037702923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79169404441514125433874461 29688526665567797037702923)
  ·
    refine ⟨44532789998351695556554385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29688526665567797037702923 44532789998351695556554385)
    ·
      refine ⟨33399592498763771667415789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44532789998351695556554385 33399592498763771667415789)
      ·
        refine ⟨12524847187036414375280921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33399592498763771667415789 12524847187036414375280921)
        ·
          refine ⟨9393635390277310781460691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12524847187036414375280921 9393635390277310781460691)
          ·
            refine ⟨14090453085415966172191037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9393635390277310781460691 14090453085415966172191037)
            ·
              refine ⟨5283919907030987314571639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14090453085415966172191037 5283919907030987314571639)
              ·
                refine ⟨7925879860546480971857459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5283919907030987314571639 7925879860546480971857459)
                ·
                  refine ⟨11888819790819721457786189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7925879860546480971857459 11888819790819721457786189)
                  ·
                    refine ⟨4458307421557395546669821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11888819790819721457786189 4458307421557395546669821)
                    ·
                      refine ⟨1671865283084023330001183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4458307421557395546669821 1671865283084023330001183)
                      ·
                        rfl

theorem cell23_3255946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_3255946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255946 prefixEnd_3255946 := by exact prefixLift 3255946
  have htrace : WordTrace (prefixWord ++ tailWord_3255946) baseStart_3255946 baseEnd_3255946 := by
    simpa [prefixWord, tailWord_3255946, baseEnd_3255946] using wordTrace_append hprefix tailTrace_3255946
  have hstable : (prefixWord ++ tailWord_3255946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255946).length < 2 ^ (prefixWord ++ tailWord_3255946).sum := by decide
  have hdescent : baseEnd_3255946 < baseStart_3255946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255952 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 4]
def baseStart_3255952 : Nat := 118140960795 + 3255952 * 2 ^ 59
def prefixEnd_3255952 : Nat := 4983230072969 + 3 ^ 40 * 3255952 * 2
def baseEnd_3255952 : Nat := 1671868363967950306526155

theorem tailTrace_3255952 : CollatzResearch.WordTrace tailWord_3255952 prefixEnd_3255952 1671868363967950306526155 := by
  unfold tailWord_3255952
  simp only [CollatzResearch.WordTrace]
  refine ⟨59377162750124725587765055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79169550333499634117020073 59377162750124725587765055)
  ·
    refine ⟨89065744125187088381647583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59377162750124725587765055 89065744125187088381647583)
    ·
      refine ⟨133598616187780632572471375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89065744125187088381647583 133598616187780632572471375)
      ·
        refine ⟨200397924281670948858707063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133598616187780632572471375 200397924281670948858707063)
        ·
          refine ⟨300596886422506423288060595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200397924281670948858707063 300596886422506423288060595)
          ·
            refine ⟨450895329633759634932090893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300596886422506423288060595 450895329633759634932090893)
            ·
              refine ⟨169085748612659863099534085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 450895329633759634932090893 169085748612659863099534085)
              ·
                refine ⟨31703577864873724331162641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169085748612659863099534085 31703577864873724331162641)
                ·
                  refine ⟨23777683398655293248371981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31703577864873724331162641 23777683398655293248371981)
                  ·
                    refine ⟨8916631274495734968139493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23777683398655293248371981 8916631274495734968139493)
                    ·
                      refine ⟨1671868363967950306526155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8916631274495734968139493 1671868363967950306526155)
                      ·
                        rfl

theorem cell23_3255952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 4].length) (baseStart_3255952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255952 prefixEnd_3255952 := by exact prefixLift 3255952
  have htrace : WordTrace (prefixWord ++ tailWord_3255952) baseStart_3255952 baseEnd_3255952 := by
    simpa [prefixWord, tailWord_3255952, baseEnd_3255952] using wordTrace_append hprefix tailTrace_3255952
  have hstable : (prefixWord ++ tailWord_3255952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255952).length < 2 ^ (prefixWord ++ tailWord_3255952).sum := by decide
  have hdescent : baseEnd_3255952 < baseStart_3255952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3255964 : List Nat := [2, 2, 3, 2, 4, 1, 1, 3, 1, 2, 2]
def baseStart_3255964 : Nat := 118140960795 + 3255964 * 2 ^ 59
def prefixEnd_3255964 : Nat := 4983230072969 + 3 ^ 40 * 3255964 * 2
def baseEnd_3255964 : Nat := 1671874525735804259576101

theorem tailTrace_3255964 : CollatzResearch.WordTrace tailWord_3255964 prefixEnd_3255964 1671874525735804259576101 := by
  unfold tailWord_3255964
  simp only [CollatzResearch.WordTrace]
  refine ⟨59377381588102988612483473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79169842117470651483311297 59377381588102988612483473)
  ·
    refine ⟨44533036191077241459362605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59377381588102988612483473 44533036191077241459362605)
    ·
      refine ⟨16699888571653965547260977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44533036191077241459362605 16699888571653965547260977)
      ·
        refine ⟨12524916428740474160445733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16699888571653965547260977 12524916428740474160445733)
        ·
          refine ⟨2348421830388838905083575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12524916428740474160445733 2348421830388838905083575)
          ·
            refine ⟨3522632745583258357625363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2348421830388838905083575 3522632745583258357625363)
            ·
              refine ⟨5283949118374887536438045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3522632745583258357625363 5283949118374887536438045)
              ·
                refine ⟨1981480919390582826164267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5283949118374887536438045 1981480919390582826164267)
                ·
                  refine ⟨2972221379085874239246401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1981480919390582826164267 2972221379085874239246401)
                  ·
                    refine ⟨2229166034314405679434801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2972221379085874239246401 2229166034314405679434801)
                    ·
                      refine ⟨1671874525735804259576101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2229166034314405679434801 1671874525735804259576101)
                      ·
                        rfl

theorem cell23_3255964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_3255964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3255964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3255964 prefixEnd_3255964 := by exact prefixLift 3255964
  have htrace : WordTrace (prefixWord ++ tailWord_3255964) baseStart_3255964 baseEnd_3255964 := by
    simpa [prefixWord, tailWord_3255964, baseEnd_3255964] using wordTrace_append hprefix tailTrace_3255964
  have hstable : (prefixWord ++ tailWord_3255964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3255964).length < 2 ^ (prefixWord ++ tailWord_3255964).sum := by decide
  have hdescent : baseEnd_3255964 < baseStart_3255964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3255964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256046 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 1, 7, 2]
def baseStart_3256046 : Nat := 118140960795 + 3256046 * 2 ^ 59
def prefixEnd_3256046 : Nat := 4983230072969 + 3 ^ 40 * 3256046 * 2
def baseEnd_3256046 : Nat := 1671916631149472938750723

theorem tailTrace_3256046 : CollatzResearch.WordTrace tailWord_3256046 prefixEnd_3256046 1671916631149472938750723 := by
  unfold tailWord_3256046
  simp only [CollatzResearch.WordTrace]
  refine ⟨14844719245238613153681499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79171835974605936819634661 14844719245238613153681499)
  ·
    refine ⟨22267078867857919730522249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14844719245238613153681499 22267078867857919730522249)
    ·
      refine ⟨16700309150893439797891687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22267078867857919730522249 16700309150893439797891687)
      ·
        refine ⟨25050463726340159696837531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16700309150893439797891687 25050463726340159696837531)
        ·
          refine ⟨37575695589510239545256297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25050463726340159696837531 37575695589510239545256297)
          ·
            refine ⟨28181771692132679658942223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37575695589510239545256297 28181771692132679658942223)
            ·
              refine ⟨42272657538199019488413335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28181771692132679658942223 42272657538199019488413335)
              ·
                refine ⟨63408986307298529232620003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42272657538199019488413335 63408986307298529232620003)
                ·
                  refine ⟨95113479460947793848930005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63408986307298529232620003 95113479460947793848930005)
                  ·
                    refine ⟨2229222174865963918334297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 95113479460947793848930005 2229222174865963918334297)
                    ·
                      refine ⟨1671916631149472938750723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2229222174865963918334297 1671916631149472938750723)
                      ·
                        rfl

theorem cell23_3256046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_3256046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256046 prefixEnd_3256046 := by exact prefixLift 3256046
  have htrace : WordTrace (prefixWord ++ tailWord_3256046) baseStart_3256046 baseEnd_3256046 := by
    simpa [prefixWord, tailWord_3256046, baseEnd_3256046] using wordTrace_append hprefix tailTrace_3256046
  have hstable : (prefixWord ++ tailWord_3256046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256046).length < 2 ^ (prefixWord ++ tailWord_3256046).sum := by decide
  have hdescent : baseEnd_3256046 < baseStart_3256046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256049 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 1, 2, 5]
def baseStart_3256049 : Nat := 118140960795 + 3256049 * 2 ^ 59
def prefixEnd_3256049 : Nat := 4983230072969 + 3 ^ 40 * 3256049 * 2
def baseEnd_3256049 : Nat := 1671918171591436427013209

theorem tailTrace_3256049 : CollatzResearch.WordTrace tailWord_3256049 prefixEnd_3256049 1671918171591436427013209 := by
  unfold tailWord_3256049
  simp only [CollatzResearch.WordTrace]
  refine ⟨118757863380898036741811201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79171908920598691161207467 118757863380898036741811201)
  ·
    refine ⟨89068397535673527556358401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118757863380898036741811201 89068397535673527556358401)
    ·
      refine ⟨66801298151755145667268801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89068397535673527556358401 66801298151755145667268801)
      ·
        refine ⟨50100973613816359250451601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66801298151755145667268801 50100973613816359250451601)
        ·
          refine ⟨37575730210362269437838701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50100973613816359250451601 37575730210362269437838701)
          ·
            refine ⟨14090898828885851039189513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37575730210362269437838701 14090898828885851039189513)
            ·
              refine ⟨10568174121664388279392135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14090898828885851039189513 10568174121664388279392135)
              ·
                refine ⟨15852261182496582419088203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10568174121664388279392135 15852261182496582419088203)
                ·
                  refine ⟨23778391773744873628632305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15852261182496582419088203 23778391773744873628632305)
                  ·
                    refine ⟨17833793830308655221474229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23778391773744873628632305 17833793830308655221474229)
                    ·
                      refine ⟨1671918171591436427013209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17833793830308655221474229 1671918171591436427013209)
                      ·
                        rfl

theorem cell23_3256049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_3256049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256049 prefixEnd_3256049 := by exact prefixLift 3256049
  have htrace : WordTrace (prefixWord ++ tailWord_3256049) baseStart_3256049 baseEnd_3256049 := by
    simpa [prefixWord, tailWord_3256049, baseEnd_3256049] using wordTrace_append hprefix tailTrace_3256049
  have hstable : (prefixWord ++ tailWord_3256049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256049).length < 2 ^ (prefixWord ++ tailWord_3256049).sum := by decide
  have hdescent : baseEnd_3256049 < baseStart_3256049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256076 : List Nat := [2, 2, 1, 2, 2, 1, 5, 1, 2, 1, 4]
def baseStart_3256076 : Nat := 118140960795 + 3256076 * 2 ^ 59
def prefixEnd_3256076 : Nat := 4983230072969 + 3 ^ 40 * 3256076 * 2
def baseEnd_3256076 : Nat := 1671932035569107821375585

theorem tailTrace_3256076 : CollatzResearch.WordTrace tailWord_3256076 prefixEnd_3256076 1671932035569107821375585 := by
  unfold tailWord_3256076
  simp only [CollatzResearch.WordTrace]
  refine ⟨59379424075900110176522041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79172565434533480235362721 59379424075900110176522041)
  ·
    refine ⟨44534568056925082632391531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59379424075900110176522041 44534568056925082632391531)
    ·
      refine ⟨66801852085387623948587297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44534568056925082632391531 66801852085387623948587297)
      ·
        refine ⟨50101389064040717961440473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66801852085387623948587297 50101389064040717961440473)
        ·
          refine ⟨37576041798030538471080355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50101389064040717961440473 37576041798030538471080355)
          ·
            refine ⟨56364062697045807706620533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37576041798030538471080355 56364062697045807706620533)
            ·
              refine ⟨5284130877848044472495675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56364062697045807706620533 5284130877848044472495675)
              ·
                refine ⟨7926196316772066708743513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5284130877848044472495675 7926196316772066708743513)
                ·
                  refine ⟨5944647237579050031557635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7926196316772066708743513 5944647237579050031557635)
                  ·
                    refine ⟨8916970856368575047336453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5944647237579050031557635 8916970856368575047336453)
                    ·
                      refine ⟨1671932035569107821375585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8916970856368575047336453 1671932035569107821375585)
                      ·
                        rfl

theorem cell23_3256076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_3256076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256076 prefixEnd_3256076 := by exact prefixLift 3256076
  have htrace : WordTrace (prefixWord ++ tailWord_3256076) baseStart_3256076 baseEnd_3256076 := by
    simpa [prefixWord, tailWord_3256076, baseEnd_3256076] using wordTrace_append hprefix tailTrace_3256076
  have hstable : (prefixWord ++ tailWord_3256076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256076).length < 2 ^ (prefixWord ++ tailWord_3256076).sum := by decide
  have hdescent : baseEnd_3256076 < baseStart_3256076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256096 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 3]
def baseStart_3256096 : Nat := 118140960795 + 3256096 * 2 ^ 59
def prefixEnd_3256096 : Nat := 4983230072969 + 3 ^ 40 * 3256096 * 2
def baseEnd_3256096 : Nat := 1671942305182197743125493

theorem tailTrace_3256096 : CollatzResearch.WordTrace tailWord_3256096 prefixEnd_3256096 1671942305182197743125493 := by
  unfold tailWord_3256096
  simp only [CollatzResearch.WordTrace]
  refine ⟨59379788805863881884386071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79173051741151842512514761 59379788805863881884386071)
  ·
    refine ⟨89069683208795822826579107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59379788805863881884386071 89069683208795822826579107)
    ·
      refine ⟨133604524813193734239868661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89069683208795822826579107 133604524813193734239868661)
      ·
        refine ⟨12525424201236912584987687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133604524813193734239868661 12525424201236912584987687)
        ·
          refine ⟨18788136301855368877481531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12525424201236912584987687 18788136301855368877481531)
          ·
            refine ⟨28182204452783053316222297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18788136301855368877481531 28182204452783053316222297)
            ·
              refine ⟨21136653339587289987166723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28182204452783053316222297 21136653339587289987166723)
              ·
                refine ⟨31704980009380934980750085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21136653339587289987166723 31704980009380934980750085)
                ·
                  refine ⟨5944683751758925308890641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31704980009380934980750085 5944683751758925308890641)
                  ·
                    refine ⟨4458512813819193981667981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5944683751758925308890641 4458512813819193981667981)
                    ·
                      refine ⟨1671942305182197743125493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4458512813819193981667981 1671942305182197743125493)
                      ·
                        rfl

theorem cell23_3256096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_3256096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256096 prefixEnd_3256096 := by exact prefixLift 3256096
  have htrace : WordTrace (prefixWord ++ tailWord_3256096) baseStart_3256096 baseEnd_3256096 := by
    simpa [prefixWord, tailWord_3256096, baseEnd_3256096] using wordTrace_append hprefix tailTrace_3256096
  have hstable : (prefixWord ++ tailWord_3256096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256096).length < 2 ^ (prefixWord ++ tailWord_3256096).sum := by decide
  have hdescent : baseEnd_3256096 < baseStart_3256096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256153 : List Nat := [1, 2, 1, 2, 2, 3, 3, 2, 2, 3, 2]
def baseStart_3256153 : Nat := 118140960795 + 3256153 * 2 ^ 59
def prefixEnd_3256153 : Nat := 4983230072969 + 3 ^ 40 * 3256153 * 2
def baseEnd_3256153 : Nat := 1671971573579504020112731

theorem tailTrace_3256153 : CollatzResearch.WordTrace tailWord_3256153 prefixEnd_3256153 1671971573579504020112731 := by
  unfold tailWord_3256153
  simp only [CollatzResearch.WordTrace]
  refine ⟨118761656572521262503597113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79174437715014175002398075 118761656572521262503597113)
  ·
    refine ⟨89071242429390946877697835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118761656572521262503597113 89071242429390946877697835)
    ·
      refine ⟨133606863644086420316546753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89071242429390946877697835 133606863644086420316546753)
      ·
        refine ⟨100205147733064815237410065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133606863644086420316546753 100205147733064815237410065)
        ·
          refine ⟨75153860799798611428057549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100205147733064815237410065 75153860799798611428057549)
          ·
            refine ⟨28182697799924479285521581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75153860799798611428057549 28182697799924479285521581)
            ·
              refine ⟨10568511674971679732070593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28182697799924479285521581 10568511674971679732070593)
              ·
                refine ⟨7926383756228759799052945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10568511674971679732070593 7926383756228759799052945)
                ·
                  refine ⟨5944787817171569849289709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7926383756228759799052945 5944787817171569849289709)
                  ·
                    refine ⟨2229295431439338693483641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5944787817171569849289709 2229295431439338693483641)
                    ·
                      refine ⟨1671971573579504020112731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2229295431439338693483641 1671971573579504020112731)
                      ·
                        rfl

theorem cell23_3256153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 3, 2].length) (baseStart_3256153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256153 prefixEnd_3256153 := by exact prefixLift 3256153
  have htrace : WordTrace (prefixWord ++ tailWord_3256153) baseStart_3256153 baseEnd_3256153 := by
    simpa [prefixWord, tailWord_3256153, baseEnd_3256153] using wordTrace_append hprefix tailTrace_3256153
  have hstable : (prefixWord ++ tailWord_3256153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256153).length < 2 ^ (prefixWord ++ tailWord_3256153).sum := by decide
  have hdescent : baseEnd_3256153 < baseStart_3256153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256160 : List Nat := [2, 1, 1, 3, 3, 4, 1, 1, 3, 1, 3]
def baseStart_3256160 : Nat := 118140960795 + 3256160 * 2 ^ 59
def prefixEnd_3256160 : Nat := 4983230072969 + 3 ^ 40 * 3256160 * 2
def baseEnd_3256160 : Nat := 1671975167944085492725199

theorem tailTrace_3256160 : CollatzResearch.WordTrace tailWord_3256160 prefixEnd_3256160 1671975167944085492725199 := by
  unfold tailWord_3256160
  simp only [CollatzResearch.WordTrace]
  refine ⟨59380955941747951349550967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79174607922330601799401289 59380955941747951349550967)
  ·
    refine ⟨89071433912621927024326451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59380955941747951349550967 89071433912621927024326451)
    ·
      refine ⟨133607150868932890536489677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89071433912621927024326451 133607150868932890536489677)
      ·
        refine ⟨50102681575849833951183629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133607150868932890536489677 50102681575849833951183629)
        ·
          refine ⟨18788505590943687731693861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50102681575849833951183629 18788505590943687731693861)
          ·
            refine ⟨3522844798301941449692599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18788505590943687731693861 3522844798301941449692599)
            ·
              refine ⟨5284267197452912174538899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3522844798301941449692599 5284267197452912174538899)
              ·
                refine ⟨7926400796179368261808349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5284267197452912174538899 7926400796179368261808349)
                ·
                  refine ⟨2972400298567263098178131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7926400796179368261808349 2972400298567263098178131)
                  ·
                    refine ⟨4458600447850894647267197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2972400298567263098178131 4458600447850894647267197)
                    ·
                      refine ⟨1671975167944085492725199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4458600447850894647267197 1671975167944085492725199)
                      ·
                        rfl

theorem cell23_3256160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_3256160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256160 prefixEnd_3256160 := by exact prefixLift 3256160
  have htrace : WordTrace (prefixWord ++ tailWord_3256160) baseStart_3256160 baseEnd_3256160 := by
    simpa [prefixWord, tailWord_3256160, baseEnd_3256160] using wordTrace_append hprefix tailTrace_3256160
  have hstable : (prefixWord ++ tailWord_3256160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256160).length < 2 ^ (prefixWord ++ tailWord_3256160).sum := by decide
  have hdescent : baseEnd_3256160 < baseStart_3256160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256196 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_3256196 : Nat := 118140960795 + 3256196 * 2 ^ 59
def prefixEnd_3256196 : Nat := 4983230072969 + 3 ^ 40 * 3256196 * 2
def baseEnd_3256196 : Nat := 1671993653247647351875033

theorem tailTrace_3256196 : CollatzResearch.WordTrace tailWord_3256196 prefixEnd_3256196 1671993653247647351875033 := by
  unfold tailWord_3256196
  simp only [CollatzResearch.WordTrace]
  refine ⟨59381612455682740423706221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79175483274243653898274961 59381612455682740423706221)
  ·
    refine ⟨22268104670881027658889833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59381612455682740423706221 22268104670881027658889833)
    ·
      refine ⟨16701078503160770744167375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22268104670881027658889833 16701078503160770744167375)
      ·
        refine ⟨25051617754741156116251063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16701078503160770744167375 25051617754741156116251063)
        ·
          refine ⟨37577426632111734174376595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25051617754741156116251063 37577426632111734174376595)
          ·
            refine ⟨56366139948167601261564893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37577426632111734174376595 56366139948167601261564893)
            ·
              refine ⟨21137302480562850473086835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56366139948167601261564893 21137302480562850473086835)
              ·
                refine ⟨31705953720844275709630253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21137302480562850473086835 31705953720844275709630253)
                ·
                  refine ⟨11889732645316603391111345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31705953720844275709630253 11889732645316603391111345)
                  ·
                    refine ⟨8917299483987452543333509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11889732645316603391111345 8917299483987452543333509)
                    ·
                      refine ⟨1671993653247647351875033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8917299483987452543333509 1671993653247647351875033)
                      ·
                        rfl

theorem cell23_3256196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_3256196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256196 prefixEnd_3256196 := by exact prefixLift 3256196
  have htrace : WordTrace (prefixWord ++ tailWord_3256196) baseStart_3256196 baseEnd_3256196 := by
    simpa [prefixWord, tailWord_3256196, baseEnd_3256196] using wordTrace_append hprefix tailTrace_3256196
  have hstable : (prefixWord ++ tailWord_3256196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256196).length < 2 ^ (prefixWord ++ tailWord_3256196).sum := by decide
  have hdescent : baseEnd_3256196 < baseStart_3256196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256206 : List Nat := [4, 1, 1, 5, 12]
def baseStart_3256206 : Nat := 118140960795 + 3256206 * 2 ^ 59
def prefixEnd_3256206 : Nat := 4983230072969 + 3 ^ 40 * 3256206 * 2
def baseEnd_3256206 : Nat := 2293551149594228138203

theorem tailTrace_3256206 : CollatzResearch.WordTrace tailWord_3256206 prefixEnd_3256206 2293551149594228138203 := by
  unfold tailWord_3256206
  simp only [CollatzResearch.WordTrace]
  refine ⟨14845448705166156569409559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79175726427552835036850981 14845448705166156569409559)
  ·
    refine ⟨22268173057749234854114339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14845448705166156569409559 22268173057749234854114339)
    ·
      refine ⟨33402259586623852281171509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22268173057749234854114339 33402259586623852281171509)
      ·
        refine ⟨3131461836245986151359829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33402259586623852281171509 3131461836245986151359829)
        ·
          refine ⟨2293551149594228138203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3131461836245986151359829 2293551149594228138203)
          ·
            rfl

theorem cell23_3256206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 12].length) (baseStart_3256206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256206 prefixEnd_3256206 := by exact prefixLift 3256206
  have htrace : WordTrace (prefixWord ++ tailWord_3256206) baseStart_3256206 baseEnd_3256206 := by
    simpa [prefixWord, tailWord_3256206, baseEnd_3256206] using wordTrace_append hprefix tailTrace_3256206
  have hstable : (prefixWord ++ tailWord_3256206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256206).length < 2 ^ (prefixWord ++ tailWord_3256206).sum := by decide
  have hdescent : baseEnd_3256206 < baseStart_3256206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256210 : List Nat := [3, 2, 3, 2, 1, 1, 1, 4, 2, 4]
def baseStart_3256210 : Nat := 118140960795 + 3256210 * 2 ^ 59
def prefixEnd_3256210 : Nat := 4983230072969 + 3 ^ 40 * 3256210 * 2
def baseEnd_3256210 : Nat := 557333613992270099033323

theorem tailTrace_3256210 : CollatzResearch.WordTrace tailWord_3256210 prefixEnd_3256210 557333613992270099033323 := by
  unfold tailWord_3256210
  simp only [CollatzResearch.WordTrace]
  refine ⟨29690933883328690309605521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79175823688876507492281389 29690933883328690309605521)
  ·
    refine ⟨22268200412496517732204141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29690933883328690309605521 22268200412496517732204141)
    ·
      refine ⟨8350575154686194149576553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22268200412496517732204141 8350575154686194149576553)
      ·
        refine ⟨6262931366014645612182415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8350575154686194149576553 6262931366014645612182415)
        ·
          refine ⟨9394397049021968418273623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6262931366014645612182415 9394397049021968418273623)
          ·
            refine ⟨14091595573532952627410435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9394397049021968418273623 14091595573532952627410435)
            ·
              refine ⟨21137393360299428941115653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14091595573532952627410435 21137393360299428941115653)
              ·
                refine ⟨3963261255056142926459185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21137393360299428941115653 3963261255056142926459185)
                ·
                  refine ⟨2972445941292107194844389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3963261255056142926459185 2972445941292107194844389)
                  ·
                    refine ⟨557333613992270099033323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2972445941292107194844389 557333613992270099033323)
                    ·
                      rfl

theorem cell23_3256210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_3256210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256210 prefixEnd_3256210 := by exact prefixLift 3256210
  have htrace : WordTrace (prefixWord ++ tailWord_3256210) baseStart_3256210 baseEnd_3256210 := by
    simpa [prefixWord, tailWord_3256210, baseEnd_3256210] using wordTrace_append hprefix tailTrace_3256210
  have hstable : (prefixWord ++ tailWord_3256210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256210).length < 2 ^ (prefixWord ++ tailWord_3256210).sum := by decide
  have hdescent : baseEnd_3256210 < baseStart_3256210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256223 : List Nat := [1, 1, 2, 5, 3, 2, 1, 8]
def baseStart_3256223 : Nat := 118140960795 + 3256223 * 2 ^ 59
def prefixEnd_3256223 : Nat := 4983230072969 + 3 ^ 40 * 3256223 * 2
def baseEnd_3256223 : Nat := 61926204341678472082867

theorem tailTrace_3256223 : CollatzResearch.WordTrace tailWord_3256223 prefixEnd_3256223 61926204341678472082867 := by
  unfold tailWord_3256223
  simp only [CollatzResearch.WordTrace]
  refine ⟨118764209682267664458645323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79176139788178442972430215 118764209682267664458645323)
  ·
    refine ⟨178146314523401496687967985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118764209682267664458645323 178146314523401496687967985)
    ·
      refine ⟨133609735892551122515975989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178146314523401496687967985 133609735892551122515975989)
      ·
        refine ⟨12525912739926667735872749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133609735892551122515975989 12525912739926667735872749)
        ·
          refine ⟨4697217277472500400952281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12525912739926667735872749 4697217277472500400952281)
          ·
            refine ⟨3522912958104375300714211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4697217277472500400952281 3522912958104375300714211)
            ·
              refine ⟨5284369437156562951071317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3522912958104375300714211 5284369437156562951071317)
              ·
                refine ⟨61926204341678472082867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5284369437156562951071317 61926204341678472082867)
                ·
                  rfl

theorem cell23_3256223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 8].length) (baseStart_3256223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256223 prefixEnd_3256223 := by exact prefixLift 3256223
  have htrace : WordTrace (prefixWord ++ tailWord_3256223) baseStart_3256223 baseEnd_3256223 := by
    simpa [prefixWord, tailWord_3256223, baseEnd_3256223] using wordTrace_append hprefix tailTrace_3256223
  have hstable : (prefixWord ++ tailWord_3256223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256223).length < 2 ^ (prefixWord ++ tailWord_3256223).sum := by decide
  have hdescent : baseEnd_3256223 < baseStart_3256223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256238 : List Nat := [4, 1, 5, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_3256238 : Nat := 118140960795 + 3256238 * 2 ^ 59
def prefixEnd_3256238 : Nat := 4983230072969 + 3 ^ 40 * 3256238 * 2
def baseEnd_3256238 : Nat := 1672015219435136187549841

theorem tailTrace_3256238 : CollatzResearch.WordTrace tailWord_3256238 prefixEnd_3256238 1672015219435136187549841 := by
  unfold tailWord_3256238
  simp only [CollatzResearch.WordTrace]
  refine ⟨14845594597151665252555171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79176504518142214680294245 14845594597151665252555171)
  ·
    refine ⟨22268391895727497878832757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14845594597151665252555171 22268391895727497878832757)
    ·
      refine ⟨2087661740224452926140571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22268391895727497878832757 2087661740224452926140571)
      ·
        refine ⟨3131492610336679389210857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2087661740224452926140571 3131492610336679389210857)
        ·
          refine ⟨2348619457752509541908143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3131492610336679389210857 2348619457752509541908143)
          ·
            refine ⟨3522929186628764312862215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2348619457752509541908143 3522929186628764312862215)
            ·
              refine ⟨5284393779943146469293323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3522929186628764312862215 5284393779943146469293323)
              ·
                refine ⟨7926590669914719703939985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5284393779943146469293323 7926590669914719703939985)
                ·
                  refine ⟨5944943002436039777954989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7926590669914719703939985 5944943002436039777954989)
                  ·
                    refine ⟨2229353625913514916733121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5944943002436039777954989 2229353625913514916733121)
                    ·
                      refine ⟨1672015219435136187549841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2229353625913514916733121 1672015219435136187549841)
                      ·
                        rfl

theorem cell23_3256238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_3256238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256238 prefixEnd_3256238 := by exact prefixLift 3256238
  have htrace : WordTrace (prefixWord ++ tailWord_3256238) baseStart_3256238 baseEnd_3256238 := by
    simpa [prefixWord, tailWord_3256238, baseEnd_3256238] using wordTrace_append hprefix tailTrace_3256238
  have hstable : (prefixWord ++ tailWord_3256238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256238).length < 2 ^ (prefixWord ++ tailWord_3256238).sum := by decide
  have hdescent : baseEnd_3256238 < baseStart_3256238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256243 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 3, 3, 2]
def baseStart_3256243 : Nat := 118140960795 + 3256243 * 2 ^ 59
def prefixEnd_3256243 : Nat := 4983230072969 + 3 ^ 40 * 3256243 * 2
def baseEnd_3256243 : Nat := 1672017786838408667987317

theorem tailTrace_3256243 : CollatzResearch.WordTrace tailWord_3256243 prefixEnd_3256243 1672017786838408667987317 := by
  unfold tailWord_3256243
  simp only [CollatzResearch.WordTrace]
  refine ⟨118764939142195207874373383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79176626094796805249582255 118764939142195207874373383)
  ·
    refine ⟨178147408713292811811560075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118764939142195207874373383 178147408713292811811560075)
    ·
      refine ⟨267221113069939217717340113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178147408713292811811560075 267221113069939217717340113)
      ·
        refine ⟨200415834802454413288005085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267221113069939217717340113 200415834802454413288005085)
        ·
          refine ⟨75155938050920404983001907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200415834802454413288005085 75155938050920404983001907)
          ·
            refine ⟨112733907076380607474502861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75155938050920404983001907 112733907076380607474502861)
            ·
              refine ⟨42275215153642727802938573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112733907076380607474502861 42275215153642727802938573)
              ·
                refine ⟨15853205682616022926101965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42275215153642727802938573 15853205682616022926101965)
                ·
                  refine ⟨5944952130981008597288237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15853205682616022926101965 5944952130981008597288237)
                  ·
                    refine ⟨2229357049117878223983089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5944952130981008597288237 2229357049117878223983089)
                    ·
                      refine ⟨1672017786838408667987317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2229357049117878223983089 1672017786838408667987317)
                      ·
                        rfl

theorem cell23_3256243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 3, 2].length) (baseStart_3256243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256243 prefixEnd_3256243 := by exact prefixLift 3256243
  have htrace : WordTrace (prefixWord ++ tailWord_3256243) baseStart_3256243 baseEnd_3256243 := by
    simpa [prefixWord, tailWord_3256243, baseEnd_3256243] using wordTrace_append hprefix tailTrace_3256243
  have hstable : (prefixWord ++ tailWord_3256243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256243).length < 2 ^ (prefixWord ++ tailWord_3256243).sum := by decide
  have hdescent : baseEnd_3256243 < baseStart_3256243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256266 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 2, 6]
def baseStart_3256266 : Nat := 118140960795 + 3256266 * 2 ^ 59
def prefixEnd_3256266 : Nat := 4983230072969 + 3 ^ 40 * 3256266 * 2
def baseEnd_3256266 : Nat := 557343198964487359333237

theorem tailTrace_3256266 : CollatzResearch.WordTrace tailWord_3256266 prefixEnd_3256266 557343198964487359333237 := by
  unfold tailWord_3256266
  simp only [CollatzResearch.WordTrace]
  refine ⟨29691444505277970700615163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79177185347407921868307101 29691444505277970700615163)
  ·
    refine ⟨44537166757916956050922745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29691444505277970700615163 44537166757916956050922745)
    ·
      refine ⟨33402875068437717038192059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44537166757916956050922745 33402875068437717038192059)
      ·
        refine ⟨50104312602656575557288089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33402875068437717038192059 50104312602656575557288089)
        ·
          refine ⟨37578234451992431667966067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50104312602656575557288089 37578234451992431667966067)
          ·
            refine ⟨56367351677988647501949101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37578234451992431667966067 56367351677988647501949101)
            ·
              refine ⟨21137756879245742813230913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56367351677988647501949101 21137756879245742813230913)
              ·
                refine ⟨15853317659434307109923185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21137756879245742813230913 15853317659434307109923185)
                ·
                  refine ⟨11889988244575730332442389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15853317659434307109923185 11889988244575730332442389)
                  ·
                    refine ⟨557343198964487359333237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11889988244575730332442389 557343198964487359333237)
                    ·
                      rfl

theorem cell23_3256266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_3256266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256266 prefixEnd_3256266 := by exact prefixLift 3256266
  have htrace : WordTrace (prefixWord ++ tailWord_3256266) baseStart_3256266 baseEnd_3256266 := by
    simpa [prefixWord, tailWord_3256266, baseEnd_3256266] using wordTrace_append hprefix tailTrace_3256266
  have hstable : (prefixWord ++ tailWord_3256266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256266).length < 2 ^ (prefixWord ++ tailWord_3256266).sum := by decide
  have hdescent : baseEnd_3256266 < baseStart_3256266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256310 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5]
def baseStart_3256310 : Nat := 118140960795 + 3256310 * 2 ^ 59
def prefixEnd_3256310 : Nat := 4983230072969 + 3 ^ 40 * 3256310 * 2
def baseEnd_3256310 : Nat := 1672052190042259905849509

theorem tailTrace_3256310 : CollatzResearch.WordTrace tailWord_3256310 prefixEnd_3256310 1672052190042259905849509 := by
  unfold tailWord_3256310
  simp only [CollatzResearch.WordTrace]
  refine ⟨7422961427059529894816399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79178255221968318878041589 7422961427059529894816399)
  ·
    refine ⟨11134442140589294842224599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7422961427059529894816399 11134442140589294842224599)
    ·
      refine ⟨16701663210883942263336899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11134442140589294842224599 16701663210883942263336899)
      ·
        refine ⟨25052494816325913395005349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16701663210883942263336899 25052494816325913395005349)
        ·
          refine ⟨4697342778061108761563503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25052494816325913395005349 4697342778061108761563503)
          ·
            refine ⟨7046014167091663142345255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4697342778061108761563503 7046014167091663142345255)
            ·
              refine ⟨10569021250637494713517883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7046014167091663142345255 10569021250637494713517883)
              ·
                refine ⟨15853531875956242070276825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10569021250637494713517883 15853531875956242070276825)
                ·
                  refine ⟨11890148906967181552707619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15853531875956242070276825 11890148906967181552707619)
                  ·
                    refine ⟨17835223360450772329061429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11890148906967181552707619 17835223360450772329061429)
                    ·
                      refine ⟨1672052190042259905849509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17835223360450772329061429 1672052190042259905849509)
                      ·
                        rfl

theorem cell23_3256310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_3256310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256310 prefixEnd_3256310 := by exact prefixLift 3256310
  have htrace : WordTrace (prefixWord ++ tailWord_3256310) baseStart_3256310 baseEnd_3256310 := by
    simpa [prefixWord, tailWord_3256310, baseEnd_3256310] using wordTrace_append hprefix tailTrace_3256310
  have hstable : (prefixWord ++ tailWord_3256310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256310).length < 2 ^ (prefixWord ++ tailWord_3256310).sum := by decide
  have hdescent : baseEnd_3256310 < baseStart_3256310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256330 : List Nat := [3, 1, 2, 2, 4, 2, 1, 1, 7]
def baseStart_3256330 : Nat := 118140960795 + 3256330 * 2 ^ 59
def prefixEnd_3256330 : Nat := 4983230072969 + 3 ^ 40 * 3256330 * 2
def baseEnd_3256330 : Nat := 185784717739483314177713

theorem tailTrace_3256330 : CollatzResearch.WordTrace tailWord_3256330 prefixEnd_3256330 185784717739483314177713 := by
  unfold tailWord_3256330
  simp only [CollatzResearch.WordTrace]
  refine ⟨29692028073220005433197611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79178741528586681155193629 29692028073220005433197611)
  ·
    refine ⟨44538042109830008149796417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29692028073220005433197611 44538042109830008149796417)
    ·
      refine ⟨33403531582372506112347313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44538042109830008149796417 33403531582372506112347313)
      ·
        refine ⟨25052648686779379584260485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33403531582372506112347313 25052648686779379584260485)
        ·
          refine ⟨4697371628771133672048841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25052648686779379584260485 4697371628771133672048841)
          ·
            refine ⟨3523028721578350254036631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4697371628771133672048841 3523028721578350254036631)
            ·
              refine ⟨5284543082367525381054947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3523028721578350254036631 5284543082367525381054947)
              ·
                refine ⟨7926814623551288071582421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5284543082367525381054947 7926814623551288071582421)
                ·
                  refine ⟨185784717739483314177713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7926814623551288071582421 185784717739483314177713)
                  ·
                    rfl

theorem cell23_3256330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 7].length) (baseStart_3256330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256330 prefixEnd_3256330 := by exact prefixLift 3256330
  have htrace : WordTrace (prefixWord ++ tailWord_3256330) baseStart_3256330 baseEnd_3256330 := by
    simpa [prefixWord, tailWord_3256330, baseEnd_3256330] using wordTrace_append hprefix tailTrace_3256330
  have hstable : (prefixWord ++ tailWord_3256330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256330).length < 2 ^ (prefixWord ++ tailWord_3256330).sum := by decide
  have hdescent : baseEnd_3256330 < baseStart_3256330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256336 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 5]
def baseStart_3256336 : Nat := 118140960795 + 3256336 * 2 ^ 59
def prefixEnd_3256336 : Nat := 4983230072969 + 3 ^ 40 * 3256336 * 2
def baseEnd_3256336 : Nat := 1672065540539276804124389

theorem tailTrace_3256336 : CollatzResearch.WordTrace tailWord_3256336 prefixEnd_3256336 1672065540539276804124389 := by
  unfold tailWord_3256336
  simp only [CollatzResearch.WordTrace]
  refine ⟨59384165565429142378754431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79178887420572189838339241 59384165565429142378754431)
  ·
    refine ⟨89076248348143713568131647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59384165565429142378754431 89076248348143713568131647)
    ·
      refine ⟨133614372522215570352197471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89076248348143713568131647 133614372522215570352197471)
      ·
        refine ⟨200421558783323355528296207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133614372522215570352197471 200421558783323355528296207)
        ·
          refine ⟨300632338174985033292444311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200421558783323355528296207 300632338174985033292444311)
          ·
            refine ⟨450948507262477549938666467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300632338174985033292444311 450948507262477549938666467)
            ·
              refine ⟨676422760893716324907999701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450948507262477549938666467 676422760893716324907999701)
              ·
                refine ⟨15853658458446476365031243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 676422760893716324907999701 15853658458446476365031243)
                ·
                  refine ⟨23780487687669714547546865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15853658458446476365031243 23780487687669714547546865)
                  ·
                    refine ⟨17835365765752285910660149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23780487687669714547546865 17835365765752285910660149)
                    ·
                      refine ⟨1672065540539276804124389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17835365765752285910660149 1672065540539276804124389)
                      ·
                        rfl

theorem cell23_3256336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 5].length) (baseStart_3256336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256336 prefixEnd_3256336 := by exact prefixLift 3256336
  have htrace : WordTrace (prefixWord ++ tailWord_3256336) baseStart_3256336 baseEnd_3256336 := by
    simpa [prefixWord, tailWord_3256336, baseEnd_3256336] using wordTrace_append hprefix tailTrace_3256336
  have hstable : (prefixWord ++ tailWord_3256336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256336).length < 2 ^ (prefixWord ++ tailWord_3256336).sum := by decide
  have hdescent : baseEnd_3256336 < baseStart_3256336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256341 : List Nat := [1, 3, 2, 1, 5, 2, 2, 1, 2, 2, 2]
def baseStart_3256341 : Nat := 118140960795 + 3256341 * 2 ^ 59
def prefixEnd_3256341 : Nat := 4983230072969 + 3 ^ 40 * 3256341 * 2
def baseEnd_3256341 : Nat := 1672068107942549284561867

theorem tailTrace_3256341 : CollatzResearch.WordTrace tailWord_3256341 prefixEnd_3256341 1672068107942549284561867 := by
  unfold tailWord_3256341
  simp only [CollatzResearch.WordTrace]
  refine ⟨118768513495840170611440877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79179008997226780407627251 118768513495840170611440877)
  ·
    refine ⟨44538192560940063979290329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118768513495840170611440877 44538192560940063979290329)
    ·
      refine ⟨33403644420705047984467747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44538192560940063979290329 33403644420705047984467747)
      ·
        refine ⟨50105466631057571976701621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33403644420705047984467747 50105466631057571976701621)
        ·
          refine ⟨4697387496661647372815777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50105466631057571976701621 4697387496661647372815777)
          ·
            refine ⟨3523040622496235529611833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4697387496661647372815777 3523040622496235529611833)
            ·
              refine ⟨2642280466872176647208875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3523040622496235529611833 2642280466872176647208875)
              ·
                refine ⟨3963420700308264970813313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2642280466872176647208875 3963420700308264970813313)
                ·
                  refine ⟨2972565525231198728109985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3963420700308264970813313 2972565525231198728109985)
                  ·
                    refine ⟨2229424143923399046082489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2972565525231198728109985 2229424143923399046082489)
                    ·
                      refine ⟨1672068107942549284561867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2229424143923399046082489 1672068107942549284561867)
                      ·
                        rfl

theorem cell23_3256341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 2, 2, 2].length) (baseStart_3256341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256341 prefixEnd_3256341 := by exact prefixLift 3256341
  have htrace : WordTrace (prefixWord ++ tailWord_3256341) baseStart_3256341 baseEnd_3256341 := by
    simpa [prefixWord, tailWord_3256341, baseEnd_3256341] using wordTrace_append hprefix tailTrace_3256341
  have hstable : (prefixWord ++ tailWord_3256341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256341).length < 2 ^ (prefixWord ++ tailWord_3256341).sum := by decide
  have hdescent : baseEnd_3256341 < baseStart_3256341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256363 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 3, 6, 2]
def baseStart_3256363 : Nat := 118140960795 + 3256363 * 2 ^ 59
def prefixEnd_3256363 : Nat := 4983230072969 + 3 ^ 40 * 3256363 * 2
def baseEnd_3256363 : Nat := 1672079404516948198486765

theorem tailTrace_3256363 : CollatzResearch.WordTrace tailWord_3256363 prefixEnd_3256363 1672079404516948198486765 := by
  unfold tailWord_3256363
  simp only [CollatzResearch.WordTrace]
  refine ⟨118769315901760468368741743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79179543934506978912494495 118769315901760468368741743)
  ·
    refine ⟨178153973852640702553112615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118769315901760468368741743 178153973852640702553112615)
    ·
      refine ⟨267230960778961053829668923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178153973852640702553112615 267230960778961053829668923)
      ·
        refine ⟨400846441168441580744503385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267230960778961053829668923 400846441168441580744503385)
        ·
          refine ⟨300634830876331185558377539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400846441168441580744503385 300634830876331185558377539)
          ·
            refine ⟨450952246314496778337566309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300634830876331185558377539 450952246314496778337566309)
            ·
              refine ⟨84553546183968145938293683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 450952246314496778337566309 84553546183968145938293683)
              ·
                refine ⟨126830319275952218907440525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84553546183968145938293683 126830319275952218907440525)
                ·
                  refine ⟨47561369728482082090290197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126830319275952218907440525 47561369728482082090290197)
                  ·
                    refine ⟨2229439206022597597982353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47561369728482082090290197 2229439206022597597982353)
                    ·
                      refine ⟨1672079404516948198486765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2229439206022597597982353 1672079404516948198486765)
                      ·
                        rfl

theorem cell23_3256363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 6, 2].length) (baseStart_3256363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256363 prefixEnd_3256363 := by exact prefixLift 3256363
  have htrace : WordTrace (prefixWord ++ tailWord_3256363) baseStart_3256363 baseEnd_3256363 := by
    simpa [prefixWord, tailWord_3256363, baseEnd_3256363] using wordTrace_append hprefix tailTrace_3256363
  have hstable : (prefixWord ++ tailWord_3256363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256363).length < 2 ^ (prefixWord ++ tailWord_3256363).sum := by decide
  have hdescent : baseEnd_3256363 < baseStart_3256363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256380 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 2, 4, 2]
def baseStart_3256380 : Nat := 118140960795 + 3256380 * 2 ^ 59
def prefixEnd_3256380 : Nat := 4983230072969 + 3 ^ 40 * 3256380 * 2
def baseEnd_3256380 : Nat := 1672088133688074631974187

theorem tailTrace_3256380 : CollatzResearch.WordTrace tailWord_3256380 prefixEnd_3256380 1672088133688074631974187 := by
  unfold tailWord_3256380
  simp only [CollatzResearch.WordTrace]
  refine ⟨59384967971349440136055297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79179957295132586848073729 59384967971349440136055297)
  ·
    refine ⟨44538725978512080102041473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59384967971349440136055297 44538725978512080102041473)
    ·
      refine ⟨33404044483884060076531105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44538725978512080102041473 33404044483884060076531105)
      ·
        refine ⟨25053033362913045057398329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33404044483884060076531105 25053033362913045057398329)
        ·
          refine ⟨18789775022184783793048747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25053033362913045057398329 18789775022184783793048747)
          ·
            refine ⟨28184662533277175689573121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18789775022184783793048747 28184662533277175689573121)
            ·
              refine ⟨21138496899957881767179841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28184662533277175689573121 21138496899957881767179841)
              ·
                refine ⟨15853872674968411325384881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21138496899957881767179841 15853872674968411325384881)
                ·
                  refine ⟨11890404506226308494038661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15853872674968411325384881 11890404506226308494038661)
                  ·
                    refine ⟨2229450844917432842632249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11890404506226308494038661 2229450844917432842632249)
                    ·
                      refine ⟨1672088133688074631974187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2229450844917432842632249 1672088133688074631974187)
                      ·
                        rfl

theorem cell23_3256380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_3256380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256380 prefixEnd_3256380 := by exact prefixLift 3256380
  have htrace : WordTrace (prefixWord ++ tailWord_3256380) baseStart_3256380 baseEnd_3256380 := by
    simpa [prefixWord, tailWord_3256380, baseEnd_3256380] using wordTrace_append hprefix tailTrace_3256380
  have hstable : (prefixWord ++ tailWord_3256380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256380).length < 2 ^ (prefixWord ++ tailWord_3256380).sum := by decide
  have hdescent : baseEnd_3256380 < baseStart_3256380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256397 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 2, 4, 2]
def baseStart_3256397 : Nat := 118140960795 + 3256397 * 2 ^ 59
def prefixEnd_3256397 : Nat := 4983230072969 + 3 ^ 40 * 3256397 * 2
def baseEnd_3256397 : Nat := 1672096862859201065461609

theorem tailTrace_3256397 : CollatzResearch.WordTrace tailWord_3256397 prefixEnd_3256397 1672096862859201065461609 := by
  unfold tailWord_3256397
  simp only [CollatzResearch.WordTrace]
  refine ⟨118770555983637292175479445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79180370655758194783652963 118770555983637292175479445)
  ·
    refine ⟨5567369811732998070725599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 118770555983637292175479445 5567369811732998070725599)
    ·
      refine ⟨8351054717599497106088399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5567369811732998070725599 8351054717599497106088399)
      ·
        refine ⟨12526582076399245659132599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8351054717599497106088399 12526582076399245659132599)
        ·
          refine ⟨18789873114598868488698899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12526582076399245659132599 18789873114598868488698899)
          ·
            refine ⟨28184809671898302733048349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18789873114598868488698899 28184809671898302733048349)
            ·
              refine ⟨10569303626961863524893131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28184809671898302733048349 10569303626961863524893131)
              ·
                refine ⟨15853955440442795287339697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10569303626961863524893131 15853955440442795287339697)
                ·
                  refine ⟨11890466580332096465504773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15853955440442795287339697 11890466580332096465504773)
                  ·
                    refine ⟨2229462483812268087282145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11890466580332096465504773 2229462483812268087282145)
                    ·
                      refine ⟨1672096862859201065461609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2229462483812268087282145 1672096862859201065461609)
                      ·
                        rfl

theorem cell23_3256397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_3256397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256397 prefixEnd_3256397 := by exact prefixLift 3256397
  have htrace : WordTrace (prefixWord ++ tailWord_3256397) baseStart_3256397 baseEnd_3256397 := by
    simpa [prefixWord, tailWord_3256397, baseEnd_3256397] using wordTrace_append hprefix tailTrace_3256397
  have hstable : (prefixWord ++ tailWord_3256397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256397).length < 2 ^ (prefixWord ++ tailWord_3256397).sum := by decide
  have hdescent : baseEnd_3256397 < baseStart_3256397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256414 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_3256414 : Nat := 118140960795 + 3256414 * 2 ^ 59
def prefixEnd_3256414 : Nat := 4983230072969 + 3 ^ 40 * 3256414 * 2
def baseEnd_3256414 : Nat := 1672105592030327498949031

theorem tailTrace_3256414 : CollatzResearch.WordTrace tailWord_3256414 prefixEnd_3256414 1672105592030327498949031 := by
  unfold tailWord_3256414
  simp only [CollatzResearch.WordTrace]
  refine ⟨14846397003071963009856037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79180784016383802719232197 14846397003071963009856037)
  ·
    refine ⟨2783699438075993064348007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14846397003071963009856037 2783699438075993064348007)
    ·
      refine ⟨4175549157113989596522011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2783699438075993064348007 4175549157113989596522011)
      ·
        refine ⟨6263323735670984394783017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4175549157113989596522011 6263323735670984394783017)
        ·
          refine ⟨4697492801753238296087263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6263323735670984394783017 4697492801753238296087263)
          ·
            refine ⟨7046239202629857444130895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4697492801753238296087263 7046239202629857444130895)
            ·
              refine ⟨10569358803944786166196343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7046239202629857444130895 10569358803944786166196343)
              ·
                refine ⟨15854038205917179249294515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10569358803944786166196343 15854038205917179249294515)
                ·
                  refine ⟨23781057308875768873941773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15854038205917179249294515 23781057308875768873941773)
                  ·
                    refine ⟨8917896490828413327728165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23781057308875768873941773 8917896490828413327728165)
                    ·
                      refine ⟨1672105592030327498949031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8917896490828413327728165 1672105592030327498949031)
                      ·
                        rfl

theorem cell23_3256414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_3256414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256414 prefixEnd_3256414 := by exact prefixLift 3256414
  have htrace : WordTrace (prefixWord ++ tailWord_3256414) baseStart_3256414 baseEnd_3256414 := by
    simpa [prefixWord, tailWord_3256414, baseEnd_3256414] using wordTrace_append hprefix tailTrace_3256414
  have hstable : (prefixWord ++ tailWord_3256414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256414).length < 2 ^ (prefixWord ++ tailWord_3256414).sum := by decide
  have hdescent : baseEnd_3256414 < baseStart_3256414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256440 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 4, 3, 2]
def baseStart_3256440 : Nat := 118140960795 + 3256440 * 2 ^ 59
def prefixEnd_3256440 : Nat := 4983230072969 + 3 ^ 40 * 3256440 * 2
def baseEnd_3256440 : Nat := 1672118942527344397223911

theorem tailTrace_3256440 : CollatzResearch.WordTrace tailWord_3256440 prefixEnd_3256440 1672118942527344397223911 := by
  unfold tailWord_3256440
  simp only [CollatzResearch.WordTrace]
  refine ⟨59386062161240755259647387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79181416214987673679529849 59386062161240755259647387)
  ·
    refine ⟨89079093241861132889471081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59386062161240755259647387 89079093241861132889471081)
    ·
      refine ⟨66809319931395849667103311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89079093241861132889471081 66809319931395849667103311)
      ·
        refine ⟨100213979897093774500654967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66809319931395849667103311 100213979897093774500654967)
        ·
          refine ⟨150320969845640661750982451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100213979897093774500654967 150320969845640661750982451)
          ·
            refine ⟨225481454768460992626473677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150320969845640661750982451 225481454768460992626473677)
            ·
              refine ⟨84555545538172872234927629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225481454768460992626473677 84555545538172872234927629)
              ·
                refine ⟨31708329576814827088097861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84555545538172872234927629 31708329576814827088097861)
                ·
                  refine ⟨5945311795652780079018349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31708329576814827088097861 5945311795652780079018349)
                  ·
                    refine ⟨2229491923369792529631881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5945311795652780079018349 2229491923369792529631881)
                    ·
                      refine ⟨1672118942527344397223911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2229491923369792529631881 1672118942527344397223911)
                      ·
                        rfl

theorem cell23_3256440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 4, 3, 2].length) (baseStart_3256440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256440 prefixEnd_3256440 := by exact prefixLift 3256440
  have htrace : WordTrace (prefixWord ++ tailWord_3256440) baseStart_3256440 baseEnd_3256440 := by
    simpa [prefixWord, tailWord_3256440, baseEnd_3256440] using wordTrace_append hprefix tailTrace_3256440
  have hstable : (prefixWord ++ tailWord_3256440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256440).length < 2 ^ (prefixWord ++ tailWord_3256440).sum := by decide
  have hdescent : baseEnd_3256440 < baseStart_3256440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256473 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 2, 6, 3]
def baseStart_3256473 : Nat := 118140960795 + 3256473 * 2 ^ 59
def prefixEnd_3256473 : Nat := 4983230072969 + 3 ^ 40 * 3256473 * 2
def baseEnd_3256473 : Nat := 1672135887388942768111259

theorem tailTrace_3256473 : CollatzResearch.WordTrace tailWord_3256473 prefixEnd_3256473 1672135887388942768111259 := by
  unfold tailWord_3256473
  simp only [CollatzResearch.WordTrace]
  refine ⟨118773327931361957155246073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79182218620907971436830715 118773327931361957155246073)
  ·
    refine ⟨89079995948521467866434555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118773327931361957155246073 89079995948521467866434555)
    ·
      refine ⟨133619993922782201799651833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89079995948521467866434555 133619993922782201799651833)
      ·
        refine ⟨100214995442086651349738875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133619993922782201799651833 100214995442086651349738875)
        ·
          refine ⟨150322493163129977024608313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100214995442086651349738875 150322493163129977024608313)
          ·
            refine ⟨112741869872347482768456235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150322493163129977024608313 112741869872347482768456235)
            ·
              refine ⟨169112804808521224152684353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112741869872347482768456235 169112804808521224152684353)
              ·
                refine ⟨126834603606390918114513265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169112804808521224152684353 126834603606390918114513265)
                ·
                  refine ⟨95125952704793188585884949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126834603606390918114513265 95125952704793188585884949)
                  ·
                    refine ⟨4459029033037180714963357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95125952704793188585884949 4459029033037180714963357)
                    ·
                      refine ⟨1672135887388942768111259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4459029033037180714963357 1672135887388942768111259)
                      ·
                        rfl

theorem cell23_3256473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 6, 3].length) (baseStart_3256473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256473 prefixEnd_3256473 := by exact prefixLift 3256473
  have htrace : WordTrace (prefixWord ++ tailWord_3256473) baseStart_3256473 baseEnd_3256473 := by
    simpa [prefixWord, tailWord_3256473, baseEnd_3256473] using wordTrace_append hprefix tailTrace_3256473
  have hstable : (prefixWord ++ tailWord_3256473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256473).length < 2 ^ (prefixWord ++ tailWord_3256473).sum := by decide
  have hdescent : baseEnd_3256473 < baseStart_3256473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256480 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 4, 4]
def baseStart_3256480 : Nat := 118140960795 + 3256480 * 2 ^ 59
def prefixEnd_3256480 : Nat := 4983230072969 + 3 ^ 40 * 3256480 * 2
def baseEnd_3256480 : Nat := 557379827251174746907909

theorem tailTrace_3256480 : CollatzResearch.WordTrace tailWord_3256480 prefixEnd_3256480 557379827251174746907909 := by
  unfold tailWord_3256480
  simp only [CollatzResearch.WordTrace]
  refine ⟨59386791621168298675375447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79182388828224398233833929 59386791621168298675375447)
  ·
    refine ⟨89080187431752448013063171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59386791621168298675375447 89080187431752448013063171)
    ·
      refine ⟨133620281147628672019594757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89080187431752448013063171 133620281147628672019594757)
      ·
        refine ⟨25053802715180376003674017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133620281147628672019594757 25053802715180376003674017)
        ·
          refine ⟨18790352036385282002755513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25053802715180376003674017 18790352036385282002755513)
          ·
            refine ⟨14092764027288961502066635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18790352036385282002755513 14092764027288961502066635)
            ·
              refine ⟨21139146040933442253099953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14092764027288961502066635 21139146040933442253099953)
              ·
                refine ⟨15854359530700081689824965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21139146040933442253099953 15854359530700081689824965)
                ·
                  refine ⟨2972692412006265316842181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15854359530700081689824965 2972692412006265316842181)
                  ·
                    refine ⟨557379827251174746907909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2972692412006265316842181 557379827251174746907909)
                    ·
                      rfl

theorem cell23_3256480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 4, 4].length) (baseStart_3256480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256480 prefixEnd_3256480 := by exact prefixLift 3256480
  have htrace : WordTrace (prefixWord ++ tailWord_3256480) baseStart_3256480 baseEnd_3256480 := by
    simpa [prefixWord, tailWord_3256480, baseEnd_3256480] using wordTrace_append hprefix tailTrace_3256480
  have hstable : (prefixWord ++ tailWord_3256480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256480).length < 2 ^ (prefixWord ++ tailWord_3256480).sum := by decide
  have hdescent : baseEnd_3256480 < baseStart_3256480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256481 : List Nat := [1, 2, 3, 3, 1, 4, 1, 3, 1, 1, 3]
def baseStart_3256481 : Nat := 118140960795 + 3256481 * 2 ^ 59
def prefixEnd_3256481 : Nat := 4983230072969 + 3 ^ 40 * 3256481 * 2
def baseEnd_3256481 : Nat := 1672139995234178736811223

theorem tailTrace_3256481 : CollatzResearch.WordTrace tailWord_3256481 prefixEnd_3256481 1672139995234178736811223 := by
  unfold tailWord_3256481
  simp only [CollatzResearch.WordTrace]
  refine ⟨118773619715332974521537297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79182413143555316347691531 118773619715332974521537297)
  ·
    refine ⟨89080214786499730891152973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118773619715332974521537297 89080214786499730891152973)
    ·
      refine ⟨33405080544937399084182365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89080214786499730891152973 33405080544937399084182365)
      ·
        refine ⟨12526905204351524656568387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33405080544937399084182365 12526905204351524656568387)
        ·
          refine ⟨18790357806527286984852581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12526905204351524656568387 18790357806527286984852581)
          ·
            refine ⟨3523192088723866309659859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18790357806527286984852581 3523192088723866309659859)
            ·
              refine ⟨5284788133085799464489789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3523192088723866309659859 5284788133085799464489789)
              ·
                refine ⟨1981795549907174799183671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5284788133085799464489789 1981795549907174799183671)
                ·
                  refine ⟨2972693324860762198775507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1981795549907174799183671 2972693324860762198775507)
                  ·
                    refine ⟨4459039987291143298163261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2972693324860762198775507 4459039987291143298163261)
                    ·
                      refine ⟨1672139995234178736811223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4459039987291143298163261 1672139995234178736811223)
                      ·
                        rfl

theorem cell23_3256481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_3256481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256481 prefixEnd_3256481 := by exact prefixLift 3256481
  have htrace : WordTrace (prefixWord ++ tailWord_3256481) baseStart_3256481 baseEnd_3256481 := by
    simpa [prefixWord, tailWord_3256481, baseEnd_3256481] using wordTrace_append hprefix tailTrace_3256481
  have hstable : (prefixWord ++ tailWord_3256481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256481).length < 2 ^ (prefixWord ++ tailWord_3256481).sum := by decide
  have hdescent : baseEnd_3256481 < baseStart_3256481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3256520 : List Nat := [2, 1, 3, 1, 2, 1, 1, 5, 1, 3, 3]
def baseStart_3256520 : Nat := 118140960795 + 3256520 * 2 ^ 59
def prefixEnd_3256520 : Nat := 4983230072969 + 3 ^ 40 * 3256520 * 2
def baseEnd_3256520 : Nat := 1672160020979704084223543

theorem tailTrace_3256520 : CollatzResearch.WordTrace tailWord_3256520 prefixEnd_3256520 1672160020979704084223543 := by
  unfold tailWord_3256520
  simp only [CollatzResearch.WordTrace]
  refine ⟨59387521081095842091103507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79183361441461122788138009 59387521081095842091103507)
  ·
    refine ⟨89081281621643763136655261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59387521081095842091103507 89081281621643763136655261)
    ·
      refine ⟨33405480608116411176245723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89081281621643763136655261 33405480608116411176245723)
      ·
        refine ⟨50108220912174616764368585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33405480608116411176245723 50108220912174616764368585)
        ·
          refine ⟨37581165684130962573276439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50108220912174616764368585 37581165684130962573276439)
          ·
            refine ⟨56371748526196443859914659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37581165684130962573276439 56371748526196443859914659)
            ·
              refine ⟨84557622789294665789871989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56371748526196443859914659 84557622789294665789871989)
              ·
                refine ⟨7927277136496374917800499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84557622789294665789871989 7927277136496374917800499)
                ·
                  refine ⟨11890915704744562376700749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7927277136496374917800499 11890915704744562376700749)
                  ·
                    refine ⟨4459093389279210891262781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11890915704744562376700749 4459093389279210891262781)
                    ·
                      refine ⟨1672160020979704084223543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4459093389279210891262781 1672160020979704084223543)
                      ·
                        rfl

theorem cell23_3256520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_3256520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3256520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3256520 prefixEnd_3256520 := by exact prefixLift 3256520
  have htrace : WordTrace (prefixWord ++ tailWord_3256520) baseStart_3256520 baseEnd_3256520 := by
    simpa [prefixWord, tailWord_3256520, baseEnd_3256520] using wordTrace_append hprefix tailTrace_3256520
  have hstable : (prefixWord ++ tailWord_3256520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3256520).length < 2 ^ (prefixWord ++ tailWord_3256520).sum := by decide
  have hdescent : baseEnd_3256520 < baseStart_3256520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3256520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
