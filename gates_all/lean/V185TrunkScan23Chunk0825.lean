import V185TrunkScan23Chunk0824

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4880343 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 3, 4, 2]
def baseStart_4880343 : Nat := 118140960795 + 4880343 * 2 ^ 59
def prefixEnd_4880343 : Nat := 4983230072969 + 3 ^ 40 * 4880343 * 2
def baseEnd_4880343 : Nat := 2505961717805504369268217

theorem tailTrace_4880343 : CollatzResearch.WordTrace tailWord_4880343 prefixEnd_4880343 2505961717805504369268217 := by
  unfold tailWord_4880343
  simp only [CollatzResearch.WordTrace]
  refine ⟨178000732558358282071485683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118667155038905521380990455 178000732558358282071485683)
  ·
    refine ⟨267001098837537423107228525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178000732558358282071485683 267001098837537423107228525)
    ·
      refine ⟨100125412064076533665210697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267001098837537423107228525 100125412064076533665210697)
      ·
        refine ⟨75094059048057400248908023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100125412064076533665210697 75094059048057400248908023)
        ·
          refine ⟨112641088572086100373362035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75094059048057400248908023 112641088572086100373362035)
          ·
            refine ⟨168961632858129150560043053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112641088572086100373362035 168961632858129150560043053)
            ·
              refine ⟨63360612321798431460016145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168961632858129150560043053 63360612321798431460016145)
              ·
                refine ⟨47520459241348823595012109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63360612321798431460016145 47520459241348823595012109)
                ·
                  refine ⟨17820172215505808848129541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47520459241348823595012109 17820172215505808848129541)
                  ·
                    refine ⟨3341282290407339159024289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17820172215505808848129541 3341282290407339159024289)
                    ·
                      refine ⟨2505961717805504369268217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3341282290407339159024289 2505961717805504369268217)
                      ·
                        rfl

theorem cell23_4880343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 4, 2].length) (baseStart_4880343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880343 prefixEnd_4880343 := by exact prefixLift 4880343
  have htrace : WordTrace (prefixWord ++ tailWord_4880343) baseStart_4880343 baseEnd_4880343 := by
    simpa [prefixWord, tailWord_4880343, baseEnd_4880343] using wordTrace_append hprefix tailTrace_4880343
  have hstable : (prefixWord ++ tailWord_4880343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880343).length < 2 ^ (prefixWord ++ tailWord_4880343).sum := by decide
  have hdescent : baseEnd_4880343 < baseStart_4880343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880360 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 6, 2, 2]
def baseStart_4880360 : Nat := 118140960795 + 4880360 * 2 ^ 59
def prefixEnd_4880360 : Nat := 4983230072969 + 3 ^ 40 * 4880360 * 2
def baseEnd_4880360 : Nat := 2505970446976630802755639

theorem tailTrace_4880360 : CollatzResearch.WordTrace tailWord_4880360 prefixEnd_4880360 2505970446976630802755639 := by
  unfold tailWord_4880360
  simp only [CollatzResearch.WordTrace]
  refine ⟨89000676299648346987427267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118667568399531129316569689 89000676299648346987427267)
  ·
    refine ⟨133501014449472520481140901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89000676299648346987427267 133501014449472520481140901)
    ·
      refine ⟨25031440209276097590213919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133501014449472520481140901 25031440209276097590213919)
      ·
        refine ⟨37547160313914146385320879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25031440209276097590213919 37547160313914146385320879)
        ·
          refine ⟨56320740470871219577981319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37547160313914146385320879 56320740470871219577981319)
          ·
            refine ⟨84481110706306829366971979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56320740470871219577981319 84481110706306829366971979)
            ·
              refine ⟨126721666059460244050457969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84481110706306829366971979 126721666059460244050457969)
              ·
                refine ⟨95041249544595183037843477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126721666059460244050457969 95041249544595183037843477)
                ·
                  refine ⟨4455058572402899204898913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 95041249544595183037843477 4455058572402899204898913)
                  ·
                    refine ⟨3341293929302174403674185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4455058572402899204898913 3341293929302174403674185)
                    ·
                      refine ⟨2505970446976630802755639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3341293929302174403674185 2505970446976630802755639)
                      ·
                        rfl

theorem cell23_4880360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_4880360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880360 prefixEnd_4880360 := by exact prefixLift 4880360
  have htrace : WordTrace (prefixWord ++ tailWord_4880360) baseStart_4880360 baseEnd_4880360 := by
    simpa [prefixWord, tailWord_4880360, baseEnd_4880360] using wordTrace_append hprefix tailTrace_4880360
  have hstable : (prefixWord ++ tailWord_4880360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880360).length < 2 ^ (prefixWord ++ tailWord_4880360).sum := by decide
  have hdescent : baseEnd_4880360 < baseStart_4880360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880403 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 1, 7, 2]
def baseStart_4880403 : Nat := 118140960795 + 4880403 * 2 ^ 59
def prefixEnd_4880403 : Nat := 4983230072969 + 3 ^ 40 * 4880403 * 2
def baseEnd_4880403 : Nat := 2505992526644774134517941

theorem tailTrace_4880403 : CollatzResearch.WordTrace tailWord_4880403 prefixEnd_4880403 2505992526644774134517941 := by
  unfold tailWord_4880403
  simp only [CollatzResearch.WordTrace]
  refine ⟨178002920938140912318669863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118668613958760608212446575 178002920938140912318669863)
  ·
    refine ⟨267004381407211368478004795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178002920938140912318669863 267004381407211368478004795)
    ·
      refine ⟨400506572110817052717007193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267004381407211368478004795 400506572110817052717007193)
      ·
        refine ⟨300379929083112789537755395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400506572110817052717007193 300379929083112789537755395)
        ·
          refine ⟨450569893624669184306633093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300379929083112789537755395 450569893624669184306633093)
          ·
            refine ⟨84481855054625472057493705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 450569893624669184306633093 84481855054625472057493705)
            ·
              refine ⟨63361391290969104043120279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84481855054625472057493705 63361391290969104043120279)
              ·
                refine ⟨95042086936453656064680419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63361391290969104043120279 95042086936453656064680419)
                ·
                  refine ⟨142563130404680484097020629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95042086936453656064680419 142563130404680484097020629)
                  ·
                    refine ⟨3341323368859698846023921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 142563130404680484097020629 3341323368859698846023921)
                    ·
                      refine ⟨2505992526644774134517941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3341323368859698846023921 2505992526644774134517941)
                      ·
                        rfl

theorem cell23_4880403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 7, 2].length) (baseStart_4880403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880403 prefixEnd_4880403 := by exact prefixLift 4880403
  have htrace : WordTrace (prefixWord ++ tailWord_4880403) baseStart_4880403 baseEnd_4880403 := by
    simpa [prefixWord, tailWord_4880403, baseEnd_4880403] using wordTrace_append hprefix tailTrace_4880403
  have hstable : (prefixWord ++ tailWord_4880403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880403).length < 2 ^ (prefixWord ++ tailWord_4880403).sum := by decide
  have hdescent : baseEnd_4880403 < baseStart_4880403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880413 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 1, 7]
def baseStart_4880413 : Nat := 118140960795 + 4880413 * 2 ^ 59
def prefixEnd_4880413 : Nat := 4983230072969 + 3 ^ 40 * 4880413 * 2
def baseEnd_4880413 : Nat := 835332553817106365130965

theorem tailTrace_4880413 : CollatzResearch.WordTrace tailWord_4880413 prefixEnd_4880413 835332553817106365130965 := by
  unfold tailWord_4880413
  simp only [CollatzResearch.WordTrace]
  refine ⟨178003285668104684026533893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118668857112069789351022595 178003285668104684026533893)
  ·
    refine ⟨33375616062769628254975105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178003285668104684026533893 33375616062769628254975105)
    ·
      refine ⟨25031712047077221191231329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33375616062769628254975105 25031712047077221191231329)
      ·
        refine ⟨18773784035307915893423497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25031712047077221191231329 18773784035307915893423497)
        ·
          refine ⟨14080338026480936920067623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18773784035307915893423497 14080338026480936920067623)
          ·
            refine ⟨21120507039721405380101435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14080338026480936920067623 21120507039721405380101435)
            ·
              refine ⟨31680760559582108070152153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21120507039721405380101435 31680760559582108070152153)
              ·
                refine ⟨23760570419686581052614115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31680760559582108070152153 23760570419686581052614115)
                ·
                  refine ⟨35640855629529871578921173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23760570419686581052614115 35640855629529871578921173)
                  ·
                    refine ⟨835332553817106365130965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35640855629529871578921173 835332553817106365130965)
                    ·
                      rfl

theorem cell23_4880413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_4880413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880413 prefixEnd_4880413 := by exact prefixLift 4880413
  have htrace : WordTrace (prefixWord ++ tailWord_4880413) baseStart_4880413 baseEnd_4880413 := by
    simpa [prefixWord, tailWord_4880413, baseEnd_4880413] using wordTrace_append hprefix tailTrace_4880413
  have hstable : (prefixWord ++ tailWord_4880413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880413).length < 2 ^ (prefixWord ++ tailWord_4880413).sum := by decide
  have hdescent : baseEnd_4880413 < baseStart_4880413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880433 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 1, 3, 4]
def baseStart_4880433 : Nat := 118140960795 + 4880433 * 2 ^ 59
def prefixEnd_4880433 : Nat := 4983230072969 + 3 ^ 40 * 4880433 * 2
def baseEnd_4880433 : Nat := 2506007931064409017142803

theorem tailTrace_4880433 : CollatzResearch.WordTrace tailWord_4880433 prefixEnd_4880433 2506007931064409017142803 := by
  unfold tailWord_4880433
  simp only [CollatzResearch.WordTrace]
  refine ⟨178004015128032227442261953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118669343418688151628174635 178004015128032227442261953)
  ·
    refine ⟨133503011346024170581696465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178004015128032227442261953 133503011346024170581696465)
    ·
      refine ⟨100127258509518127936272349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133503011346024170581696465 100127258509518127936272349)
      ·
        refine ⟨37547721941069297976102131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100127258509518127936272349 37547721941069297976102131)
        ·
          refine ⟨56321582911603946964153197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37547721941069297976102131 56321582911603946964153197)
          ·
            refine ⟨21120593591851480111557449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56321582911603946964153197 21120593591851480111557449)
            ·
              refine ⟨15840445193888610083668087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21120593591851480111557449 15840445193888610083668087)
              ·
                refine ⟨23760667790832915125502131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15840445193888610083668087 23760667790832915125502131)
                ·
                  refine ⟨35641001686249372688253197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23760667790832915125502131 35641001686249372688253197)
                  ·
                    refine ⟨13365375632343514758094949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35641001686249372688253197 13365375632343514758094949)
                    ·
                      refine ⟨2506007931064409017142803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13365375632343514758094949 2506007931064409017142803)
                      ·
                        rfl

theorem cell23_4880433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_4880433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880433 prefixEnd_4880433 := by exact prefixLift 4880433
  have htrace : WordTrace (prefixWord ++ tailWord_4880433) baseStart_4880433 baseEnd_4880433 := by
    simpa [prefixWord, tailWord_4880433, baseEnd_4880433] using wordTrace_append hprefix tailTrace_4880433
  have hstable : (prefixWord ++ tailWord_4880433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880433).length < 2 ^ (prefixWord ++ tailWord_4880433).sum := by decide
  have hdescent : baseEnd_4880433 < baseStart_4880433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880460 : List Nat := [2, 2, 1, 3, 1, 1, 5, 1, 3, 4]
def baseStart_4880460 : Nat := 118140960795 + 4880460 * 2 ^ 59
def prefixEnd_4880460 : Nat := 4983230072969 + 3 ^ 40 * 4880460 * 2
def baseEnd_4880460 : Nat := 835340598347360137168393

theorem tailTrace_4880460 : CollatzResearch.WordTrace tailWord_4880460 prefixEnd_4880460 835340598347360137168393 := by
  unfold tailWord_4880460
  simp only [CollatzResearch.WordTrace]
  refine ⟨89002499949467205526747417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118669999932622940702329889 89002499949467205526747417)
  ·
    refine ⟨66751874962100404145060563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89002499949467205526747417 66751874962100404145060563)
    ·
      refine ⟨100127812443150606217590845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66751874962100404145060563 100127812443150606217590845)
      ·
        refine ⟨37547929666181477331596567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100127812443150606217590845 37547929666181477331596567)
        ·
          refine ⟨56321894499272215997394851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37547929666181477331596567 56321894499272215997394851)
          ·
            refine ⟨84482841748908323996092277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56321894499272215997394851 84482841748908323996092277)
            ·
              refine ⟨7920266413960155374633651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84482841748908323996092277 7920266413960155374633651)
              ·
                refine ⟨11880399620940233061950477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7920266413960155374633651 11880399620940233061950477)
                ·
                  refine ⟨4455149857852587398231429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11880399620940233061950477 4455149857852587398231429)
                  ·
                    refine ⟨835340598347360137168393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4455149857852587398231429 835340598347360137168393)
                    ·
                      rfl

theorem cell23_4880460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 3, 4].length) (baseStart_4880460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880460 prefixEnd_4880460 := by exact prefixLift 4880460
  have htrace : WordTrace (prefixWord ++ tailWord_4880460) baseStart_4880460 baseEnd_4880460 := by
    simpa [prefixWord, tailWord_4880460, baseEnd_4880460] using wordTrace_append hprefix tailTrace_4880460
  have hstable : (prefixWord ++ tailWord_4880460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880460).length < 2 ^ (prefixWord ++ tailWord_4880460).sum := by decide
  have hdescent : baseEnd_4880460 < baseStart_4880460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880473 : List Nat := [1, 2, 1, 2, 2, 1, 5, 3, 6]
def baseStart_4880473 : Nat := 118140960795 + 4880473 * 2 ^ 59
def prefixEnd_4880473 : Nat := 4983230072969 + 3 ^ 40 * 4880473 * 2
def baseEnd_4880473 : Nat := 278447607810065428960291

theorem tailTrace_4880473 : CollatzResearch.WordTrace tailWord_4880473 prefixEnd_4880473 278447607810065428960291 := by
  unfold tailWord_4880473
  simp only [CollatzResearch.WordTrace]
  refine ⟨178005474047887314273718073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118670316031924876182478715 178005474047887314273718073)
  ·
    refine ⟨133504105535915485705288555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178005474047887314273718073 133504105535915485705288555)
    ·
      refine ⟨200256158303873228557932833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133504105535915485705288555 200256158303873228557932833)
      ·
        refine ⟨150192118727904921418449625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200256158303873228557932833 150192118727904921418449625)
        ·
          refine ⟨112644089045928691063837219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150192118727904921418449625 112644089045928691063837219)
          ·
            refine ⟨168966133568893036595755829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112644089045928691063837219 168966133568893036595755829)
            ·
              refine ⟨15840575022083722180852109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 168966133568893036595755829 15840575022083722180852109)
              ·
                refine ⟨5940215633281395817819541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15840575022083722180852109 5940215633281395817819541)
                ·
                  refine ⟨278447607810065428960291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5940215633281395817819541 278447607810065428960291)
                  ·
                    rfl

theorem cell23_4880473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 6].length) (baseStart_4880473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880473 prefixEnd_4880473 := by exact prefixLift 4880473
  have htrace : WordTrace (prefixWord ++ tailWord_4880473) baseStart_4880473 baseEnd_4880473 := by
    simpa [prefixWord, tailWord_4880473, baseEnd_4880473] using wordTrace_append hprefix tailTrace_4880473
  have hstable : (prefixWord ++ tailWord_4880473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880473).length < 2 ^ (prefixWord ++ tailWord_4880473).sum := by decide
  have hdescent : baseEnd_4880473 < baseStart_4880473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880483 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 3]
def baseStart_4880483 : Nat := 118140960795 + 4880483 * 2 ^ 59
def prefixEnd_4880483 : Nat := 4983230072969 + 3 ^ 40 * 4880483 * 2
def baseEnd_4880483 : Nat := 2506033605097133821517573

theorem tailTrace_4880483 : CollatzResearch.WordTrace tailWord_4880483 prefixEnd_4880483 2506033605097133821517573 := by
  unfold tailWord_4880483
  simp only [CollatzResearch.WordTrace]
  refine ⟨178005838777851085981582103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118670559185234057321054735 178005838777851085981582103)
  ·
    refine ⟨267008758166776628972373155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178005838777851085981582103 267008758166776628972373155)
    ·
      refine ⟨400513137250164943458559733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267008758166776628972373155 400513137250164943458559733)
      ·
        refine ⟨37548106617202963449239975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 400513137250164943458559733 37548106617202963449239975)
        ·
          refine ⟨56322159925804445173859963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37548106617202963449239975 56322159925804445173859963)
          ·
            refine ⟨84483239888706667760789945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56322159925804445173859963 84483239888706667760789945)
            ·
              refine ⟨63362429916530000820592459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84483239888706667760789945 63362429916530000820592459)
              ·
                refine ⟨95043644874795001230888689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63362429916530000820592459 95043644874795001230888689)
                ·
                  refine ⟨71282733656096250923166517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95043644874795001230888689 71282733656096250923166517)
                  ·
                    refine ⟨6682756280259023524046861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71282733656096250923166517 6682756280259023524046861)
                    ·
                      refine ⟨2506033605097133821517573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6682756280259023524046861 2506033605097133821517573)
                      ·
                        rfl

theorem cell23_4880483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_4880483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880483 prefixEnd_4880483 := by exact prefixLift 4880483
  have htrace : WordTrace (prefixWord ++ tailWord_4880483) baseStart_4880483 baseEnd_4880483 := by
    simpa [prefixWord, tailWord_4880483, baseEnd_4880483] using wordTrace_append hprefix tailTrace_4880483
  have hstable : (prefixWord ++ tailWord_4880483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880483).length < 2 ^ (prefixWord ++ tailWord_4880483).sum := by decide
  have hdescent : baseEnd_4880483 < baseStart_4880483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880520 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 3, 5]
def baseStart_4880520 : Nat := 118140960795 + 4880520 * 2 ^ 59
def prefixEnd_4880520 : Nat := 4983230072969 + 3 ^ 40 * 4880520 * 2
def baseEnd_4880520 : Nat := 835350867960450058918301

theorem tailTrace_4880520 : CollatzResearch.WordTrace tailWord_4880520 prefixEnd_4880520 835350867960450058918301 := by
  unfold tailWord_4880520
  simp only [CollatzResearch.WordTrace]
  refine ⟨89003594139358520650339507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118671458852478027533786009 89003594139358520650339507)
  ·
    refine ⟨133505391209037780975509261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89003594139358520650339507 133505391209037780975509261)
    ·
      refine ⟨50064521703389167865815973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133505391209037780975509261 50064521703389167865815973)
      ·
        refine ⟨9387097819385468974840495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50064521703389167865815973 9387097819385468974840495)
        ·
          refine ⟨14080646729078203462260743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9387097819385468974840495 14080646729078203462260743)
          ·
            refine ⟨21120970093617305193391115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14080646729078203462260743 21120970093617305193391115)
            ·
              refine ⟨31681455140425957790086673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21120970093617305193391115 31681455140425957790086673)
              ·
                refine ⟨23761091355319468342565005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31681455140425957790086673 23761091355319468342565005)
                ·
                  refine ⟨8910409258244800628461877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23761091355319468342565005 8910409258244800628461877)
                  ·
                    refine ⟨835350867960450058918301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8910409258244800628461877 835350867960450058918301)
                    ·
                      rfl

theorem cell23_4880520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_4880520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880520 prefixEnd_4880520 := by exact prefixLift 4880520
  have htrace : WordTrace (prefixWord ++ tailWord_4880520) baseStart_4880520 baseEnd_4880520 := by
    simpa [prefixWord, tailWord_4880520, baseEnd_4880520] using wordTrace_append hprefix tailTrace_4880520
  have hstable : (prefixWord ++ tailWord_4880520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880520).length < 2 ^ (prefixWord ++ tailWord_4880520).sum := by decide
  have hdescent : baseEnd_4880520 < baseStart_4880520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880540 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_4880540 : Nat := 118140960795 + 4880540 * 2 ^ 59
def prefixEnd_4880540 : Nat := 4983230072969 + 3 ^ 40 * 4880540 * 2
def baseEnd_4880540 : Nat := 2506062873494440098504811

theorem tailTrace_4880540 : CollatzResearch.WordTrace tailWord_4880540 prefixEnd_4880540 2506062873494440098504811 := by
  unfold tailWord_4880540
  simp only [CollatzResearch.WordTrace]
  refine ⟨89003958869322292358203537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118671945159096389810938049 89003958869322292358203537)
  ·
    refine ⟨66752969151991719268652653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89003958869322292358203537 66752969151991719268652653)
    ·
      refine ⟨25032363431996894725744745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66752969151991719268652653 25032363431996894725744745)
      ·
        refine ⟨18774272573997671044308559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25032363431996894725744745 18774272573997671044308559)
        ·
          refine ⟨28161408860996506566462839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18774272573997671044308559 28161408860996506566462839)
          ·
            refine ⟨42242113291494759849694259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28161408860996506566462839 42242113291494759849694259)
            ·
              refine ⟨63363169937242139774541389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42242113291494759849694259 63363169937242139774541389)
              ·
                refine ⟨23761188726465802415453021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63363169937242139774541389 23761188726465802415453021)
                ·
                  refine ⟨8910445772424675905794883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23761188726465802415453021 8910445772424675905794883)
                  ·
                    refine ⟨13365668658637013858692325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8910445772424675905794883 13365668658637013858692325)
                    ·
                      refine ⟨2506062873494440098504811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13365668658637013858692325 2506062873494440098504811)
                      ·
                        rfl

theorem cell23_4880540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_4880540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880540 prefixEnd_4880540 := by exact prefixLift 4880540
  have htrace : WordTrace (prefixWord ++ tailWord_4880540) baseStart_4880540 baseEnd_4880540 := by
    simpa [prefixWord, tailWord_4880540, baseEnd_4880540] using wordTrace_append hprefix tailTrace_4880540
  have hstable : (prefixWord ++ tailWord_4880540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880540).length < 2 ^ (prefixWord ++ tailWord_4880540).sum := by decide
  have hdescent : baseEnd_4880540 < baseStart_4880540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880544 : List Nat := [2, 1, 1, 4, 2, 4, 1, 1, 2, 3, 2]
def baseStart_4880544 : Nat := 118140960795 + 4880544 * 2 ^ 59
def prefixEnd_4880544 : Nat := 4983230072969 + 3 ^ 40 * 4880544 * 2
def baseEnd_4880544 : Nat := 2506064927417058082854793

theorem tailTrace_4880544 : CollatzResearch.WordTrace tailWord_4880544 prefixEnd_4880544 2506064927417058082854793 := by
  unfold tailWord_4880544
  simp only [CollatzResearch.WordTrace]
  refine ⟨89004031815315046699776343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118672042420420062266368457 89004031815315046699776343)
  ·
    refine ⟨133506047722972570049664515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89004031815315046699776343 133506047722972570049664515)
    ·
      refine ⟨200259071584458855074496773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133506047722972570049664515 200259071584458855074496773)
      ·
        refine ⟨37548575922086035326468145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200259071584458855074496773 37548575922086035326468145)
        ·
          refine ⟨28161431941564526494851109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37548575922086035326468145 28161431941564526494851109)
          ·
            refine ⟨5280268489043348717784583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28161431941564526494851109 5280268489043348717784583)
            ·
              refine ⟨7920402733565023076676875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5280268489043348717784583 7920402733565023076676875)
              ·
                refine ⟨11880604100347534615015313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7920402733565023076676875 11880604100347534615015313)
                ·
                  refine ⟨8910453075260650961261485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11880604100347534615015313 8910453075260650961261485)
                  ·
                    refine ⟨3341419903222744110473057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8910453075260650961261485 3341419903222744110473057)
                    ·
                      refine ⟨2506064927417058082854793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3341419903222744110473057 2506064927417058082854793)
                      ·
                        rfl

theorem cell23_4880544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_4880544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880544 prefixEnd_4880544 := by exact prefixLift 4880544
  have htrace : WordTrace (prefixWord ++ tailWord_4880544) baseStart_4880544 baseEnd_4880544 := by
    simpa [prefixWord, tailWord_4880544, baseEnd_4880544] using wordTrace_append hprefix tailTrace_4880544
  have hstable : (prefixWord ++ tailWord_4880544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880544).length < 2 ^ (prefixWord ++ tailWord_4880544).sum := by decide
  have hdescent : baseEnd_4880544 < baseStart_4880544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880554 : List Nat := [3, 1, 5, 1, 2, 1, 1, 3, 1, 5]
def baseStart_4880554 : Nat := 118140960795 + 4880554 * 2 ^ 59
def prefixEnd_4880554 : Nat := 4983230072969 + 3 ^ 40 * 4880554 * 2
def baseEnd_4880554 : Nat := 835356687407867681243249

theorem tailTrace_4880554 : CollatzResearch.WordTrace tailWord_4880554 prefixEnd_4880554 835356687407867681243249 := by
  unfold tailWord_4880554
  simp only [CollatzResearch.WordTrace]
  refine ⟨44502107090148466276854179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118672285573729243404944477 44502107090148466276854179)
  ·
    refine ⟨66753160635222699415281269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44502107090148466276854179 66753160635222699415281269)
    ·
      refine ⟨6258108809552128070182619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66753160635222699415281269 6258108809552128070182619)
      ·
        refine ⟨9387163214328192105273929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6258108809552128070182619 9387163214328192105273929)
        ·
          refine ⟨7040372410746144078955447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9387163214328192105273929 7040372410746144078955447)
          ·
            refine ⟨10560558616119216118433171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7040372410746144078955447 10560558616119216118433171)
            ·
              refine ⟨15840837924178824177649757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10560558616119216118433171 15840837924178824177649757)
              ·
                refine ⟨5940314221567059066618659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15840837924178824177649757 5940314221567059066618659)
                ·
                  refine ⟨8910471332350588599927989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5940314221567059066618659 8910471332350588599927989)
                  ·
                    refine ⟨835356687407867681243249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8910471332350588599927989 835356687407867681243249)
                    ·
                      rfl

theorem cell23_4880554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_4880554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880554 prefixEnd_4880554 := by exact prefixLift 4880554
  have htrace : WordTrace (prefixWord ++ tailWord_4880554) baseStart_4880554 baseEnd_4880554 := by
    simpa [prefixWord, tailWord_4880554, baseEnd_4880554] using wordTrace_append hprefix tailTrace_4880554
  have hstable : (prefixWord ++ tailWord_4880554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880554).length < 2 ^ (prefixWord ++ tailWord_4880554).sum := by decide
  have hdescent : baseEnd_4880554 < baseStart_4880554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880567 : List Nat := [1, 1, 3, 1, 4, 2, 3, 2, 2, 4]
def baseStart_4880567 : Nat := 118140960795 + 4880567 * 2 ^ 59
def prefixEnd_4880567 : Nat := 4983230072969 + 3 ^ 40 * 4880567 * 2
def baseEnd_4880567 : Nat := 835358912490703830955729

theorem tailTrace_4880567 : CollatzResearch.WordTrace tailWord_4880567 prefixEnd_4880567 835358912490703830955729 := by
  unfold tailWord_4880567
  simp only [CollatzResearch.WordTrace]
  refine ⟨178008902509546768327639955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118672601673031178885093303 178008902509546768327639955)
  ·
    refine ⟨267013353764320152491459933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178008902509546768327639955 267013353764320152491459933)
    ·
      refine ⟨100130007661620057184297475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267013353764320152491459933 100130007661620057184297475)
      ·
        refine ⟨150195011492430085776446213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100130007661620057184297475 150195011492430085776446213)
        ·
          refine ⟨28161564654830641083083665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150195011492430085776446213 28161564654830641083083665)
          ·
            refine ⟨21121173491122980812312749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28161564654830641083083665 21121173491122980812312749)
            ·
              refine ⟨7920440059171117804617281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21121173491122980812312749 7920440059171117804617281)
              ·
                refine ⟨5940330044378338353462961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7920440059171117804617281 5940330044378338353462961)
                ·
                  refine ⟨4455247533283753765097221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5940330044378338353462961 4455247533283753765097221)
                  ·
                    refine ⟨835358912490703830955729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4455247533283753765097221 835358912490703830955729)
                    ·
                      rfl

theorem cell23_4880567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 4].length) (baseStart_4880567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880567 prefixEnd_4880567 := by exact prefixLift 4880567
  have htrace : WordTrace (prefixWord ++ tailWord_4880567) baseStart_4880567 baseEnd_4880567 := by
    simpa [prefixWord, tailWord_4880567, baseEnd_4880567] using wordTrace_append hprefix tailTrace_4880567
  have hstable : (prefixWord ++ tailWord_4880567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880567).length < 2 ^ (prefixWord ++ tailWord_4880567).sum := by decide
  have hdescent : baseEnd_4880567 < baseStart_4880567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880573 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 2, 2, 7]
def baseStart_4880573 : Nat := 118140960795 + 4880573 * 2 ^ 59
def prefixEnd_4880573 : Nat := 4983230072969 + 3 ^ 40 * 4880573 * 2
def baseEnd_4880573 : Nat := 2506079818356038469392159

theorem tailTrace_4880573 : CollatzResearch.WordTrace tailWord_4880573 prefixEnd_4880573 2506079818356038469392159 := by
  unfold tailWord_4880573
  simp only [CollatzResearch.WordTrace]
  refine ⟨178009121347525031352358373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118672747565016687568238915 178009121347525031352358373)
  ·
    refine ⟨33376710252660943378567195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178009121347525031352358373 33376710252660943378567195)
    ·
      refine ⟨50065065378991415067850793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33376710252660943378567195 50065065378991415067850793)
      ·
        refine ⟨37548799034243561300888095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50065065378991415067850793 37548799034243561300888095)
        ·
          refine ⟨56323198551365341951332143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37548799034243561300888095 56323198551365341951332143)
          ·
            refine ⟨84484797827048012926998215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56323198551365341951332143 84484797827048012926998215)
            ·
              refine ⟨126727196740572019390497323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84484797827048012926998215 126727196740572019390497323)
              ·
                refine ⟨190090795110858029085745985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126727196740572019390497323 190090795110858029085745985)
                ·
                  refine ⟨142568096333143521814309489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190090795110858029085745985 142568096333143521814309489)
                  ·
                    refine ⟨106926072249857641360732117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 142568096333143521814309489 106926072249857641360732117)
                    ·
                      refine ⟨2506079818356038469392159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 106926072249857641360732117 2506079818356038469392159)
                      ·
                        rfl

theorem cell23_4880573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_4880573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880573 prefixEnd_4880573 := by exact prefixLift 4880573
  have htrace : WordTrace (prefixWord ++ tailWord_4880573) baseStart_4880573 baseEnd_4880573 := by
    simpa [prefixWord, tailWord_4880573, baseEnd_4880573] using wordTrace_append hprefix tailTrace_4880573
  have hstable : (prefixWord ++ tailWord_4880573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880573).length < 2 ^ (prefixWord ++ tailWord_4880573).sum := by decide
  have hdescent : baseEnd_4880573 < baseStart_4880573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880593 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 2, 7]
def baseStart_4880593 : Nat := 118140960795 + 4880593 * 2 ^ 59
def prefixEnd_4880593 : Nat := 4983230072969 + 3 ^ 40 * 4880593 * 2
def baseEnd_4880593 : Nat := 835363362656376130380689

theorem tailTrace_4880593 : CollatzResearch.WordTrace tailWord_4880593 prefixEnd_4880593 835363362656376130380689 := by
  unfold tailWord_4880593
  simp only [CollatzResearch.WordTrace]
  refine ⟨178009850807452574768086433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118673233871635049845390955 178009850807452574768086433)
  ·
    refine ⟨133507388105589431076064825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178009850807452574768086433 133507388105589431076064825)
    ·
      refine ⟨100130541079192073307048619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133507388105589431076064825 100130541079192073307048619)
      ·
        refine ⟨150195811618788109960572929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100130541079192073307048619 150195811618788109960572929)
        ·
          refine ⟨112646858714091082470429697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150195811618788109960572929 112646858714091082470429697)
          ·
            refine ⟨84485144035568311852822273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112646858714091082470429697 84485144035568311852822273)
            ·
              refine ⟨63363858026676233889616705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84485144035568311852822273 63363858026676233889616705)
              ·
                refine ⟨47522893520007175417212529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63363858026676233889616705 47522893520007175417212529)
                ·
                  refine ⟨35642170140005381562909397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47522893520007175417212529 35642170140005381562909397)
                  ·
                    refine ⟨835363362656376130380689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35642170140005381562909397 835363362656376130380689)
                    ·
                      rfl

theorem cell23_4880593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_4880593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880593 prefixEnd_4880593 := by exact prefixLift 4880593
  have htrace : WordTrace (prefixWord ++ tailWord_4880593) baseStart_4880593 baseEnd_4880593 := by
    simpa [prefixWord, tailWord_4880593, baseEnd_4880593] using wordTrace_append hprefix tailTrace_4880593
  have hstable : (prefixWord ++ tailWord_4880593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880593).length < 2 ^ (prefixWord ++ tailWord_4880593).sum := by decide
  have hdescent : baseEnd_4880593 < baseStart_4880593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880594 : List Nat := [3, 2, 2, 2, 1, 3, 2, 2, 1, 2, 3]
def baseStart_4880594 : Nat := 118140960795 + 4880594 * 2 ^ 59
def prefixEnd_4880594 : Nat := 4983230072969 + 3 ^ 40 * 4880594 * 2
def baseEnd_4880594 : Nat := 2506090601449782887229563

theorem tailTrace_4880594 : CollatzResearch.WordTrace tailWord_4880594 prefixEnd_4880594 2506090601449782887229563 := by
  unfold tailWord_4880594
  simp only [CollatzResearch.WordTrace]
  refine ⟨44502471820112237984718209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118673258186965967959248557 44502471820112237984718209)
  ·
    refine ⟨33376853865084178488538657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44502471820112237984718209 33376853865084178488538657)
    ·
      refine ⟨25032640398813133866403993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33376853865084178488538657 25032640398813133866403993)
      ·
        refine ⟨18774480299109850399802995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25032640398813133866403993 18774480299109850399802995)
        ·
          refine ⟨28161720448664775599704493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18774480299109850399802995 28161720448664775599704493)
          ·
            refine ⟨10560645168249290849889185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28161720448664775599704493 10560645168249290849889185)
            ·
              refine ⟨7920483876186968137416889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10560645168249290849889185 7920483876186968137416889)
              ·
                refine ⟨5940362907140226103062667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7920483876186968137416889 5940362907140226103062667)
                ·
                  refine ⟨8910544360710339154594001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5940362907140226103062667 8910544360710339154594001)
                  ·
                    refine ⟨6682908270532754365945501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8910544360710339154594001 6682908270532754365945501)
                    ·
                      refine ⟨2506090601449782887229563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6682908270532754365945501 2506090601449782887229563)
                      ·
                        rfl

theorem cell23_4880594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_4880594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880594 prefixEnd_4880594 := by exact prefixLift 4880594
  have htrace : WordTrace (prefixWord ++ tailWord_4880594) baseStart_4880594 baseEnd_4880594 := by
    simpa [prefixWord, tailWord_4880594, baseEnd_4880594] using wordTrace_append hprefix tailTrace_4880594
  have hstable : (prefixWord ++ tailWord_4880594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880594).length < 2 ^ (prefixWord ++ tailWord_4880594).sum := by decide
  have hdescent : baseEnd_4880594 < baseStart_4880594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880603 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 5]
def baseStart_4880603 : Nat := 118140960795 + 4880603 * 2 ^ 59
def prefixEnd_4880603 : Nat := 4983230072969 + 3 ^ 40 * 4880603 * 2
def baseEnd_4880603 : Nat := 2506095222775673352017021

theorem tailTrace_4880603 : CollatzResearch.WordTrace tailWord_4880603 prefixEnd_4880603 2506095222775673352017021 := by
  unfold tailWord_4880603
  simp only [CollatzResearch.WordTrace]
  refine ⟨178010215537416346475950463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118673477024944230983966975 178010215537416346475950463)
  ·
    refine ⟨267015323306124519713925695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178010215537416346475950463 267015323306124519713925695)
    ·
      refine ⟨400522984959186779570888543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267015323306124519713925695 400522984959186779570888543)
      ·
        refine ⟨600784477438780169356332815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400522984959186779570888543 600784477438780169356332815)
        ·
          refine ⟨901176716158170254034499223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600784477438780169356332815 901176716158170254034499223)
          ·
            refine ⟨1351765074237255381051748835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901176716158170254034499223 1351765074237255381051748835)
            ·
              refine ⟨2027647611355883071577623253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1351765074237255381051748835 2027647611355883071577623253)
              ·
                refine ⟨47522990891153509490100545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2027647611355883071577623253 47522990891153509490100545)
                ·
                  refine ⟨35642243168365132117575409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47522990891153509490100545 35642243168365132117575409)
                  ·
                    refine ⟨26731682376273849088181557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35642243168365132117575409 26731682376273849088181557)
                    ·
                      refine ⟨2506095222775673352017021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26731682376273849088181557 2506095222775673352017021)
                      ·
                        rfl

theorem cell23_4880603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 5].length) (baseStart_4880603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880603 prefixEnd_4880603 := by exact prefixLift 4880603
  have htrace : WordTrace (prefixWord ++ tailWord_4880603) baseStart_4880603 baseEnd_4880603 := by
    simpa [prefixWord, tailWord_4880603, baseEnd_4880603] using wordTrace_append hprefix tailTrace_4880603
  have hstable : (prefixWord ++ tailWord_4880603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880603).length < 2 ^ (prefixWord ++ tailWord_4880603).sum := by decide
  have hdescent : baseEnd_4880603 < baseStart_4880603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880650 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5]
def baseStart_4880650 : Nat := 118140960795 + 4880650 * 2 ^ 59
def prefixEnd_4880650 : Nat := 4983230072969 + 3 ^ 40 * 4880650 * 2
def baseEnd_4880650 : Nat := 2506119356366434668129305

theorem tailTrace_4880650 : CollatzResearch.WordTrace tailWord_4880650 prefixEnd_4880650 2506119356366434668129305 := by
  unfold tailWord_4880650
  simp only [CollatzResearch.WordTrace]
  refine ⟨44502982442061518375727851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118674619845497382335274269 44502982442061518375727851)
  ·
    refine ⟨66754473663092277563591777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44502982442061518375727851 66754473663092277563591777)
    ·
      refine ⟨50065855247319208172693833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66754473663092277563591777 50065855247319208172693833)
      ·
        refine ⟨37549391435489406129520375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50065855247319208172693833 37549391435489406129520375)
        ·
          refine ⟨56324087153234109194280563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37549391435489406129520375 56324087153234109194280563)
          ·
            refine ⟨84486130729851163791420845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56324087153234109194280563 84486130729851163791420845)
            ·
              refine ⟨31682299023694186421782817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84486130729851163791420845 31682299023694186421782817)
              ·
                refine ⟨23761724267770639816337113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31682299023694186421782817 23761724267770639816337113)
                ·
                  refine ⟨17821293200827979862252835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23761724267770639816337113 17821293200827979862252835)
                  ·
                    refine ⟨26731939801241969793379253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17821293200827979862252835 26731939801241969793379253)
                    ·
                      refine ⟨2506119356366434668129305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26731939801241969793379253 2506119356366434668129305)
                      ·
                        rfl

theorem cell23_4880650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_4880650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880650 prefixEnd_4880650 := by exact prefixLift 4880650
  have htrace : WordTrace (prefixWord ++ tailWord_4880650) baseStart_4880650 baseEnd_4880650 := by
    simpa [prefixWord, tailWord_4880650, baseEnd_4880650] using wordTrace_append hprefix tailTrace_4880650
  have hstable : (prefixWord ++ tailWord_4880650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880650).length < 2 ^ (prefixWord ++ tailWord_4880650).sum := by decide
  have hdescent : baseEnd_4880650 < baseStart_4880650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880697 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 1, 5, 3]
def baseStart_4880697 : Nat := 118140960795 + 4880697 * 2 ^ 59
def prefixEnd_4880697 : Nat := 4983230072969 + 3 ^ 40 * 4880697 * 2
def baseEnd_4880697 : Nat := 2506143489957195984241589

theorem tailTrace_4880697 : CollatzResearch.WordTrace tailWord_4880697 prefixEnd_4880697 2506143489957195984241589 := by
  unfold tailWord_4880697
  simp only [CollatzResearch.WordTrace]
  refine ⟨178013643999075800529872345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118675762666050533686581563 178013643999075800529872345)
  ·
    refine ⟨133510232999306850397404259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178013643999075800529872345 133510232999306850397404259)
    ·
      refine ⟨200265349498960275596106389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133510232999306850397404259 200265349498960275596106389)
      ·
        refine ⟨9387438257763762918567487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 200265349498960275596106389 9387438257763762918567487)
        ·
          refine ⟨14081157386645644377851231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9387438257763762918567487 14081157386645644377851231)
          ·
            refine ⟨21121736079968466566776847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14081157386645644377851231 21121736079968466566776847)
            ·
              refine ⟨31682604119952699850165271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21121736079968466566776847 31682604119952699850165271)
              ·
                refine ⟨47523906179929049775247907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31682604119952699850165271 47523906179929049775247907)
                ·
                  refine ⟨71285859269893574662871861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47523906179929049775247907 71285859269893574662871861)
                  ·
                    refine ⟨6683049306552522624644237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71285859269893574662871861 6683049306552522624644237)
                    ·
                      refine ⟨2506143489957195984241589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6683049306552522624644237 2506143489957195984241589)
                      ·
                        rfl

theorem cell23_4880697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_4880697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880697 prefixEnd_4880697 := by exact prefixLift 4880697
  have htrace : WordTrace (prefixWord ++ tailWord_4880697) baseStart_4880697 baseEnd_4880697 := by
    simpa [prefixWord, tailWord_4880697, baseEnd_4880697] using wordTrace_append hprefix tailTrace_4880697
  have hstable : (prefixWord ++ tailWord_4880697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880697).length < 2 ^ (prefixWord ++ tailWord_4880697).sum := by decide
  have hdescent : baseEnd_4880697 < baseStart_4880697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880700 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 1, 7]
def baseStart_4880700 : Nat := 118140960795 + 4880700 * 2 ^ 59
def prefixEnd_4880700 : Nat := 4983230072969 + 3 ^ 40 * 4880700 * 2
def baseEnd_4880700 : Nat := 835381676799719824168025

theorem tailTrace_4880700 : CollatzResearch.WordTrace tailWord_4880700 prefixEnd_4880700 835381676799719824168025 := by
  unfold tailWord_4880700
  simp only [CollatzResearch.WordTrace]
  refine ⟨89006876709032466021115777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118675835612043288028154369 89006876709032466021115777)
  ·
    refine ⟨66755157531774349515836833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89006876709032466021115777 66755157531774349515836833)
    ·
      refine ⟨50066368148830762136877625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66755157531774349515836833 50066368148830762136877625)
      ·
        refine ⟨37549776111623071602658219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50066368148830762136877625 37549776111623071602658219)
        ·
          refine ⟨56324664167434607403987329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37549776111623071602658219 56324664167434607403987329)
          ·
            refine ⟨42243498125575955552990497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56324664167434607403987329 42243498125575955552990497)
            ·
              refine ⟨31682623594181966664742873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42243498125575955552990497 31682623594181966664742873)
              ·
                refine ⟨23761967695636474998557155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31682623594181966664742873 23761967695636474998557155)
                ·
                  refine ⟨35642951543454712497835733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23761967695636474998557155 35642951543454712497835733)
                  ·
                    refine ⟨835381676799719824168025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35642951543454712497835733 835381676799719824168025)
                    ·
                      rfl

theorem cell23_4880700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_4880700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880700 prefixEnd_4880700 := by exact prefixLift 4880700
  have htrace : WordTrace (prefixWord ++ tailWord_4880700) baseStart_4880700 baseEnd_4880700 := by
    simpa [prefixWord, tailWord_4880700, baseEnd_4880700] using wordTrace_append hprefix tailTrace_4880700
  have hstable : (prefixWord ++ tailWord_4880700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880700).length < 2 ^ (prefixWord ++ tailWord_4880700).sum := by decide
  have hdescent : baseEnd_4880700 < baseStart_4880700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880732 : List Nat := [2, 2, 4, 3, 2, 1, 1, 2, 2, 2, 2]
def baseStart_4880732 : Nat := 118140960795 + 4880732 * 2 ^ 59
def prefixEnd_4880732 : Nat := 4983230072969 + 3 ^ 40 * 4880732 * 2
def baseEnd_4880732 : Nat := 2506161461780103347303929

theorem tailTrace_4880732 : CollatzResearch.WordTrace tailWord_4880732 prefixEnd_4880732 2506161461780103347303929 := by
  unfold tailWord_4880732
  simp only [CollatzResearch.WordTrace]
  refine ⟨89007460276974500753698225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118676613702632667671597633 89007460276974500753698225)
  ·
    refine ⟨66755595207730875565273669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89007460276974500753698225 66755595207730875565273669)
    ·
      refine ⟨12516674101449539168488813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66755595207730875565273669 12516674101449539168488813)
      ·
        refine ⟨4693752788043577188183305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12516674101449539168488813 4693752788043577188183305)
        ·
          refine ⟨3520314591032682891137479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4693752788043577188183305 3520314591032682891137479)
          ·
            refine ⟨5280471886549024336706219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3520314591032682891137479 5280471886549024336706219)
            ·
              refine ⟨7920707829823536505059329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5280471886549024336706219 7920707829823536505059329)
              ·
                refine ⟨5940530872367652378794497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7920707829823536505059329 5940530872367652378794497)
                ·
                  refine ⟨4455398154275739284095873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5940530872367652378794497 4455398154275739284095873)
                  ·
                    refine ⟨3341548615706804463071905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4455398154275739284095873 3341548615706804463071905)
                    ·
                      refine ⟨2506161461780103347303929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3341548615706804463071905 2506161461780103347303929)
                      ·
                        rfl

theorem cell23_4880732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_4880732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880732 prefixEnd_4880732 := by exact prefixLift 4880732
  have htrace : WordTrace (prefixWord ++ tailWord_4880732) baseStart_4880732 baseEnd_4880732 := by
    simpa [prefixWord, tailWord_4880732, baseEnd_4880732] using wordTrace_append hprefix tailTrace_4880732
  have hstable : (prefixWord ++ tailWord_4880732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880732).length < 2 ^ (prefixWord ++ tailWord_4880732).sum := by decide
  have hdescent : baseEnd_4880732 < baseStart_4880732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880754 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 2, 4, 2]
def baseStart_4880754 : Nat := 118140960795 + 4880754 * 2 ^ 59
def prefixEnd_4880754 : Nat := 4983230072969 + 3 ^ 40 * 4880754 * 2
def baseEnd_4880754 : Nat := 2506172758354502261228827

theorem tailTrace_4880754 : CollatzResearch.WordTrace tailWord_4880754 prefixEnd_4880754 2506172758354502261228827 := by
  unfold tailWord_4880754
  simp only [CollatzResearch.WordTrace]
  refine ⟨44503930739967324816174329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118677148639912866176464877 44503930739967324816174329)
  ·
    refine ⟨33377948054975493612130747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44503930739967324816174329 33377948054975493612130747)
    ·
      refine ⟨50066922082463240418196121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33377948054975493612130747 50066922082463240418196121)
      ·
        refine ⟨37550191561847430313647091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50066922082463240418196121 37550191561847430313647091)
        ·
          refine ⟨56325287342771145470470637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37550191561847430313647091 56325287342771145470470637)
          ·
            refine ⟨21121982753539179551426489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56325287342771145470470637 21121982753539179551426489)
            ·
              refine ⟨15841487065154384663569867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21121982753539179551426489 15841487065154384663569867)
              ·
                refine ⟨23762230597731576995354801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15841487065154384663569867 23762230597731576995354801)
                ·
                  refine ⟨17821672948298682746516101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23762230597731576995354801 17821672948298682746516101)
                  ·
                    refine ⟨3341563677806003014971769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17821672948298682746516101 3341563677806003014971769)
                    ·
                      refine ⟨2506172758354502261228827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3341563677806003014971769 2506172758354502261228827)
                      ·
                        rfl

theorem cell23_4880754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_4880754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880754 prefixEnd_4880754 := by exact prefixLift 4880754
  have htrace : WordTrace (prefixWord ++ tailWord_4880754) baseStart_4880754 baseEnd_4880754 := by
    simpa [prefixWord, tailWord_4880754, baseEnd_4880754] using wordTrace_append hprefix tailTrace_4880754
  have hstable : (prefixWord ++ tailWord_4880754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880754).length < 2 ^ (prefixWord ++ tailWord_4880754).sum := by decide
  have hdescent : baseEnd_4880754 < baseStart_4880754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880798 : List Nat := [4, 3, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_4880798 : Nat := 118140960795 + 4880798 * 2 ^ 59
def prefixEnd_4880798 : Nat := 4983230072969 + 3 ^ 40 * 4880798 * 2
def baseEnd_4880798 : Nat := 835398450501100029692875

theorem tailTrace_4880798 : CollatzResearch.WordTrace tailWord_4880798 prefixEnd_4880798 835398450501100029692875 := by
  unfold tailWord_4880798
  simp only [CollatzResearch.WordTrace]
  refine ⟨22252165971463736847412381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118678218514473263186199365 22252165971463736847412381)
  ·
    refine ⟨8344562239298901317779643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22252165971463736847412381 8344562239298901317779643)
    ·
      refine ⟨12516843358948351976669465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8344562239298901317779643 12516843358948351976669465)
      ·
        refine ⟨9387632519211263982502099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12516843358948351976669465 9387632519211263982502099)
        ·
          refine ⟨14081448778816895973753149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9387632519211263982502099 14081448778816895973753149)
          ·
            refine ⟨5280543292056335990157431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14081448778816895973753149 5280543292056335990157431)
            ·
              refine ⟨7920814938084503985236147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5280543292056335990157431 7920814938084503985236147)
              ·
                refine ⟨11881222407126755977854221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7920814938084503985236147 11881222407126755977854221)
                ·
                  refine ⟨4455458402672533491695333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11881222407126755977854221 4455458402672533491695333)
                  ·
                    refine ⟨835398450501100029692875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4455458402672533491695333 835398450501100029692875)
                    ·
                      rfl

theorem cell23_4880798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_4880798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880798 prefixEnd_4880798 := by exact prefixLift 4880798
  have htrace : WordTrace (prefixWord ++ tailWord_4880798) baseStart_4880798 baseEnd_4880798 := by
    simpa [prefixWord, tailWord_4880798, baseEnd_4880798] using wordTrace_append hprefix tailTrace_4880798
  have hstable : (prefixWord ++ tailWord_4880798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880798).length < 2 ^ (prefixWord ++ tailWord_4880798).sum := by decide
  have hdescent : baseEnd_4880798 < baseStart_4880798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880854 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_4880854 : Nat := 118140960795 + 4880854 * 2 ^ 59
def prefixEnd_4880854 : Nat := 4983230072969 + 3 ^ 40 * 4880854 * 2
def baseEnd_4880854 : Nat := 835408035473317289992789

theorem tailTrace_4880854 : CollatzResearch.WordTrace tailWord_4880854 prefixEnd_4880854 835408035473317289992789 := by
  unfold tailWord_4880854
  simp only [CollatzResearch.WordTrace]
  refine ⟨11126210641219188521458601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118679580173004677562225077 11126210641219188521458601)
  ·
    refine ⟨8344657980914391391093951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11126210641219188521458601 8344657980914391391093951)
    ·
      refine ⟨12516986971371587086640927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8344657980914391391093951 12516986971371587086640927)
      ·
        refine ⟨18775480457057380629961391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12516986971371587086640927 18775480457057380629961391)
        ·
          refine ⟨28163220685586070944942087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18775480457057380629961391 28163220685586070944942087)
          ·
            refine ⟨42244831028379106417413131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28163220685586070944942087 42244831028379106417413131)
            ·
              refine ⟨63367246542568659626119697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42244831028379106417413131 63367246542568659626119697)
              ·
                refine ⟨47525434906926494719589773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63367246542568659626119697 47525434906926494719589773)
                ·
                  refine ⟨17822038090097435519846165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47525434906926494719589773 17822038090097435519846165)
                  ·
                    refine ⟨835408035473317289992789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17822038090097435519846165 835408035473317289992789)
                    ·
                      rfl

theorem cell23_4880854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_4880854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880854 prefixEnd_4880854 := by exact prefixLift 4880854
  have htrace : WordTrace (prefixWord ++ tailWord_4880854) baseStart_4880854 baseEnd_4880854 := by
    simpa [prefixWord, tailWord_4880854, baseEnd_4880854] using wordTrace_append hprefix tailTrace_4880854
  have hstable : (prefixWord ++ tailWord_4880854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880854).length < 2 ^ (prefixWord ++ tailWord_4880854).sum := by decide
  have hdescent : baseEnd_4880854 < baseStart_4880854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880857 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 3, 2, 4]
def baseStart_4880857 : Nat := 118140960795 + 4880857 * 2 ^ 59
def prefixEnd_4880857 : Nat := 4983230072969 + 3 ^ 40 * 4880857 * 2
def baseEnd_4880857 : Nat := 2506225646861915358240853

theorem tailTrace_4880857 : CollatzResearch.WordTrace tailWord_4880857 prefixEnd_4880857 2506225646861915358240853 := by
  unfold tailWord_4880857
  simp only [CollatzResearch.WordTrace]
  refine ⟨178019479678496147855696825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118679653118997431903797883 178019479678496147855696825)
  ·
    refine ⟨133514609758872110891772619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178019479678496147855696825 133514609758872110891772619)
    ·
      refine ⟨200271914638308166337658929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133514609758872110891772619 200271914638308166337658929)
      ·
        refine ⟨150203935978731124753244197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200271914638308166337658929 150203935978731124753244197)
        ·
          refine ⟨28163237996012085891233287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150203935978731124753244197 28163237996012085891233287)
          ·
            refine ⟨42244856994018128836849931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28163237996012085891233287 42244856994018128836849931)
            ·
              refine ⟨63367285491027193255274897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42244856994018128836849931 63367285491027193255274897)
              ·
                refine ⟨47525464118270394941456173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63367285491027193255274897 47525464118270394941456173)
                ·
                  refine ⟨17822049044351398103046065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47525464118270394941456173 17822049044351398103046065)
                  ·
                    refine ⟨13366536783263548577284549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17822049044351398103046065 13366536783263548577284549)
                    ·
                      refine ⟨2506225646861915358240853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13366536783263548577284549 2506225646861915358240853)
                      ·
                        rfl

theorem cell23_4880857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_4880857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880857 prefixEnd_4880857 := by exact prefixLift 4880857
  have htrace : WordTrace (prefixWord ++ tailWord_4880857) baseStart_4880857 baseEnd_4880857 := by
    simpa [prefixWord, tailWord_4880857, baseEnd_4880857] using wordTrace_append hprefix tailTrace_4880857
  have hstable : (prefixWord ++ tailWord_4880857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880857).length < 2 ^ (prefixWord ++ tailWord_4880857).sum := by decide
  have hdescent : baseEnd_4880857 < baseStart_4880857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880874 : List Nat := [3, 1, 3, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_4880874 : Nat := 118140960795 + 4880874 * 2 ^ 59
def prefixEnd_4880874 : Nat := 4983230072969 + 3 ^ 40 * 4880874 * 2
def baseEnd_4880874 : Nat := 2506234376033041791728275

theorem tailTrace_4880874 : CollatzResearch.WordTrace tailWord_4880874 prefixEnd_4880874 2506234376033041791728275 := by
  unfold tailWord_4880874
  simp only [CollatzResearch.WordTrace]
  refine ⟨44505024929858639939766419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118680066479623039839377117 44505024929858639939766419)
  ·
    refine ⟨66757537394787959909649629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44505024929858639939766419 66757537394787959909649629)
    ·
      refine ⟨25034076523045484966118611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66757537394787959909649629 25034076523045484966118611)
      ·
        refine ⟨37551114784568227449177917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25034076523045484966118611 37551114784568227449177917)
        ·
          refine ⟨14081668044213085293441719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37551114784568227449177917 14081668044213085293441719)
          ·
            refine ⟨21122502066319627940162579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14081668044213085293441719 21122502066319627940162579)
            ·
              refine ⟨31683753099479441910243869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21122502066319627940162579 31683753099479441910243869)
              ·
                refine ⟨11881407412304790716341451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31683753099479441910243869 11881407412304790716341451)
                ·
                  refine ⟨17822111118457186074512177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11881407412304790716341451 17822111118457186074512177)
                  ·
                    refine ⟨13366583338842889555884133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17822111118457186074512177 13366583338842889555884133)
                    ·
                      refine ⟨2506234376033041791728275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13366583338842889555884133 2506234376033041791728275)
                      ·
                        rfl

theorem cell23_4880874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_4880874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880874 prefixEnd_4880874 := by exact prefixLift 4880874
  have htrace : WordTrace (prefixWord ++ tailWord_4880874) baseStart_4880874 baseEnd_4880874 := by
    simpa [prefixWord, tailWord_4880874, baseEnd_4880874] using wordTrace_append hprefix tailTrace_4880874
  have hstable : (prefixWord ++ tailWord_4880874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880874).length < 2 ^ (prefixWord ++ tailWord_4880874).sum := by decide
  have hdescent : baseEnd_4880874 < baseStart_4880874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880878 : List Nat := [4, 1, 2, 1, 2, 3, 1, 2, 3, 2, 2]
def baseStart_4880878 : Nat := 118140960795 + 4880878 * 2 ^ 59
def prefixEnd_4880878 : Nat := 4983230072969 + 3 ^ 40 * 4880878 * 2
def baseEnd_4880878 : Nat := 2506236429955659776078257

theorem tailTrace_4880878 : CollatzResearch.WordTrace tailWord_4880878 prefixEnd_4880878 2506236429955659776078257 := by
  unfold tailWord_4880878
  simp only [CollatzResearch.WordTrace]
  refine ⟨22252530701427508555276411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118680163740946712294807525 22252530701427508555276411)
  ·
    refine ⟨33378796052141262832914617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22252530701427508555276411 33378796052141262832914617)
    ·
      refine ⟨25034097039105947124685963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33378796052141262832914617 25034097039105947124685963)
      ·
        refine ⟨37551145558658920687028945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25034097039105947124685963 37551145558658920687028945)
        ·
          refine ⟨28163359168994190515271709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37551145558658920687028945 28163359168994190515271709)
          ·
            refine ⟨10561259688372821443226891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28163359168994190515271709 10561259688372821443226891)
            ·
              refine ⟨15841889532559232164840337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10561259688372821443226891 15841889532559232164840337)
              ·
                refine ⟨11881417149419424123630253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15841889532559232164840337 11881417149419424123630253)
                ·
                  refine ⟨4455531431032284046361345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11881417149419424123630253 4455531431032284046361345)
                  ·
                    refine ⟨3341648573274213034771009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4455531431032284046361345 3341648573274213034771009)
                    ·
                      refine ⟨2506236429955659776078257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3341648573274213034771009 2506236429955659776078257)
                      ·
                        rfl

theorem cell23_4880878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_4880878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880878 prefixEnd_4880878 := by exact prefixLift 4880878
  have htrace : WordTrace (prefixWord ++ tailWord_4880878) baseStart_4880878 baseEnd_4880878 := by
    simpa [prefixWord, tailWord_4880878, baseEnd_4880878] using wordTrace_append hprefix tailTrace_4880878
  have hstable : (prefixWord ++ tailWord_4880878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880878).length < 2 ^ (prefixWord ++ tailWord_4880878).sum := by decide
  have hdescent : baseEnd_4880878 < baseStart_4880878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880928 : List Nat := [2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 3]
def baseStart_4880928 : Nat := 118140960795 + 4880928 * 2 ^ 59
def prefixEnd_4880928 : Nat := 4983230072969 + 3 ^ 40 * 4880928 * 2
def baseEnd_4880928 : Nat := 2506262103988384580453027

theorem tailTrace_4880928 : CollatzResearch.WordTrace tailWord_4880928 prefixEnd_4880928 2506262103988384580453027 := by
  unfold tailWord_4880928
  simp only [CollatzResearch.WordTrace]
  refine ⟨89011034630619463490765719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118681379507492617987687625 89011034630619463490765719)
  ·
    refine ⟨133516551945929195236148579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89011034630619463490765719 133516551945929195236148579)
    ·
      refine ⟨200274827918893792854222869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133516551945929195236148579 200274827918893792854222869)
      ·
        refine ⟨9387882558698146540041697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 200274827918893792854222869 9387882558698146540041697)
        ·
          refine ⟨7040911919023609905031273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9387882558698146540041697 7040911919023609905031273)
          ·
            refine ⟨5280683939267707428773455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7040911919023609905031273 5280683939267707428773455)
            ·
              refine ⟨7921025908901561143160183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5280683939267707428773455 7921025908901561143160183)
              ·
                refine ⟨11881538863352341714740275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7921025908901561143160183 11881538863352341714740275)
                ·
                  refine ⟨17822308295028512572110413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11881538863352341714740275 17822308295028512572110413)
                  ·
                    refine ⟨6683365610635692214541405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17822308295028512572110413 6683365610635692214541405)
                    ·
                      refine ⟨2506262103988384580453027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6683365610635692214541405 2506262103988384580453027)
                      ·
                        rfl

theorem cell23_4880928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_4880928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880928 prefixEnd_4880928 := by exact prefixLift 4880928
  have htrace : WordTrace (prefixWord ++ tailWord_4880928) baseStart_4880928 baseEnd_4880928 := by
    simpa [prefixWord, tailWord_4880928, baseEnd_4880928] using wordTrace_append hprefix tailTrace_4880928
  have hstable : (prefixWord ++ tailWord_4880928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880928).length < 2 ^ (prefixWord ++ tailWord_4880928).sum := by decide
  have hdescent : baseEnd_4880928 < baseStart_4880928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880935 : List Nat := [1, 1, 7, 2, 2, 1, 2, 7]
def baseStart_4880935 : Nat := 118140960795 + 4880935 * 2 ^ 59
def prefixEnd_4880935 : Nat := 4983230072969 + 3 ^ 40 * 4880935 * 2
def baseEnd_4880935 : Nat := 92824655494554298261685

theorem tailTrace_4880935 : CollatzResearch.WordTrace tailWord_4880935 prefixEnd_4880935 92824655494554298261685 := by
  unfold tailWord_4880935
  simp only [CollatzResearch.WordTrace]
  refine ⟨178022324572213567177036259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118681549714809044784690839 178022324572213567177036259)
  ·
    refine ⟨267033486858320350765554389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178022324572213567177036259 267033486858320350765554389)
    ·
      refine ⟨6258597348241883221067681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 267033486858320350765554389 6258597348241883221067681)
      ·
        refine ⟨4693948011181412415800761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6258597348241883221067681 4693948011181412415800761)
        ·
          refine ⟨3520461008386059311850571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4693948011181412415800761 3520461008386059311850571)
          ·
            refine ⟨5280691512579088967775857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3520461008386059311850571 5280691512579088967775857)
            ·
              refine ⟨3960518634434316725831893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5280691512579088967775857 3960518634434316725831893)
              ·
                refine ⟨92824655494554298261685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3960518634434316725831893 92824655494554298261685)
                ·
                  rfl

theorem cell23_4880935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 7].length) (baseStart_4880935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880935 prefixEnd_4880935 := by exact prefixLift 4880935
  have htrace : WordTrace (prefixWord ++ tailWord_4880935) baseStart_4880935 baseEnd_4880935 := by
    simpa [prefixWord, tailWord_4880935, baseEnd_4880935] using wordTrace_append hprefix tailTrace_4880935
  have hstable : (prefixWord ++ tailWord_4880935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880935).length < 2 ^ (prefixWord ++ tailWord_4880935).sum := by decide
  have hdescent : baseEnd_4880935 < baseStart_4880935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880938 : List Nat := [3, 1, 4, 1, 1, 2, 1, 4, 1, 3, 2]
def baseStart_4880938 : Nat := 118140960795 + 4880938 * 2 ^ 59
def prefixEnd_4880938 : Nat := 4983230072969 + 3 ^ 40 * 4880938 * 2
def baseEnd_4880938 : Nat := 2506267238794929541327981

theorem tailTrace_4880938 : CollatzResearch.WordTrace tailWord_4880938 prefixEnd_4880938 2506267238794929541327981 := by
  unfold tailWord_4880938
  simp only [CollatzResearch.WordTrace]
  refine ⟨44505608497800674672348867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118681622660801799126263645 44505608497800674672348867)
  ·
    refine ⟨66758412746701012008523301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44505608497800674672348867 66758412746701012008523301)
    ·
      refine ⟨12517202390006439751598119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66758412746701012008523301 12517202390006439751598119)
      ·
        refine ⟨18775803585009659627397179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12517202390006439751598119 18775803585009659627397179)
        ·
          refine ⟨28163705377514489441095769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18775803585009659627397179 28163705377514489441095769)
          ·
            refine ⟨21122779033135867080821827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28163705377514489441095769 21122779033135867080821827)
            ·
              refine ⟨31684168549703800621232741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21122779033135867080821827 31684168549703800621232741)
              ·
                refine ⟨5940781603069462616481139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31684168549703800621232741 5940781603069462616481139)
                ·
                  refine ⟨8911172404604193924721709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5940781603069462616481139 8911172404604193924721709)
                  ·
                    refine ⟨3341689651726572721770641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8911172404604193924721709 3341689651726572721770641)
                    ·
                      refine ⟨2506267238794929541327981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3341689651726572721770641 2506267238794929541327981)
                      ·
                        rfl

theorem cell23_4880938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_4880938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880938 prefixEnd_4880938 := by exact prefixLift 4880938
  have htrace : WordTrace (prefixWord ++ tailWord_4880938) baseStart_4880938 baseEnd_4880938 := by
    simpa [prefixWord, tailWord_4880938, baseEnd_4880938] using wordTrace_append hprefix tailTrace_4880938
  have hstable : (prefixWord ++ tailWord_4880938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880938).length < 2 ^ (prefixWord ++ tailWord_4880938).sum := by decide
  have hdescent : baseEnd_4880938 < baseStart_4880938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880951 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 6, 2, 2]
def baseStart_4880951 : Nat := 118140960795 + 4880951 * 2 ^ 59
def prefixEnd_4880951 : Nat := 4983230072969 + 3 ^ 40 * 4880951 * 2
def baseEnd_4880951 : Nat := 2506273914043437990465421

theorem tailTrace_4880951 : CollatzResearch.WordTrace tailWord_4880951 prefixEnd_4880951 2506273914043437990465421 := by
  unfold tailWord_4880951
  simp only [CollatzResearch.WordTrace]
  refine ⟨178022908140155601909618707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118681938760103734606412471 178022908140155601909618707)
  ·
    refine ⟨267034362210233402864428061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178022908140155601909618707 267034362210233402864428061)
    ·
      refine ⟨100137885828837526074160523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267034362210233402864428061 100137885828837526074160523)
      ·
        refine ⟨150206828743256289111240785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100137885828837526074160523 150206828743256289111240785)
        ·
          refine ⟨112655121557442216833430589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150206828743256289111240785 112655121557442216833430589)
          ·
            refine ⟨42245670584040831312536471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112655121557442216833430589 42245670584040831312536471)
            ·
              refine ⟨63368505876061246968804707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42245670584040831312536471 63368505876061246968804707)
              ·
                refine ⟨95052758814091870453207061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63368505876061246968804707 95052758814091870453207061)
                ·
                  refine ⟨4455598069410556427494081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 95052758814091870453207061 4455598069410556427494081)
                  ·
                    refine ⟨3341698552057917320620561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4455598069410556427494081 3341698552057917320620561)
                    ·
                      refine ⟨2506273914043437990465421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3341698552057917320620561 2506273914043437990465421)
                      ·
                        rfl

theorem cell23_4880951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 2, 2].length) (baseStart_4880951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880951 prefixEnd_4880951 := by exact prefixLift 4880951
  have htrace : WordTrace (prefixWord ++ tailWord_4880951) baseStart_4880951 baseEnd_4880951 := by
    simpa [prefixWord, tailWord_4880951, baseEnd_4880951] using wordTrace_append hprefix tailTrace_4880951
  have hstable : (prefixWord ++ tailWord_4880951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880951).length < 2 ^ (prefixWord ++ tailWord_4880951).sum := by decide
  have hdescent : baseEnd_4880951 < baseStart_4880951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880954 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5]
def baseStart_4880954 : Nat := 118140960795 + 4880954 * 2 ^ 59
def prefixEnd_4880954 : Nat := 4983230072969 + 3 ^ 40 * 4880954 * 2
def baseEnd_4880954 : Nat := 2506275454485401478727907

theorem tailTrace_4880954 : CollatzResearch.WordTrace tailWord_4880954 prefixEnd_4880954 2506275454485401478727907 := by
  unfold tailWord_4880954
  simp only [CollatzResearch.WordTrace]
  refine ⟨44505754389786183355494479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118682011706096488947985277 44505754389786183355494479)
  ·
    refine ⟨66758631584679275033241719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44505754389786183355494479 66758631584679275033241719)
    ·
      refine ⟨100137947377018912549862579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66758631584679275033241719 100137947377018912549862579)
      ·
        refine ⟨150206921065528368824793869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100137947377018912549862579 150206921065528368824793869)
        ·
          refine ⟨56327595399573138309297701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150206921065528368824793869 56327595399573138309297701)
          ·
            refine ⟨10561424137419963432993319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56327595399573138309297701 10561424137419963432993319)
            ·
              refine ⟨15842136206129945149489979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10561424137419963432993319 15842136206129945149489979)
              ·
                refine ⟨23763204309194917724234969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15842136206129945149489979 23763204309194917724234969)
                ·
                  refine ⟨17822403231896188293176227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23763204309194917724234969 17822403231896188293176227)
                  ·
                    refine ⟨26733604847844282439764341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17822403231896188293176227 26733604847844282439764341)
                    ·
                      refine ⟨2506275454485401478727907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26733604847844282439764341 2506275454485401478727907)
                      ·
                        rfl

theorem cell23_4880954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_4880954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880954 prefixEnd_4880954 := by exact prefixLift 4880954
  have htrace : WordTrace (prefixWord ++ tailWord_4880954) baseStart_4880954 baseEnd_4880954 := by
    simpa [prefixWord, tailWord_4880954, baseEnd_4880954] using wordTrace_append hprefix tailTrace_4880954
  have hstable : (prefixWord ++ tailWord_4880954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880954).length < 2 ^ (prefixWord ++ tailWord_4880954).sum := by decide
  have hdescent : baseEnd_4880954 < baseStart_4880954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880974 : List Nat := [4, 1, 1, 1, 1, 2, 5, 1, 7]
def baseStart_4880974 : Nat := 118140960795 + 4880974 * 2 ^ 59
def prefixEnd_4880974 : Nat := 4983230072969 + 3 ^ 40 * 4880974 * 2
def baseEnd_4880974 : Nat := 278476191566499044497535

theorem tailTrace_4880974 : CollatzResearch.WordTrace tailWord_4880974 prefixEnd_4880974 278476191566499044497535 := by
  unfold tailWord_4880974
  simp only [CollatzResearch.WordTrace]
  refine ⟨22252968377384034604713247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118682498012714851225137317 22252968377384034604713247)
  ·
    refine ⟨33379452566076051907069871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22252968377384034604713247 33379452566076051907069871)
    ·
      refine ⟨50069178849114077860604807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33379452566076051907069871 50069178849114077860604807)
      ·
        refine ⟨75103768273671116790907211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50069178849114077860604807 75103768273671116790907211)
        ·
          refine ⟨112655652410506675186360817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75103768273671116790907211 112655652410506675186360817)
          ·
            refine ⟨84491739307880006389770613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112655652410506675186360817 84491739307880006389770613)
            ·
              refine ⟨7921100560113750599040995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84491739307880006389770613 7921100560113750599040995)
              ·
                refine ⟨11881650840170625898561493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7921100560113750599040995 11881650840170625898561493)
                ·
                  refine ⟨278476191566499044497535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11881650840170625898561493 278476191566499044497535)
                  ·
                    rfl

theorem cell23_4880974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_4880974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880974 prefixEnd_4880974 := by exact prefixLift 4880974
  have htrace : WordTrace (prefixWord ++ tailWord_4880974) baseStart_4880974 baseEnd_4880974 := by
    simpa [prefixWord, tailWord_4880974, baseEnd_4880974] using wordTrace_append hprefix tailTrace_4880974
  have hstable : (prefixWord ++ tailWord_4880974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880974).length < 2 ^ (prefixWord ++ tailWord_4880974).sum := by decide
  have hdescent : baseEnd_4880974 < baseStart_4880974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880984 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 2, 3, 3]
def baseStart_4880984 : Nat := 118140960795 + 4880984 * 2 ^ 59
def prefixEnd_4880984 : Nat := 4983230072969 + 3 ^ 40 * 4880984 * 2
def baseEnd_4880984 : Nat := 2506290858905036361352769

theorem tailTrace_4880984 : CollatzResearch.WordTrace tailWord_4880984 prefixEnd_4880984 2506290858905036361352769 := by
  unfold tailWord_4880984
  simp only [CollatzResearch.WordTrace]
  refine ⟨89012055874518024272785003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118682741166024032363713337 89012055874518024272785003)
  ·
    refine ⟨133518083811777036409177505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89012055874518024272785003 133518083811777036409177505)
    ·
      refine ⟨100138562858832777306883129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133518083811777036409177505 100138562858832777306883129)
      ·
        refine ⟨75103922144124582980162347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100138562858832777306883129 75103922144124582980162347)
        ·
          refine ⟨112655883216186874470243521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75103922144124582980162347 112655883216186874470243521)
          ·
            refine ⟨84491912412140155852682641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112655883216186874470243521 84491912412140155852682641)
            ·
              refine ⟨63368934309105116889511981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84491912412140155852682641 63368934309105116889511981)
              ·
                refine ⟨23763350365914418833566993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63368934309105116889511981 23763350365914418833566993)
                ·
                  refine ⟨17822512774435814125175245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23763350365914418833566993 17822512774435814125175245)
                  ·
                    refine ⟨6683442290413430296940717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17822512774435814125175245 6683442290413430296940717)
                    ·
                      refine ⟨2506290858905036361352769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6683442290413430296940717 2506290858905036361352769)
                      ·
                        rfl

theorem cell23_4880984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_4880984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880984 prefixEnd_4880984 := by exact prefixLift 4880984
  have htrace : WordTrace (prefixWord ++ tailWord_4880984) baseStart_4880984 baseEnd_4880984 := by
    simpa [prefixWord, tailWord_4880984, baseEnd_4880984] using wordTrace_append hprefix tailTrace_4880984
  have hstable : (prefixWord ++ tailWord_4880984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880984).length < 2 ^ (prefixWord ++ tailWord_4880984).sum := by decide
  have hdescent : baseEnd_4880984 < baseStart_4880984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881004 : List Nat := [2, 2, 1, 1, 3, 1, 3, 3, 2, 5]
def baseStart_4881004 : Nat := 118140960795 + 4881004 * 2 ^ 59
def prefixEnd_4881004 : Nat := 4983230072969 + 3 ^ 40 * 4881004 * 2
def baseEnd_4881004 : Nat := 835433709506042094367559

theorem tailTrace_4881004 : CollatzResearch.WordTrace tailWord_4881004 prefixEnd_4881004 835433709506042094367559 := by
  unfold tailWord_4881004
  simp only [CollatzResearch.WordTrace]
  refine ⟨89012420604481795980649033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118683227472642394640865377 89012420604481795980649033)
  ·
    refine ⟨66759315453361346985486775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89012420604481795980649033 66759315453361346985486775)
    ·
      refine ⟨100138973180042020478230163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66759315453361346985486775 100138973180042020478230163)
      ·
        refine ⟨150208459770063030717345245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100138973180042020478230163 150208459770063030717345245)
        ·
          refine ⟨56328172413773636519004467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150208459770063030717345245 56328172413773636519004467)
          ·
            refine ⟨84492258620660454778506701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56328172413773636519004467 84492258620660454778506701)
            ·
              refine ⟨31684596982747670541940013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84492258620660454778506701 31684596982747670541940013)
              ·
                refine ⟨11881723868530376453227505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31684596982747670541940013 11881723868530376453227505)
                ·
                  refine ⟨8911292901397782339920629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11881723868530376453227505 8911292901397782339920629)
                  ·
                    refine ⟨835433709506042094367559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8911292901397782339920629 835433709506042094367559)
                    ·
                      rfl

theorem cell23_4881004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_4881004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881004 prefixEnd_4881004 := by exact prefixLift 4881004
  have htrace : WordTrace (prefixWord ++ tailWord_4881004) baseStart_4881004 baseEnd_4881004 := by
    simpa [prefixWord, tailWord_4881004, baseEnd_4881004] using wordTrace_append hprefix tailTrace_4881004
  have hstable : (prefixWord ++ tailWord_4881004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881004).length < 2 ^ (prefixWord ++ tailWord_4881004).sum := by decide
  have hdescent : baseEnd_4881004 < baseStart_4881004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881084 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 1, 1, 8]
def baseStart_4881084 : Nat := 118140960795 + 4881084 * 2 ^ 59
def prefixEnd_4881084 : Nat := 4983230072969 + 3 ^ 40 * 4881084 * 2
def baseEnd_4881084 : Nat := 2506342206970485970102309

theorem tailTrace_4881084 : CollatzResearch.WordTrace tailWord_4881084 prefixEnd_4881084 2506342206970485970102309 := by
  unfold tailWord_4881084
  simp only [CollatzResearch.WordTrace]
  refine ⟨89013879524336882812105153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118685172699115843749473537 89013879524336882812105153)
  ·
    refine ⟨66760409643252662109078865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89013879524336882812105153 66760409643252662109078865)
    ·
      refine ⟨50070307232439496581809149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66760409643252662109078865 50070307232439496581809149)
      ·
        refine ⟨18776365212164811218178431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50070307232439496581809149 18776365212164811218178431)
        ·
          refine ⟨28164547818247216827267647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18776365212164811218178431 28164547818247216827267647)
          ·
            refine ⟨42246821727370825240901471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28164547818247216827267647 42246821727370825240901471)
            ·
              refine ⟨63370232591056237861352207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42246821727370825240901471 63370232591056237861352207)
              ·
                refine ⟨95055348886584356792028311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63370232591056237861352207 95055348886584356792028311)
                ·
                  refine ⟨142583023329876535188042467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95055348886584356792028311 142583023329876535188042467)
                  ·
                    refine ⟨213874534994814802782063701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 142583023329876535188042467 213874534994814802782063701)
                    ·
                      refine ⟨2506342206970485970102309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 213874534994814802782063701 2506342206970485970102309)
                      ·
                        rfl

theorem cell23_4881084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_4881084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881084 prefixEnd_4881084 := by exact prefixLift 4881084
  have htrace : WordTrace (prefixWord ++ tailWord_4881084) baseStart_4881084 baseEnd_4881084 := by
    simpa [prefixWord, tailWord_4881084, baseEnd_4881084] using wordTrace_append hprefix tailTrace_4881084
  have hstable : (prefixWord ++ tailWord_4881084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881084).length < 2 ^ (prefixWord ++ tailWord_4881084).sum := by decide
  have hdescent : baseEnd_4881084 < baseStart_4881084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881098 : List Nat := [3, 1, 2, 1, 4, 2, 3, 1, 6]
def baseStart_4881098 : Nat := 118140960795 + 4881098 * 2 ^ 59
def prefixEnd_4881098 : Nat := 4983230072969 + 3 ^ 40 * 4881098 * 2
def baseEnd_4881098 : Nat := 278483266188849879480805

theorem tailTrace_4881098 : CollatzResearch.WordTrace tailWord_4881098 prefixEnd_4881098 278483266188849879480805 := by
  unfold tailWord_4881098
  simp only [CollatzResearch.WordTrace]
  refine ⟨44507067417655761503804987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118685513113748697343479965 44507067417655761503804987)
  ·
    refine ⟨66760601126483642255707481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44507067417655761503804987 66760601126483642255707481)
    ·
      refine ⟨50070450844862731691780611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66760601126483642255707481 50070450844862731691780611)
      ·
        refine ⟨75105676267294097537670917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50070450844862731691780611 75105676267294097537670917)
        ·
          refine ⟨14082314300117643288313297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75105676267294097537670917 14082314300117643288313297)
          ·
            refine ⟨10561735725088232466234973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14082314300117643288313297 10561735725088232466234973)
            ·
              refine ⟨3960650896908087174838115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10561735725088232466234973 3960650896908087174838115)
              ·
                refine ⟨5940976345362130762257173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3960650896908087174838115 5940976345362130762257173)
                ·
                  refine ⟨278483266188849879480805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5940976345362130762257173 278483266188849879480805)
                  ·
                    rfl

theorem cell23_4881098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 6].length) (baseStart_4881098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881098 prefixEnd_4881098 := by exact prefixLift 4881098
  have htrace : WordTrace (prefixWord ++ tailWord_4881098) baseStart_4881098 baseEnd_4881098 := by
    simpa [prefixWord, tailWord_4881098, baseEnd_4881098] using wordTrace_append hprefix tailTrace_4881098
  have hstable : (prefixWord ++ tailWord_4881098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881098).length < 2 ^ (prefixWord ++ tailWord_4881098).sum := by decide
  have hdescent : baseEnd_4881098 < baseStart_4881098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881111 : List Nat := [1, 1, 3, 2, 1, 4, 1, 4, 1, 5]
def baseStart_4881111 : Nat := 118140960795 + 4881111 * 2 ^ 59
def prefixEnd_4881111 : Nat := 4983230072969 + 3 ^ 40 * 4881111 * 2
def baseEnd_4881111 : Nat := 835452023649385788154895

theorem tailTrace_4881111 : CollatzResearch.WordTrace tailWord_4881111 prefixEnd_4881111 835452023649385788154895 := by
  unfold tailWord_4881111
  simp only [CollatzResearch.WordTrace]
  refine ⟨178028743819575949235443187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118685829213050632823628791 178028743819575949235443187)
  ·
    refine ⟨267043115729363923853164781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178028743819575949235443187 267043115729363923853164781)
    ·
      refine ⟨100141168398511471444936793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267043115729363923853164781 100141168398511471444936793)
      ·
        refine ⟨75105876298883603583702595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100141168398511471444936793 75105876298883603583702595)
        ·
          refine ⟨112658814448325405375553893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75105876298883603583702595 112658814448325405375553893)
          ·
            refine ⟨21123527709061013507916355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112658814448325405375553893 21123527709061013507916355)
            ·
              refine ⟨31685291563591520261874533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21123527709061013507916355 31685291563591520261874533)
              ·
                refine ⟨5940992168173410049101475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31685291563591520261874533 5940992168173410049101475)
                ·
                  refine ⟨8911488252260115073652213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5940992168173410049101475 8911488252260115073652213)
                  ·
                    refine ⟨835452023649385788154895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8911488252260115073652213 835452023649385788154895)
                    ·
                      rfl

theorem cell23_4881111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 5].length) (baseStart_4881111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881111 prefixEnd_4881111 := by exact prefixLift 4881111
  have htrace : WordTrace (prefixWord ++ tailWord_4881111) baseStart_4881111 baseEnd_4881111 := by
    simpa [prefixWord, tailWord_4881111, baseEnd_4881111] using wordTrace_append hprefix tailTrace_4881111
  have hstable : (prefixWord ++ tailWord_4881111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881111).length < 2 ^ (prefixWord ++ tailWord_4881111).sum := by decide
  have hdescent : baseEnd_4881111 < baseStart_4881111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881144 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 3, 1, 6]
def baseStart_4881144 : Nat := 118140960795 + 4881144 * 2 ^ 59
def prefixEnd_4881144 : Nat := 4983230072969 + 3 ^ 40 * 4881144 * 2
def baseEnd_4881144 : Nat := 2506373015809755735352033

theorem tailTrace_4881144 : CollatzResearch.WordTrace tailWord_4881144 prefixEnd_4881144 2506373015809755735352033 := by
  unfold tailWord_4881144
  simp only [CollatzResearch.WordTrace]
  refine ⟨89014973714228197935697243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118686631618970930580929657 89014973714228197935697243)
  ·
    refine ⟨133522460571342296903545865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89014973714228197935697243 133522460571342296903545865)
    ·
      refine ⟨100141845428506722677659399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133522460571342296903545865 100141845428506722677659399)
      ·
        refine ⟨150212768142760084016489099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100141845428506722677659399 150212768142760084016489099)
        ·
          refine ⟨225319152214140126024733649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150212768142760084016489099 225319152214140126024733649)
          ·
            refine ⟨168989364160605094518550237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225319152214140126024733649 168989364160605094518550237)
            ·
              refine ⟨63371011560226910444456339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168989364160605094518550237 63371011560226910444456339)
              ·
                refine ⟨95056517340340365666684509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63371011560226910444456339 95056517340340365666684509)
                ·
                  refine ⟨35646194002627637125006691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95056517340340365666684509 35646194002627637125006691)
                  ·
                    refine ⟨53469291003941455687510037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35646194002627637125006691 53469291003941455687510037)
                    ·
                      refine ⟨2506373015809755735352033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53469291003941455687510037 2506373015809755735352033)
                      ·
                        rfl

theorem cell23_4881144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_4881144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881144 prefixEnd_4881144 := by exact prefixLift 4881144
  have htrace : WordTrace (prefixWord ++ tailWord_4881144) baseStart_4881144 baseEnd_4881144 := by
    simpa [prefixWord, tailWord_4881144, baseEnd_4881144] using wordTrace_append hprefix tailTrace_4881144
  have hstable : (prefixWord ++ tailWord_4881144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881144).length < 2 ^ (prefixWord ++ tailWord_4881144).sum := by decide
  have hdescent : baseEnd_4881144 < baseStart_4881144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881151 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 3]
def baseStart_4881151 : Nat := 118140960795 + 4881151 * 2 ^ 59
def prefixEnd_4881151 : Nat := 4983230072969 + 3 ^ 40 * 4881151 * 2
def baseEnd_4881151 : Nat := 2506376610174337207964501

theorem tailTrace_4881151 : CollatzResearch.WordTrace tailWord_4881151 prefixEnd_4881151 2506376610174337207964501 := by
  unfold tailWord_4881151
  simp only [CollatzResearch.WordTrace]
  refine ⟨178030202739431036066899307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118686801826287357377932871 178030202739431036066899307)
  ·
    refine ⟨267045304109146554100348961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178030202739431036066899307 267045304109146554100348961)
    ·
      refine ⟨200283978081859915575261721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267045304109146554100348961 200283978081859915575261721)
      ·
        refine ⟨150212983561394936681446291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200283978081859915575261721 150212983561394936681446291)
        ·
          refine ⟨225319475342092405022169437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150212983561394936681446291 225319475342092405022169437)
          ·
            refine ⟨84494803253284651883313539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225319475342092405022169437 84494803253284651883313539)
            ·
              refine ⟨126742204879926977824970309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84494803253284651883313539 126742204879926977824970309)
              ·
                refine ⟨23764163414986308342181933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126742204879926977824970309 23764163414986308342181933)
                ·
                  refine ⟨8911561280619865628318225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23764163414986308342181933 8911561280619865628318225)
                  ·
                    refine ⟨6683670960464899221238669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8911561280619865628318225 6683670960464899221238669)
                    ·
                      refine ⟨2506376610174337207964501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6683670960464899221238669 2506376610174337207964501)
                      ·
                        rfl

theorem cell23_4881151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 3].length) (baseStart_4881151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881151 prefixEnd_4881151 := by exact prefixLift 4881151
  have htrace : WordTrace (prefixWord ++ tailWord_4881151) baseStart_4881151 baseEnd_4881151 := by
    simpa [prefixWord, tailWord_4881151, baseEnd_4881151] using wordTrace_append hprefix tailTrace_4881151
  have hstable : (prefixWord ++ tailWord_4881151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881151).length < 2 ^ (prefixWord ++ tailWord_4881151).sum := by decide
  have hdescent : baseEnd_4881151 < baseStart_4881151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881185 : List Nat := [1, 2, 3, 2, 1, 2, 5, 1, 1, 2, 3]
def baseStart_4881185 : Nat := 118140960795 + 4881185 * 2 ^ 59
def prefixEnd_4881185 : Nat := 4983230072969 + 3 ^ 40 * 4881185 * 2
def baseEnd_4881185 : Nat := 2506394068516590074939345

theorem tailTrace_4881185 : CollatzResearch.WordTrace tailWord_4881185 prefixEnd_4881185 2506394068516590074939345 := by
  unfold tailWord_4881185
  simp only [CollatzResearch.WordTrace]
  refine ⟨178031442821307859873637009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118687628547538573249091339 178031442821307859873637009)
  ·
    refine ⟨133523582115980894905227757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178031442821307859873637009 133523582115980894905227757)
    ·
      refine ⟨50071343293492835589460409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133523582115980894905227757 50071343293492835589460409)
      ·
        refine ⟨37553507470119626692095307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50071343293492835589460409 37553507470119626692095307)
        ·
          refine ⟨56330261205179440038142961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37553507470119626692095307 56330261205179440038142961)
          ·
            refine ⟨42247695903884580028607221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56330261205179440038142961 42247695903884580028607221)
            ·
              refine ⟨3960721490989179377681927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42247695903884580028607221 3960721490989179377681927)
              ·
                refine ⟨5941082236483769066522891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3960721490989179377681927 5941082236483769066522891)
                ·
                  refine ⟨8911623354725653599784337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5941082236483769066522891 8911623354725653599784337)
                  ·
                    refine ⟨6683717516044240199838253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8911623354725653599784337 6683717516044240199838253)
                    ·
                      refine ⟨2506394068516590074939345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6683717516044240199838253 2506394068516590074939345)
                      ·
                        rfl

theorem cell23_4881185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_4881185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881185 prefixEnd_4881185 := by exact prefixLift 4881185
  have htrace : WordTrace (prefixWord ++ tailWord_4881185) baseStart_4881185 baseEnd_4881185 := by
    simpa [prefixWord, tailWord_4881185, baseEnd_4881185] using wordTrace_append hprefix tailTrace_4881185
  have hstable : (prefixWord ++ tailWord_4881185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881185).length < 2 ^ (prefixWord ++ tailWord_4881185).sum := by decide
  have hdescent : baseEnd_4881185 < baseStart_4881185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881208 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 5, 3, 2]
def baseStart_4881208 : Nat := 118140960795 + 4881208 * 2 ^ 59
def prefixEnd_4881208 : Nat := 4983230072969 + 3 ^ 40 * 4881208 * 2
def baseEnd_4881208 : Nat := 2506405878571643484951739

theorem tailTrace_4881208 : CollatzResearch.WordTrace tailWord_4881208 prefixEnd_4881208 2506405878571643484951739 := by
  unfold tailWord_4881208
  simp only [CollatzResearch.WordTrace]
  refine ⟨89016140850112267400862139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118688187800149689867816185 89016140850112267400862139)
  ·
    refine ⟨133524211275168401101293209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89016140850112267400862139 133524211275168401101293209)
    ·
      refine ⟨100143158456376300825969907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133524211275168401101293209 100143158456376300825969907)
      ·
        refine ⟨150214737684564451238954861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100143158456376300825969907 150214737684564451238954861)
        ·
          refine ⟨56330526631711669214608073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150214737684564451238954861 56330526631711669214608073)
          ·
            refine ⟨42247894973783751910956055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56330526631711669214608073 42247894973783751910956055)
            ·
              refine ⟨63371842460675627866434083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42247894973783751910956055 63371842460675627866434083)
              ·
                refine ⟨95057763691013441799651125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63371842460675627866434083 95057763691013441799651125)
                ·
                  refine ⟨8911665346032510168717293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95057763691013441799651125 8911665346032510168717293)
                  ·
                    refine ⟨3341874504762191313268985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8911665346032510168717293 3341874504762191313268985)
                    ·
                      refine ⟨2506405878571643484951739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3341874504762191313268985 2506405878571643484951739)
                      ·
                        rfl

theorem cell23_4881208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 5, 3, 2].length) (baseStart_4881208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881208 prefixEnd_4881208 := by exact prefixLift 4881208
  have htrace : WordTrace (prefixWord ++ tailWord_4881208) baseStart_4881208 baseEnd_4881208 := by
    simpa [prefixWord, tailWord_4881208, baseEnd_4881208] using wordTrace_append hprefix tailTrace_4881208
  have hstable : (prefixWord ++ tailWord_4881208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881208).length < 2 ^ (prefixWord ++ tailWord_4881208).sum := by decide
  have hdescent : baseEnd_4881208 < baseStart_4881208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881215 : List Nat := [1, 1, 2, 2, 5, 1, 2, 3, 2, 1, 3]
def baseStart_4881215 : Nat := 118140960795 + 4881215 * 2 ^ 59
def prefixEnd_4881215 : Nat := 4983230072969 + 3 ^ 40 * 4881215 * 2
def baseEnd_4881215 : Nat := 2506409472936224957564207

theorem tailTrace_4881215 : CollatzResearch.WordTrace tailWord_4881215 prefixEnd_4881215 2506409472936224957564207 := by
  unfold tailWord_4881215
  simp only [CollatzResearch.WordTrace]
  refine ⟨178032537011199174997229099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118688358007466116664819399 178032537011199174997229099)
  ·
    refine ⟨267048805516798762495843649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178032537011199174997229099 267048805516798762495843649)
    ·
      refine ⟨200286604137599071871882737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267048805516798762495843649 200286604137599071871882737)
      ·
        refine ⟨150214953103199303903912053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200286604137599071871882737 150214953103199303903912053)
        ·
          refine ⟨14082651853424934740991755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 150214953103199303903912053 14082651853424934740991755)
          ·
            refine ⟨21123977780137402111487633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14082651853424934740991755 21123977780137402111487633)
            ·
              refine ⟨15842983335103051583615725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21123977780137402111487633 15842983335103051583615725)
              ·
                refine ⟨5941118750663644343855897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15842983335103051583615725 5941118750663644343855897)
                ·
                  refine ⟨4455839062997733257891923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5941118750663644343855897 4455839062997733257891923)
                  ·
                    refine ⟨6683758594496599886837885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4455839062997733257891923 6683758594496599886837885)
                    ·
                      refine ⟨2506409472936224957564207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6683758594496599886837885 2506409472936224957564207)
                      ·
                        rfl

theorem cell23_4881215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 1, 3].length) (baseStart_4881215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881215 prefixEnd_4881215 := by exact prefixLift 4881215
  have htrace : WordTrace (prefixWord ++ tailWord_4881215) baseStart_4881215 baseEnd_4881215 := by
    simpa [prefixWord, tailWord_4881215, baseEnd_4881215] using wordTrace_append hprefix tailTrace_4881215
  have hstable : (prefixWord ++ tailWord_4881215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881215).length < 2 ^ (prefixWord ++ tailWord_4881215).sum := by decide
  have hdescent : baseEnd_4881215 < baseStart_4881215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881222 : List Nat := [6, 1, 1, 2, 2, 1, 3, 7]
def baseStart_4881222 : Nat := 118140960795 + 4881222 * 2 ^ 59
def prefixEnd_4881222 : Nat := 4983230072969 + 3 ^ 40 * 4881222 * 2
def baseEnd_4881222 : Nat := 92830113603733571488025

theorem tailTrace_4881222 : CollatzResearch.WordTrace tailWord_4881222 prefixEnd_4881222 92830113603733571488025 := by
  unfold tailWord_4881222
  simp only [CollatzResearch.WordTrace]
  refine ⟨5563524760067931724772935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 118688528214782543461822613 5563524760067931724772935)
  ·
    refine ⟨8345287140101897587159403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5563524760067931724772935 8345287140101897587159403)
    ·
      refine ⟨12517930710152846380739105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8345287140101897587159403 12517930710152846380739105)
      ·
        refine ⟨9388448032614634785554329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12517930710152846380739105 9388448032614634785554329)
        ·
          refine ⟨7041336024460976089165747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9388448032614634785554329 7041336024460976089165747)
          ·
            refine ⟨10562004036691464133748621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7041336024460976089165747 10562004036691464133748621)
            ·
              refine ⟨3960751513759299050155733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10562004036691464133748621 3960751513759299050155733)
              ·
                refine ⟨92830113603733571488025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3960751513759299050155733 92830113603733571488025)
                ·
                  rfl

theorem cell23_4881222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_4881222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881222 prefixEnd_4881222 := by exact prefixLift 4881222
  have htrace : WordTrace (prefixWord ++ tailWord_4881222) baseStart_4881222 baseEnd_4881222 := by
    simpa [prefixWord, tailWord_4881222, baseEnd_4881222] using wordTrace_append hprefix tailTrace_4881222
  have hstable : (prefixWord ++ tailWord_4881222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881222).length < 2 ^ (prefixWord ++ tailWord_4881222).sum := by decide
  have hdescent : baseEnd_4881222 < baseStart_4881222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881242 : List Nat := [3, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2]
def baseStart_4881242 : Nat := 118140960795 + 4881242 * 2 ^ 59
def prefixEnd_4881242 : Nat := 4983230072969 + 3 ^ 40 * 4881242 * 2
def baseEnd_4881242 : Nat := 2506423336913896351926583

theorem tailTrace_4881242 : CollatzResearch.WordTrace tailWord_4881242 prefixEnd_4881242 2506423336913896351926583 := by
  unfold tailWord_4881242
  simp only [CollatzResearch.WordTrace]
  refine ⟨44508380445525339652115495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118689014521400905738974653 44508380445525339652115495)
  ·
    refine ⟨66762570668288009478173243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44508380445525339652115495 66762570668288009478173243)
    ·
      refine ⟨100143856002432014217259865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66762570668288009478173243 100143856002432014217259865)
      ·
        refine ⟨75107892001824010662944899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100143856002432014217259865 75107892001824010662944899)
        ·
          refine ⟨112661838002736015994417349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75107892001824010662944899 112661838002736015994417349)
          ·
            refine ⟨21124094625513002998953253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112661838002736015994417349 21124094625513002998953253)
            ·
              refine ⟨3960767742283688062303735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21124094625513002998953253 3960767742283688062303735)
              ·
                refine ⟨5941151613425532093455603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3960767742283688062303735 5941151613425532093455603)
                ·
                  refine ⟨8911727420138298140183405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5941151613425532093455603 8911727420138298140183405)
                  ·
                    refine ⟨3341897782551861802568777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8911727420138298140183405 3341897782551861802568777)
                    ·
                      refine ⟨2506423336913896351926583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3341897782551861802568777 2506423336913896351926583)
                      ·
                        rfl

theorem cell23_4881242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2].length) (baseStart_4881242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881242 prefixEnd_4881242 := by exact prefixLift 4881242
  have htrace : WordTrace (prefixWord ++ tailWord_4881242) baseStart_4881242 baseEnd_4881242 := by
    simpa [prefixWord, tailWord_4881242, baseEnd_4881242] using wordTrace_append hprefix tailTrace_4881242
  have hstable : (prefixWord ++ tailWord_4881242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881242).length < 2 ^ (prefixWord ++ tailWord_4881242).sum := by decide
  have hdescent : baseEnd_4881242 < baseStart_4881242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881291 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 1, 7]
def baseStart_4881291 : Nat := 118140960795 + 4881291 * 2 ^ 59
def prefixEnd_4881291 : Nat := 4983230072969 + 3 ^ 40 * 4881291 * 2
def baseEnd_4881291 : Nat := 835482832488655553404619

theorem tailTrace_4881291 : CollatzResearch.WordTrace tailWord_4881291 prefixEnd_4881291 835482832488655553404619 := by
  unfold tailWord_4881291
  simp only [CollatzResearch.WordTrace]
  refine ⟨178035308958923839976995727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118690205972615893317997151 178035308958923839976995727)
  ·
    refine ⟨267052963438385759965493591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178035308958923839976995727 267052963438385759965493591)
    ·
      refine ⟨400579445157578639948240387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267052963438385759965493591 400579445157578639948240387)
      ·
        refine ⟨600869167736367959922360581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400579445157578639948240387 600869167736367959922360581)
        ·
          refine ⟨112662968950568992485442609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 600869167736367959922360581 112662968950568992485442609)
          ·
            refine ⟨84497226712926744364081957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112662968950568992485442609 84497226712926744364081957)
            ·
              refine ⟨15843230008673764568265367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84497226712926744364081957 15843230008673764568265367)
              ·
                refine ⟨23764845013010646852398051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15843230008673764568265367 23764845013010646852398051)
                ·
                  refine ⟨35647267519515970278597077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23764845013010646852398051 35647267519515970278597077)
                  ·
                    refine ⟨835482832488655553404619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35647267519515970278597077 835482832488655553404619)
                    ·
                      rfl

theorem cell23_4881291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 7].length) (baseStart_4881291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881291 prefixEnd_4881291 := by exact prefixLift 4881291
  have htrace : WordTrace (prefixWord ++ tailWord_4881291) baseStart_4881291 baseEnd_4881291 := by
    simpa [prefixWord, tailWord_4881291, baseEnd_4881291] using wordTrace_append hprefix tailTrace_4881291
  have hstable : (prefixWord ++ tailWord_4881291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881291).length < 2 ^ (prefixWord ++ tailWord_4881291).sum := by decide
  have hdescent : baseEnd_4881291 < baseStart_4881291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881338 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 5, 4]
def baseStart_4881338 : Nat := 118140960795 + 4881338 * 2 ^ 59
def prefixEnd_4881338 : Nat := 4983230072969 + 3 ^ 40 * 4881338 * 2
def baseEnd_4881338 : Nat := 835490877018909325442047

theorem tailTrace_4881338 : CollatzResearch.WordTrace tailWord_4881338 prefixEnd_4881338 835490877018909325442047 := by
  unfold tailWord_4881338
  simp only [CollatzResearch.WordTrace]
  refine ⟨44509255797438391750989167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118691348793169044669304445 44509255797438391750989167)
  ·
    refine ⟨66763883696157587626483751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44509255797438391750989167 66763883696157587626483751)
    ·
      refine ⟨100145825544236381439725627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66763883696157587626483751 100145825544236381439725627)
      ·
        refine ⟨150218738316354572159588441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100145825544236381439725627 150218738316354572159588441)
        ·
          refine ⟨112664053737265929119691331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150218738316354572159588441 112664053737265929119691331)
          ·
            refine ⟨168996080605898893679536997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112664053737265929119691331 168996080605898893679536997)
            ·
              refine ⟨31686765113606042564913187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 168996080605898893679536997 31686765113606042564913187)
              ·
                refine ⟨47530147670409063847369781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31686765113606042564913187 47530147670409063847369781)
                ·
                  refine ⟨4455951344100849735690917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47530147670409063847369781 4455951344100849735690917)
                  ·
                    refine ⟨835490877018909325442047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4455951344100849735690917 835490877018909325442047)
                    ·
                      rfl

theorem cell23_4881338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 5, 4].length) (baseStart_4881338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881338 prefixEnd_4881338 := by exact prefixLift 4881338
  have htrace : WordTrace (prefixWord ++ tailWord_4881338) baseStart_4881338 baseEnd_4881338 := by
    simpa [prefixWord, tailWord_4881338, baseEnd_4881338] using wordTrace_append hprefix tailTrace_4881338
  have hstable : (prefixWord ++ tailWord_4881338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881338).length < 2 ^ (prefixWord ++ tailWord_4881338).sum := by decide
  have hdescent : baseEnd_4881338 < baseStart_4881338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881351 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 10]
def baseStart_4881351 : Nat := 118140960795 + 4881351 * 2 ^ 59
def prefixEnd_4881351 : Nat := 4983230072969 + 3 ^ 40 * 4881351 * 2
def baseEnd_4881351 : Nat := 278497700700581825051509

theorem tailTrace_4881351 : CollatzResearch.WordTrace tailWord_4881351 prefixEnd_4881351 278497700700581825051509 := by
  unfold tailWord_4881351
  simp only [CollatzResearch.WordTrace]
  refine ⟨178037497338706470224179907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118691664892470980149453271 178037497338706470224179907)
  ·
    refine ⟨267056246008059705336269861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178037497338706470224179907 267056246008059705336269861)
    ·
      refine ⟨50073046126511194750550599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 267056246008059705336269861 50073046126511194750550599)
      ·
        refine ⟨75109569189766792125825899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50073046126511194750550599 75109569189766792125825899)
        ·
          refine ⟨112664353784650188188738849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75109569189766792125825899 112664353784650188188738849)
          ·
            refine ⟨84498265338487641141554137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112664353784650188188738849 84498265338487641141554137)
            ·
              refine ⟨63373699003865730856165603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84498265338487641141554137 63373699003865730856165603)
              ·
                refine ⟨95060548505798596284248405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63373699003865730856165603 95060548505798596284248405)
                ·
                  refine ⟨278497700700581825051509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 95060548505798596284248405 278497700700581825051509)
                  ·
                    rfl

theorem cell23_4881351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 10].length) (baseStart_4881351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881351 prefixEnd_4881351 := by exact prefixLift 4881351
  have htrace : WordTrace (prefixWord ++ tailWord_4881351) baseStart_4881351 baseEnd_4881351 := by
    simpa [prefixWord, tailWord_4881351, baseEnd_4881351] using wordTrace_append hprefix tailTrace_4881351
  have hstable : (prefixWord ++ tailWord_4881351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881351).length < 2 ^ (prefixWord ++ tailWord_4881351).sum := by decide
  have hdescent : baseEnd_4881351 < baseStart_4881351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881368 : List Nat := [2, 1, 2, 2, 2, 3, 1, 4, 6]
def baseStart_4881368 : Nat := 118140960795 + 4881368 * 2 ^ 59
def prefixEnd_4881368 : Nat := 4983230072969 + 3 ^ 40 * 4881368 * 2
def baseEnd_4881368 : Nat := 278498670608484762105667

theorem tailTrace_4881368 : CollatzResearch.WordTrace tailWord_4881368 prefixEnd_4881368 278498670608484762105667 := by
  unfold tailWord_4881368
  simp only [CollatzResearch.WordTrace]
  refine ⟨89019058689822441063774379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118692078253096588085032505 89019058689822441063774379)
  ·
    refine ⟨133528588034733661595661569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89019058689822441063774379 133528588034733661595661569)
    ·
      refine ⟨100146441026050246196746177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133528588034733661595661569 100146441026050246196746177)
      ·
        refine ⟨75109830769537684647559633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100146441026050246196746177 75109830769537684647559633)
        ·
          refine ⟨56332373077153263485669725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75109830769537684647559633 56332373077153263485669725)
          ·
            refine ⟨21124639903932473807126147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56332373077153263485669725 21124639903932473807126147)
            ·
              refine ⟨31686959855898710710689221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21124639903932473807126147 31686959855898710710689221)
              ·
                refine ⟨5941304972981008258254229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31686959855898710710689221 5941304972981008258254229)
                ·
                  refine ⟨278498670608484762105667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5941304972981008258254229 278498670608484762105667)
                  ·
                    rfl

theorem cell23_4881368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 6].length) (baseStart_4881368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881368 prefixEnd_4881368 := by exact prefixLift 4881368
  have htrace : WordTrace (prefixWord ++ tailWord_4881368) baseStart_4881368 baseEnd_4881368 := by
    simpa [prefixWord, tailWord_4881368, baseEnd_4881368] using wordTrace_append hprefix tailTrace_4881368
  have hstable : (prefixWord ++ tailWord_4881368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881368).length < 2 ^ (prefixWord ++ tailWord_4881368).sum := by decide
  have hdescent : baseEnd_4881368 < baseStart_4881368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881396 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_4881396 : Nat := 118140960795 + 4881396 * 2 ^ 59
def prefixEnd_4881396 : Nat := 4983230072969 + 3 ^ 40 * 4881396 * 2
def baseEnd_4881396 : Nat := 2506502412934688749400875

theorem tailTrace_4881396 : CollatzResearch.WordTrace tailWord_4881396 prefixEnd_4881396 2506502412934688749400875 := by
  unfold tailWord_4881396
  simp only [CollatzResearch.WordTrace]
  refine ⟨89019569311771721454784021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118692759082362295273045361 89019569311771721454784021)
  ·
    refine ⟨4172792311489299443193001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 89019569311771721454784021 4172792311489299443193001)
    ·
      refine ⟨3129594233616974582394751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4172792311489299443193001 3129594233616974582394751)
      ·
        refine ⟨4694391350425461873592127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3129594233616974582394751 4694391350425461873592127)
        ·
          refine ⟨7041587025638192810388191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4694391350425461873592127 7041587025638192810388191)
          ·
            refine ⟨10562380538457289215582287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7041587025638192810388191 10562380538457289215582287)
            ·
              refine ⟨15843570807685933823373431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10562380538457289215582287 15843570807685933823373431)
              ·
                refine ⟨23765356211528900735060147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15843570807685933823373431 23765356211528900735060147)
                ·
                  refine ⟨35648034317293351102590221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23765356211528900735060147 35648034317293351102590221)
                  ·
                    refine ⟨13368012868985006663471333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35648034317293351102590221 13368012868985006663471333)
                    ·
                      refine ⟨2506502412934688749400875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13368012868985006663471333 2506502412934688749400875)
                      ·
                        rfl

theorem cell23_4881396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_4881396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881396 prefixEnd_4881396 := by exact prefixLift 4881396
  have htrace : WordTrace (prefixWord ++ tailWord_4881396) baseStart_4881396 baseEnd_4881396 := by
    simpa [prefixWord, tailWord_4881396, baseEnd_4881396] using wordTrace_append hprefix tailTrace_4881396
  have hstable : (prefixWord ++ tailWord_4881396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881396).length < 2 ^ (prefixWord ++ tailWord_4881396).sum := by decide
  have hdescent : baseEnd_4881396 < baseStart_4881396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881406 : List Nat := [4, 2, 2, 2, 2, 1, 2, 3, 1, 4]
def baseStart_4881406 : Nat := 118140960795 + 4881406 * 2 ^ 59
def prefixEnd_4881406 : Nat := 4983230072969 + 3 ^ 40 * 4881406 * 2
def baseEnd_4881406 : Nat := 835502515913744570091943

theorem tailTrace_4881406 : CollatzResearch.WordTrace tailWord_4881406 prefixEnd_4881406 835502515913744570091943 := by
  unfold tailWord_4881406
  simp only [CollatzResearch.WordTrace]
  refine ⟨22254937919188401827179009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118693002235671476411621381 22254937919188401827179009)
  ·
    refine ⟨16691203439391301370384257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22254937919188401827179009 16691203439391301370384257)
    ·
      refine ⟨12518402579543476027788193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16691203439391301370384257 12518402579543476027788193)
      ·
        refine ⟨9388801934657607020841145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12518402579543476027788193 9388801934657607020841145)
        ·
          refine ⟨7041601450993205265630859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9388801934657607020841145 7041601450993205265630859)
          ·
            refine ⟨10562402176489807898446289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7041601450993205265630859 10562402176489807898446289)
            ·
              refine ⟨7921801632367355923834717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10562402176489807898446289 7921801632367355923834717)
              ·
                refine ⟨2970675612137758471438019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7921801632367355923834717 2970675612137758471438019)
                ·
                  refine ⟨4456013418206637707157029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2970675612137758471438019 4456013418206637707157029)
                  ·
                    refine ⟨835502515913744570091943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4456013418206637707157029 835502515913744570091943)
                    ·
                      rfl

theorem cell23_4881406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_4881406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881406 prefixEnd_4881406 := by exact prefixLift 4881406
  have htrace : WordTrace (prefixWord ++ tailWord_4881406) baseStart_4881406 baseEnd_4881406 := by
    simpa [prefixWord, tailWord_4881406, baseEnd_4881406] using wordTrace_append hprefix tailTrace_4881406
  have hstable : (prefixWord ++ tailWord_4881406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881406).length < 2 ^ (prefixWord ++ tailWord_4881406).sum := by decide
  have hdescent : baseEnd_4881406 < baseStart_4881406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881415 : List Nat := [1, 1, 4, 3, 1, 1, 3, 3, 1, 5]
def baseStart_4881415 : Nat := 118140960795 + 4881415 * 2 ^ 59
def prefixEnd_4881415 : Nat := 4983230072969 + 3 ^ 40 * 4881415 * 2
def baseEnd_4881415 : Nat := 835504056355708058354429

theorem tailTrace_4881415 : CollatzResearch.WordTrace tailWord_4881415 prefixEnd_4881415 835504056355708058354429 := by
  unfold tailWord_4881415
  simp only [CollatzResearch.WordTrace]
  refine ⟨178039831610474609154509699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118693221073649739436339799 178039831610474609154509699)
  ·
    refine ⟨267059747415711913731764549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178039831610474609154509699 267059747415711913731764549)
    ·
      refine ⟨50073702640445983824705853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 267059747415711913731764549 50073702640445983824705853)
      ·
        refine ⟨18777638490167243934264695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50073702640445983824705853 18777638490167243934264695)
        ·
          refine ⟨28166457735250865901397043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18777638490167243934264695 28166457735250865901397043)
          ·
            refine ⟨42249686602876298852095565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28166457735250865901397043 42249686602876298852095565)
            ·
              refine ⟨15843632476078612069535837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42249686602876298852095565 15843632476078612069535837)
              ·
                refine ⟨5941362178529479526075939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15843632476078612069535837 5941362178529479526075939)
                ·
                  refine ⟨8912043267794219289113909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5941362178529479526075939 8912043267794219289113909)
                  ·
                    refine ⟨835504056355708058354429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8912043267794219289113909 835504056355708058354429)
                    ·
                      rfl

theorem cell23_4881415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_4881415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881415 prefixEnd_4881415 := by exact prefixLift 4881415
  have htrace : WordTrace (prefixWord ++ tailWord_4881415) baseStart_4881415 baseEnd_4881415 := by
    simpa [prefixWord, tailWord_4881415, baseEnd_4881415] using wordTrace_append hprefix tailTrace_4881415
  have hstable : (prefixWord ++ tailWord_4881415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881415).length < 2 ^ (prefixWord ++ tailWord_4881415).sum := by decide
  have hdescent : baseEnd_4881415 < baseStart_4881415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881429 : List Nat := [1, 3, 2, 1, 4, 1, 2, 4, 1, 1, 3]
def baseStart_4881429 : Nat := 118140960795 + 4881429 * 2 ^ 59
def prefixEnd_4881429 : Nat := 4983230072969 + 3 ^ 40 * 4881429 * 2
def baseEnd_4881429 : Nat := 2506519357796287120288223

theorem tailTrace_4881429 : CollatzResearch.WordTrace tailWord_4881429 prefixEnd_4881429 2506519357796287120288223 := by
  unfold tailWord_4881429
  simp only [CollatzResearch.WordTrace]
  refine ⟨178040342232423889545519341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118693561488282593030346227 178040342232423889545519341)
  ·
    refine ⟨66765128337158958579569753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178040342232423889545519341 66765128337158958579569753)
    ·
      refine ⟨50073846252869218934677315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66765128337158958579569753 50073846252869218934677315)
      ·
        refine ⟨75110769379303828402015973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50073846252869218934677315 75110769379303828402015973)
        ·
          refine ⟨14083269258619467825377995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75110769379303828402015973 14083269258619467825377995)
          ·
            refine ⟨21124903887929201738066993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14083269258619467825377995 21124903887929201738066993)
            ·
              refine ⟨15843677915946901303550245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21124903887929201738066993 15843677915946901303550245)
              ·
                refine ⟨2970689609240043994415671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15843677915946901303550245 2970689609240043994415671)
                ·
                  refine ⟨4456034413860065991623507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2970689609240043994415671 4456034413860065991623507)
                  ·
                    refine ⟨6684051620790098987435261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4456034413860065991623507 6684051620790098987435261)
                    ·
                      refine ⟨2506519357796287120288223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6684051620790098987435261 2506519357796287120288223)
                      ·
                        rfl

theorem cell23_4881429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 1, 1, 3].length) (baseStart_4881429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881429 prefixEnd_4881429 := by exact prefixLift 4881429
  have htrace : WordTrace (prefixWord ++ tailWord_4881429) baseStart_4881429 baseEnd_4881429 := by
    simpa [prefixWord, tailWord_4881429, baseEnd_4881429] using wordTrace_append hprefix tailTrace_4881429
  have hstable : (prefixWord ++ tailWord_4881429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881429).length < 2 ^ (prefixWord ++ tailWord_4881429).sum := by decide
  have hdescent : baseEnd_4881429 < baseStart_4881429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881452 : List Nat := [2, 2, 1, 1, 1, 2, 3, 4, 3, 2, 2]
def baseStart_4881452 : Nat := 118140960795 + 4881452 * 2 ^ 59
def prefixEnd_4881452 : Nat := 4983230072969 + 3 ^ 40 * 4881452 * 2
def baseEnd_4881452 : Nat := 2506531167851340530300617

theorem tailTrace_4881452 : CollatzResearch.WordTrace tailWord_4881452 prefixEnd_4881452 2506531167851340530300617 := by
  unfold tailWord_4881452
  simp only [CollatzResearch.WordTrace]
  refine ⟨89020590555670282236803305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118694120740893709649071073 89020590555670282236803305)
  ·
    refine ⟨66765442916752711677602479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89020590555670282236803305 66765442916752711677602479)
    ·
      refine ⟨100148164375129067516403719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66765442916752711677602479 100148164375129067516403719)
      ·
        refine ⟨150222246562693601274605579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100148164375129067516403719 150222246562693601274605579)
        ·
          refine ⟨225333369844040401911908369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150222246562693601274605579 225333369844040401911908369)
          ·
            refine ⟨169000027383030301433931277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225333369844040401911908369 169000027383030301433931277)
            ·
              refine ⟨63375010268636363037724229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169000027383030301433931277 63375010268636363037724229)
              ·
                refine ⟨11882814425369318069573293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63375010268636363037724229 11882814425369318069573293)
                ·
                  refine ⟨4456055409513494276089985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11882814425369318069573293 4456055409513494276089985)
                  ·
                    refine ⟨3342041557135120707067489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4456055409513494276089985 3342041557135120707067489)
                    ·
                      refine ⟨2506531167851340530300617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3342041557135120707067489 2506531167851340530300617)
                      ·
                        rfl

theorem cell23_4881452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 2, 2].length) (baseStart_4881452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881452 prefixEnd_4881452 := by exact prefixLift 4881452
  have htrace : WordTrace (prefixWord ++ tailWord_4881452) baseStart_4881452 baseEnd_4881452 := by
    simpa [prefixWord, tailWord_4881452, baseEnd_4881452] using wordTrace_append hprefix tailTrace_4881452
  have hstable : (prefixWord ++ tailWord_4881452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881452).length < 2 ^ (prefixWord ++ tailWord_4881452).sum := by decide
  have hdescent : baseEnd_4881452 < baseStart_4881452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881458 : List Nat := [3, 2, 1, 1, 2, 2, 3, 9]
def baseStart_4881458 : Nat := 118140960795 + 4881458 * 2 ^ 59
def prefixEnd_4881458 : Nat := 4983230072969 + 3 ^ 40 * 4881458 * 2
def baseEnd_4881458 : Nat := 92834601805009907660207

theorem tailTrace_4881458 : CollatzResearch.WordTrace tailWord_4881458 prefixEnd_4881458 92834601805009907660207 := by
  unfold tailWord_4881458
  simp only [CollatzResearch.WordTrace]
  refine ⟨44510349987329706874581257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118694266632879218332216685 44510349987329706874581257)
  ·
    refine ⟨33382762490497280155935943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44510349987329706874581257 33382762490497280155935943)
    ·
      refine ⟨50074143735745920233903915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33382762490497280155935943 50074143735745920233903915)
      ·
        refine ⟨75111215603618880350855873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50074143735745920233903915 75111215603618880350855873)
        ·
          refine ⟨56333411702714160263141905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75111215603618880350855873 56333411702714160263141905)
          ·
            refine ⟨42250058777035620197356429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56333411702714160263141905 42250058777035620197356429)
            ·
              refine ⟨15843772041388357574008661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42250058777035620197356429 15843772041388357574008661)
              ·
                refine ⟨92834601805009907660207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15843772041388357574008661 92834601805009907660207)
                ·
                  rfl

theorem cell23_4881458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 9].length) (baseStart_4881458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881458 prefixEnd_4881458 := by exact prefixLift 4881458
  have htrace : WordTrace (prefixWord ++ tailWord_4881458) baseStart_4881458 baseEnd_4881458 := by
    simpa [prefixWord, tailWord_4881458, baseEnd_4881458] using wordTrace_append hprefix tailTrace_4881458
  have hstable : (prefixWord ++ tailWord_4881458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881458).length < 2 ^ (prefixWord ++ tailWord_4881458).sum := by decide
  have hdescent : baseEnd_4881458 < baseStart_4881458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881462 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 4, 4]
def baseStart_4881462 : Nat := 118140960795 + 4881462 * 2 ^ 59
def prefixEnd_4881462 : Nat := 4983230072969 + 3 ^ 40 * 4881462 * 2
def baseEnd_4881462 : Nat := 835512100885961830391857

theorem tailTrace_4881462 : CollatzResearch.WordTrace tailWord_4881462 prefixEnd_4881462 835512100885961830391857 := by
  unfold tailWord_4881462
  simp only [CollatzResearch.WordTrace]
  refine ⟨11127596615081521011341915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118694363894202890787647093 11127596615081521011341915)
  ·
    refine ⟨16691394922622281517012873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11127596615081521011341915 16691394922622281517012873)
    ·
      refine ⟨12518546191966711137759655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16691394922622281517012873 12518546191966711137759655)
      ·
        refine ⟨18777819287950066706639483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12518546191966711137759655 18777819287950066706639483)
        ·
          refine ⟨28166728931925100059959225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18777819287950066706639483 28166728931925100059959225)
          ·
            refine ⟨21125046698943825044969419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28166728931925100059959225 21125046698943825044969419)
            ·
              refine ⟨31687570048415737567454129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21125046698943825044969419 31687570048415737567454129)
              ·
                refine ⟨23765677536311803175590597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31687570048415737567454129 23765677536311803175590597)
                ·
                  refine ⟨4456064538058463095423237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23765677536311803175590597 4456064538058463095423237)
                  ·
                    refine ⟨835512100885961830391857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4456064538058463095423237 835512100885961830391857)
                    ·
                      rfl

theorem cell23_4881462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_4881462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881462 prefixEnd_4881462 := by exact prefixLift 4881462
  have htrace : WordTrace (prefixWord ++ tailWord_4881462) baseStart_4881462 baseEnd_4881462 := by
    simpa [prefixWord, tailWord_4881462, baseEnd_4881462] using wordTrace_append hprefix tailTrace_4881462
  have hstable : (prefixWord ++ tailWord_4881462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881462).length < 2 ^ (prefixWord ++ tailWord_4881462).sum := by decide
  have hdescent : baseEnd_4881462 < baseStart_4881462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881495 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 2, 7, 2]
def baseStart_4881495 : Nat := 118140960795 + 4881495 * 2 ^ 59
def prefixEnd_4881495 : Nat := 4983230072969 + 3 ^ 40 * 4881495 * 2
def baseEnd_4881495 : Nat := 2506553247519483862062919

theorem tailTrace_4881495 : CollatzResearch.WordTrace tailWord_4881495 prefixEnd_4881495 2506553247519483862062919 := by
  unfold tailWord_4881495
  simp only [CollatzResearch.WordTrace]
  refine ⟨178042749450184782817421939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118695166300123188544947959 178042749450184782817421939)
  ·
    refine ⟨267064124175277174226132909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178042749450184782817421939 267064124175277174226132909)
    ·
      refine ⟨100149046565728940334799841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267064124175277174226132909 100149046565728940334799841)
      ·
        refine ⟨75111784924296705251099881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100149046565728940334799841 75111784924296705251099881)
        ·
          refine ⟨56333838693222528938324911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75111784924296705251099881 56333838693222528938324911)
          ·
            refine ⟨84500758039833793407487367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56333838693222528938324911 84500758039833793407487367)
            ·
              refine ⟨126751137059750690111231051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84500758039833793407487367 126751137059750690111231051)
              ·
                refine ⟨190126705589626035166846577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126751137059750690111231051 190126705589626035166846577)
                ·
                  refine ⟨142595029192219526375134933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190126705589626035166846577 142595029192219526375134933)
                  ·
                    refine ⟨3342070996692645149417225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 142595029192219526375134933 3342070996692645149417225)
                    ·
                      refine ⟨2506553247519483862062919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3342070996692645149417225 2506553247519483862062919)
                      ·
                        rfl

theorem cell23_4881495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_4881495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881495 prefixEnd_4881495 := by exact prefixLift 4881495
  have htrace : WordTrace (prefixWord ++ tailWord_4881495) baseStart_4881495 baseEnd_4881495 := by
    simpa [prefixWord, tailWord_4881495, baseEnd_4881495] using wordTrace_append hprefix tailTrace_4881495
  have hstable : (prefixWord ++ tailWord_4881495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881495).length < 2 ^ (prefixWord ++ tailWord_4881495).sum := by decide
  have hdescent : baseEnd_4881495 < baseStart_4881495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881498 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5]
def baseStart_4881498 : Nat := 118140960795 + 4881498 * 2 ^ 59
def prefixEnd_4881498 : Nat := 4983230072969 + 3 ^ 40 * 4881498 * 2
def baseEnd_4881498 : Nat := 2506554787961447350325405

theorem tailTrace_4881498 : CollatzResearch.WordTrace tailWord_4881498 prefixEnd_4881498 2506554787961447350325405 := by
  unfold tailWord_4881498
  simp only [CollatzResearch.WordTrace]
  refine ⟨44510714717293478582445287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118695239246115942886520765 44510714717293478582445287)
  ·
    refine ⟨66766072075940217873667931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44510714717293478582445287 66766072075940217873667931)
    ·
      refine ⟨100149108113910326810501897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66766072075940217873667931 100149108113910326810501897)
      ·
        refine ⟨75111831085432745107876423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100149108113910326810501897 75111831085432745107876423)
        ·
          refine ⟨112667746628149117661814635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75111831085432745107876423 112667746628149117661814635)
          ·
            refine ⟨169001619942223676492721953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112667746628149117661814635 169001619942223676492721953)
            ·
              refine ⟨126751214956667757369541465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169001619942223676492721953 126751214956667757369541465)
              ·
                refine ⟨95063411217500818027156099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126751214956667757369541465 95063411217500818027156099)
                ·
                  refine ⟨142595116826251227040734149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95063411217500818027156099 142595116826251227040734149)
                  ·
                    refine ⟨26736584404922105070137653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 142595116826251227040734149 26736584404922105070137653)
                    ·
                      refine ⟨2506554787961447350325405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26736584404922105070137653 2506554787961447350325405)
                      ·
                        rfl

theorem cell23_4881498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_4881498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881498 prefixEnd_4881498 := by exact prefixLift 4881498
  have htrace : WordTrace (prefixWord ++ tailWord_4881498) baseStart_4881498 baseEnd_4881498 := by
    simpa [prefixWord, tailWord_4881498, baseEnd_4881498] using wordTrace_append hprefix tailTrace_4881498
  have hstable : (prefixWord ++ tailWord_4881498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881498).length < 2 ^ (prefixWord ++ tailWord_4881498).sum := by decide
  have hdescent : baseEnd_4881498 < baseStart_4881498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881506 : List Nat := [3, 3, 2, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_4881506 : Nat := 118140960795 + 4881506 * 2 ^ 59
def prefixEnd_4881506 : Nat := 4983230072969 + 3 ^ 40 * 4881506 * 2
def baseEnd_4881506 : Nat := 2506558895806683319025369

theorem tailTrace_4881506 : CollatzResearch.WordTrace tailWord_4881506 prefixEnd_4881506 2506558895806683319025369 := by
  unfold tailWord_4881506
  simp only [CollatzResearch.WordTrace]
  refine ⟨44510787663286232924018093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118695433768763287797381581 44510787663286232924018093)
  ·
    refine ⟨16691545373732337346506785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44510787663286232924018093 16691545373732337346506785)
    ·
      refine ⟨12518659030299253009880089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16691545373732337346506785 12518659030299253009880089)
      ·
        refine ⟨9388994272724439757410067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12518659030299253009880089 9388994272724439757410067)
        ·
          refine ⟨14083491409086659636115101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9388994272724439757410067 14083491409086659636115101)
          ·
            refine ⟨5281309278407497363543163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14083491409086659636115101 5281309278407497363543163)
            ·
              refine ⟨7921963917611246045314745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5281309278407497363543163 7921963917611246045314745)
              ·
                refine ⟨5941472938208434533986059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7921963917611246045314745 5941472938208434533986059)
                ·
                  refine ⟨8912209407312651800979089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5941472938208434533986059 8912209407312651800979089)
                  ·
                    refine ⟨6684157055484488850734317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8912209407312651800979089 6684157055484488850734317)
                    ·
                      refine ⟨2506558895806683319025369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6684157055484488850734317 2506558895806683319025369)
                      ·
                        rfl

theorem cell23_4881506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_4881506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881506 prefixEnd_4881506 := by exact prefixLift 4881506
  have htrace : WordTrace (prefixWord ++ tailWord_4881506) baseStart_4881506 baseEnd_4881506 := by
    simpa [prefixWord, tailWord_4881506, baseEnd_4881506] using wordTrace_append hprefix tailTrace_4881506
  have hstable : (prefixWord ++ tailWord_4881506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881506).length < 2 ^ (prefixWord ++ tailWord_4881506).sum := by decide
  have hdescent : baseEnd_4881506 < baseStart_4881506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881508 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 1, 2, 8]
def baseStart_4881508 : Nat := 118140960795 + 4881508 * 2 ^ 59
def prefixEnd_4881508 : Nat := 4983230072969 + 3 ^ 40 * 4881508 * 2
def baseEnd_4881508 : Nat := 2506559922767992311200359

theorem tailTrace_4881508 : CollatzResearch.WordTrace tailWord_4881508 prefixEnd_4881508 2506559922767992311200359 := by
  unfold tailWord_4881508
  simp only [CollatzResearch.WordTrace]
  refine ⟨89021611799568843018822589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118695482399425124025096785 89021611799568843018822589)
  ·
    refine ⟨33383104424838316132058471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89021611799568843018822589 33383104424838316132058471)
    ·
      refine ⟨50074656637257474198087707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33383104424838316132058471 50074656637257474198087707)
      ·
        refine ⟨75111984955886211297131561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50074656637257474198087707 75111984955886211297131561)
        ·
          refine ⟨56333988716914658472848671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75111984955886211297131561 56333988716914658472848671)
          ·
            refine ⟨84500983075371987709273007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56333988716914658472848671 84500983075371987709273007)
            ·
              refine ⟨126751474613057981563909511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84500983075371987709273007 126751474613057981563909511)
              ·
                refine ⟨190127211919586972345864267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126751474613057981563909511 190127211919586972345864267)
                ·
                  refine ⟨285190817879380458518796401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190127211919586972345864267 285190817879380458518796401)
                  ·
                    refine ⟨213893113409535343889097301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 285190817879380458518796401 213893113409535343889097301)
                    ·
                      refine ⟨2506559922767992311200359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 213893113409535343889097301 2506559922767992311200359)
                      ·
                        rfl

theorem cell23_4881508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_4881508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881508 prefixEnd_4881508 := by exact prefixLift 4881508
  have htrace : WordTrace (prefixWord ++ tailWord_4881508) baseStart_4881508 baseEnd_4881508 := by
    simpa [prefixWord, tailWord_4881508, baseEnd_4881508] using wordTrace_append hprefix tailTrace_4881508
  have hstable : (prefixWord ++ tailWord_4881508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881508).length < 2 ^ (prefixWord ++ tailWord_4881508).sum := by decide
  have hdescent : baseEnd_4881508 < baseStart_4881508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881545 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 2, 4, 3]
def baseStart_4881545 : Nat := 118140960795 + 4881545 * 2 ^ 59
def prefixEnd_4881545 : Nat := 4983230072969 + 3 ^ 40 * 4881545 * 2
def baseEnd_4881545 : Nat := 2506578921552208666437689

theorem tailTrace_4881545 : CollatzResearch.WordTrace tailWord_4881545 prefixEnd_4881545 2506578921552208666437689 := by
  unfold tailWord_4881545
  simp only [CollatzResearch.WordTrace]
  refine ⟨178044573100003641356742089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118696382066669094237828059 178044573100003641356742089)
  ·
    refine ⟨133533429825002731017556567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178044573100003641356742089 133533429825002731017556567)
    ·
      refine ⟨200300144737504096526334851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133533429825002731017556567 200300144737504096526334851)
      ·
        refine ⟨300450217106256144789502277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200300144737504096526334851 300450217106256144789502277)
        ·
          refine ⟨56334415707423027148031677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 300450217106256144789502277 56334415707423027148031677)
          ·
            refine ⟨21125405890283635180511879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56334415707423027148031677 21125405890283635180511879)
            ·
              refine ⟨31688108835425452770767819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21125405890283635180511879 31688108835425452770767819)
              ·
                refine ⟨47532163253138179156151729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31688108835425452770767819 47532163253138179156151729)
                ·
                  refine ⟨35649122439853634367113797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47532163253138179156151729 35649122439853634367113797)
                  ·
                    refine ⟨6684210457472556443833837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35649122439853634367113797 6684210457472556443833837)
                    ·
                      refine ⟨2506578921552208666437689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6684210457472556443833837 2506578921552208666437689)
                      ·
                        rfl

theorem cell23_4881545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 4, 3].length) (baseStart_4881545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881545 prefixEnd_4881545 := by exact prefixLift 4881545
  have htrace : WordTrace (prefixWord ++ tailWord_4881545) baseStart_4881545 baseEnd_4881545 := by
    simpa [prefixWord, tailWord_4881545, baseEnd_4881545] using wordTrace_append hprefix tailTrace_4881545
  have hstable : (prefixWord ++ tailWord_4881545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881545).length < 2 ^ (prefixWord ++ tailWord_4881545).sum := by decide
  have hdescent : baseEnd_4881545 < baseStart_4881545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881548 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 11]
def baseStart_4881548 : Nat := 118140960795 + 4881548 * 2 ^ 59
def prefixEnd_4881548 : Nat := 4983230072969 + 3 ^ 40 * 4881548 * 2
def baseEnd_4881548 : Nat := 278508940221574683855575

theorem tailTrace_4881548 : CollatzResearch.WordTrace tailWord_4881548 prefixEnd_4881548 278508940221574683855575 := by
  unfold tailWord_4881548
  simp only [CollatzResearch.WordTrace]
  refine ⟨89022341259496386434550649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118696455012661848579400865 89022341259496386434550649)
  ·
    refine ⟨66766755944622289825912987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89022341259496386434550649 66766755944622289825912987)
    ·
      refine ⟨100150133916933434738869481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66766755944622289825912987 100150133916933434738869481)
      ·
        refine ⟨75112600437700076054152111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100150133916933434738869481 75112600437700076054152111)
        ·
          refine ⟨112668900656550114081228167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75112600437700076054152111 112668900656550114081228167)
          ·
            refine ⟨169003350984825171121842251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112668900656550114081228167 169003350984825171121842251)
            ·
              refine ⟨253505026477237756682763377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169003350984825171121842251 253505026477237756682763377)
              ·
                refine ⟨190128769857928317512072533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 253505026477237756682763377 190128769857928317512072533)
                ·
                  refine ⟨278508940221574683855575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 190128769857928317512072533 278508940221574683855575)
                  ·
                    rfl

theorem cell23_4881548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 11].length) (baseStart_4881548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881548 prefixEnd_4881548 := by exact prefixLift 4881548
  have htrace : WordTrace (prefixWord ++ tailWord_4881548) baseStart_4881548 baseEnd_4881548 := by
    simpa [prefixWord, tailWord_4881548, baseEnd_4881548] using wordTrace_append hprefix tailTrace_4881548
  have hstable : (prefixWord ++ tailWord_4881548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881548).length < 2 ^ (prefixWord ++ tailWord_4881548).sum := by decide
  have hdescent : baseEnd_4881548 < baseStart_4881548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881559 : List Nat := [1, 1, 3, 3, 3, 2, 2, 1, 1, 4, 2]
def baseStart_4881559 : Nat := 118140960795 + 4881559 * 2 ^ 59
def prefixEnd_4881559 : Nat := 4983230072969 + 3 ^ 40 * 4881559 * 2
def baseEnd_4881559 : Nat := 2506586110281371611662625

theorem tailTrace_4881559 : CollatzResearch.WordTrace tailWord_4881559 prefixEnd_4881559 2506586110281371611662625 := by
  unfold tailWord_4881559
  simp only [CollatzResearch.WordTrace]
  refine ⟨178045083721952921747751731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118696722481301947831834487 178045083721952921747751731)
  ·
    refine ⟨267067625582929382621627597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178045083721952921747751731 267067625582929382621627597)
    ·
      refine ⟨100150359593598518483110349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267067625582929382621627597 100150359593598518483110349)
      ·
        refine ⟨37556384847599444431166381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100150359593598518483110349 37556384847599444431166381)
        ·
          refine ⟨14083644317849791661687393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37556384847599444431166381 14083644317849791661687393)
          ·
            refine ⟨10562733238387343746265545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14083644317849791661687393 10562733238387343746265545)
            ·
              refine ⟨7922049928790507809699159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10562733238387343746265545 7922049928790507809699159)
              ·
                refine ⟨11883074893185761714548739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7922049928790507809699159 11883074893185761714548739)
                ·
                  refine ⟨17824612339778642571823109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11883074893185761714548739 17824612339778642571823109)
                  ·
                    refine ⟨3342114813708495482216833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17824612339778642571823109 3342114813708495482216833)
                    ·
                      refine ⟨2506586110281371611662625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3342114813708495482216833 2506586110281371611662625)
                      ·
                        rfl

theorem cell23_4881559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_4881559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881559 prefixEnd_4881559 := by exact prefixLift 4881559
  have htrace : WordTrace (prefixWord ++ tailWord_4881559) baseStart_4881559 baseEnd_4881559 := by
    simpa [prefixWord, tailWord_4881559, baseEnd_4881559] using wordTrace_append hprefix tailTrace_4881559
  have hstable : (prefixWord ++ tailWord_4881559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881559).length < 2 ^ (prefixWord ++ tailWord_4881559).sum := by decide
  have hdescent : baseEnd_4881559 < baseStart_4881559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881565 : List Nat := [1, 4, 2, 1, 1, 2, 3, 2, 7]
def baseStart_4881565 : Nat := 118140960795 + 4881565 * 2 ^ 59
def prefixEnd_4881565 : Nat := 4983230072969 + 3 ^ 40 * 4881565 * 2
def baseEnd_4881565 : Nat := 278509910129477620909733

theorem tailTrace_4881565 : CollatzResearch.WordTrace tailWord_4881565 prefixEnd_4881565 278509910129477620909733 := by
  unfold tailWord_4881565
  simp only [CollatzResearch.WordTrace]
  refine ⟨178045302559931184772470149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118696868373287456514980099 178045302559931184772470149)
  ·
    refine ⟨33383494229987097144838153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178045302559931184772470149 33383494229987097144838153)
    ·
      refine ⟨25037620672490322858628615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33383494229987097144838153 25037620672490322858628615)
      ·
        refine ⟨37556431008735484287942923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25037620672490322858628615 37556431008735484287942923)
        ·
          refine ⟨56334646513103226431914385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37556431008735484287942923 56334646513103226431914385)
          ·
            refine ⟨42250984884827419823935789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56334646513103226431914385 42250984884827419823935789)
            ·
              refine ⟨15844119331810282433975921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42250984884827419823935789 15844119331810282433975921)
              ·
                refine ⟨11883089498857711825481941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15844119331810282433975921 11883089498857711825481941)
                ·
                  refine ⟨278509910129477620909733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11883089498857711825481941 278509910129477620909733)
                  ·
                    rfl

theorem cell23_4881565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_4881565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881565 prefixEnd_4881565 := by exact prefixLift 4881565
  have htrace : WordTrace (prefixWord ++ tailWord_4881565) baseStart_4881565 baseEnd_4881565 := by
    simpa [prefixWord, tailWord_4881565, baseEnd_4881565] using wordTrace_append hprefix tailTrace_4881565
  have hstable : (prefixWord ++ tailWord_4881565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881565).length < 2 ^ (prefixWord ++ tailWord_4881565).sum := by decide
  have hdescent : baseEnd_4881565 < baseStart_4881565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881615 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 4]
def baseStart_4881615 : Nat := 118140960795 + 4881615 * 2 ^ 59
def prefixEnd_4881615 : Nat := 4983230072969 + 3 ^ 40 * 4881615 * 2
def baseEnd_4881615 : Nat := 2506614865198023392562367

theorem tailTrace_4881615 : CollatzResearch.WordTrace tailWord_4881615 prefixEnd_4881615 2506614865198023392562367 := by
  unfold tailWord_4881615
  simp only [CollatzResearch.WordTrace]
  refine ⟨178047126209750043311790299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118698084139833362207860199 178047126209750043311790299)
  ·
    refine ⟨267070689314625064967685449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178047126209750043311790299 267070689314625064967685449)
    ·
      refine ⟨200303016985968798725764087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267070689314625064967685449 200303016985968798725764087)
      ·
        refine ⟨300454525478953198088646131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200303016985968798725764087 300454525478953198088646131)
        ·
          refine ⟨450681788218429797132969197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300454525478953198088646131 450681788218429797132969197)
          ·
            refine ⟨169005670581911173924863449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 450681788218429797132969197 169005670581911173924863449)
            ·
              refine ⟨126754252936433380443647587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169005670581911173924863449 126754252936433380443647587)
              ·
                refine ⟨190131379404650070665471381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126754252936433380443647587 190131379404650070665471381)
                ·
                  refine ⟨8912408409592972062443971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 190131379404650070665471381 8912408409592972062443971)
                  ·
                    refine ⟨13368612614389458093665957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8912408409592972062443971 13368612614389458093665957)
                    ·
                      refine ⟨2506614865198023392562367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13368612614389458093665957 2506614865198023392562367)
                      ·
                        rfl

theorem cell23_4881615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 4].length) (baseStart_4881615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881615 prefixEnd_4881615 := by exact prefixLift 4881615
  have htrace : WordTrace (prefixWord ++ tailWord_4881615) baseStart_4881615 baseEnd_4881615 := by
    simpa [prefixWord, tailWord_4881615, baseEnd_4881615] using wordTrace_append hprefix tailTrace_4881615
  have hstable : (prefixWord ++ tailWord_4881615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881615).length < 2 ^ (prefixWord ++ tailWord_4881615).sum := by decide
  have hdescent : baseEnd_4881615 < baseStart_4881615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881705 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 4, 5, 4]
def baseStart_4881705 : Nat := 118140960795 + 4881705 * 2 ^ 59
def prefixEnd_4881705 : Nat := 4983230072969 + 3 ^ 40 * 4881705 * 2
def baseEnd_4881705 : Nat := 2506661078456928040436953

theorem tailTrace_4881705 : CollatzResearch.WordTrace tailWord_4881705 prefixEnd_4881705 2506661078456928040436953 := by
  unfold tailWord_4881705
  simp only [CollatzResearch.WordTrace]
  refine ⟨178050408779423988682566569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118700272519615992455044379 178050408779423988682566569)
  ·
    refine ⟨133537806584567991511924927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178050408779423988682566569 133537806584567991511924927)
    ·
      refine ⟨200306709876851987267887391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133537806584567991511924927 200306709876851987267887391)
      ·
        refine ⟨300460064815277980901831087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200306709876851987267887391 300460064815277980901831087)
        ·
          refine ⟨450690097222916971352746631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300460064815277980901831087 450690097222916971352746631)
          ·
            refine ⟨676035145834375457029119947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450690097222916971352746631 676035145834375457029119947)
            ·
              refine ⟨1014052718751563185543679921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676035145834375457029119947 1014052718751563185543679921)
              ·
                refine ⟨760539539063672389157759941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1014052718751563185543679921 760539539063672389157759941)
                ·
                  refine ⟨142601163574438572967079989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 760539539063672389157759941 142601163574438572967079989)
                  ·
                    refine ⟨13368859085103616215663749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 142601163574438572967079989 13368859085103616215663749)
                    ·
                      refine ⟨2506661078456928040436953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13368859085103616215663749 2506661078456928040436953)
                      ·
                        rfl

theorem cell23_4881705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 5, 4].length) (baseStart_4881705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881705 prefixEnd_4881705 := by exact prefixLift 4881705
  have htrace : WordTrace (prefixWord ++ tailWord_4881705) baseStart_4881705 baseEnd_4881705 := by
    simpa [prefixWord, tailWord_4881705, baseEnd_4881705] using wordTrace_append hprefix tailTrace_4881705
  have hstable : (prefixWord ++ tailWord_4881705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881705).length < 2 ^ (prefixWord ++ tailWord_4881705).sum := by decide
  have hdescent : baseEnd_4881705 < baseStart_4881705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881716 : List Nat := [2, 5, 1, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_4881716 : Nat := 118140960795 + 4881716 * 2 ^ 59
def prefixEnd_4881716 : Nat := 4983230072969 + 3 ^ 40 * 4881716 * 2
def baseEnd_4881716 : Nat := 2506666726744127497399403

theorem tailTrace_4881716 : CollatzResearch.WordTrace tailWord_4881716 prefixEnd_4881716 2506666726744127497399403 := by
  unfold tailWord_4881716
  simp only [CollatzResearch.WordTrace]
  refine ⟨89025404991192068780608501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118700539988256091707478001 89025404991192068780608501)
  ·
    refine ⟨8346131717924256448182047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89025404991192068780608501 8346131717924256448182047)
    ·
      refine ⟨12519197576886384672273071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8346131717924256448182047 12519197576886384672273071)
      ·
        refine ⟨18778796365329577008409607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12519197576886384672273071 18778796365329577008409607)
        ·
          refine ⟨28168194547994365512614411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18778796365329577008409607 28168194547994365512614411)
          ·
            refine ⟨42252291821991548268921617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28168194547994365512614411 42252291821991548268921617)
            ·
              refine ⟨31689218866493661201691213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42252291821991548268921617 31689218866493661201691213)
              ·
                refine ⟨11883457074935122950634205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31689218866493661201691213 11883457074935122950634205)
                ·
                  refine ⟨4456296403100671106487827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11883457074935122950634205 4456296403100671106487827)
                  ·
                    refine ⟨6684444604651006659731741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4456296403100671106487827 6684444604651006659731741)
                    ·
                      refine ⟨2506666726744127497399403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6684444604651006659731741 2506666726744127497399403)
                      ·
                        rfl

theorem cell23_4881716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_4881716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881716 prefixEnd_4881716 := by exact prefixLift 4881716
  have htrace : WordTrace (prefixWord ++ tailWord_4881716) baseStart_4881716 baseEnd_4881716 := by
    simpa [prefixWord, tailWord_4881716, baseEnd_4881716] using wordTrace_append hprefix tailTrace_4881716
  have hstable : (prefixWord ++ tailWord_4881716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881716).length < 2 ^ (prefixWord ++ tailWord_4881716).sum := by decide
  have hdescent : baseEnd_4881716 < baseStart_4881716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881722 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4]
def baseStart_4881722 : Nat := 118140960795 + 4881722 * 2 ^ 59
def prefixEnd_4881722 : Nat := 4983230072969 + 3 ^ 40 * 4881722 * 2
def baseEnd_4881722 : Nat := 2506669807628054473924375

theorem tailTrace_4881722 : CollatzResearch.WordTrace tailWord_4881722 prefixEnd_4881722 2506669807628054473924375 := by
  unfold tailWord_4881722
  simp only [CollatzResearch.WordTrace]
  refine ⟨44512757205090600146483855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118700685880241600390623613 44512757205090600146483855)
  ·
    refine ⟨66769135807635900219725783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44512757205090600146483855 66769135807635900219725783)
    ·
      refine ⟨100153703711453850329588675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66769135807635900219725783 100153703711453850329588675)
      ·
        refine ⟨150230555567180775494383013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100153703711453850329588675 150230555567180775494383013)
        ·
          refine ⟨28168229168846395405196815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150230555567180775494383013 28168229168846395405196815)
          ·
            refine ⟨42252343753269593107795223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28168229168846395405196815 42252343753269593107795223)
            ·
              refine ⟨63378515629904389661692835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42252343753269593107795223 63378515629904389661692835)
              ·
                refine ⟨95067773444856584492539253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63378515629904389661692835 95067773444856584492539253)
                ·
                  refine ⟨8912603760455304796175555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95067773444856584492539253 8912603760455304796175555)
                  ·
                    refine ⟨13368905640682957194263333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8912603760455304796175555 13368905640682957194263333)
                    ·
                      refine ⟨2506669807628054473924375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13368905640682957194263333 2506669807628054473924375)
                      ·
                        rfl

theorem cell23_4881722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_4881722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881722 prefixEnd_4881722 := by exact prefixLift 4881722
  have htrace : WordTrace (prefixWord ++ tailWord_4881722) baseStart_4881722 baseEnd_4881722 := by
    simpa [prefixWord, tailWord_4881722, baseEnd_4881722] using wordTrace_append hprefix tailTrace_4881722
  have hstable : (prefixWord ++ tailWord_4881722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881722).length < 2 ^ (prefixWord ++ tailWord_4881722).sum := by decide
  have hdescent : baseEnd_4881722 < baseStart_4881722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881752 : List Nat := [2, 1, 2, 2, 1, 1, 3, 4, 1, 2, 4]
def baseStart_4881752 : Nat := 118140960795 + 4881752 * 2 ^ 59
def prefixEnd_4881752 : Nat := 4983230072969 + 3 ^ 40 * 4881752 * 2
def baseEnd_4881752 : Nat := 2506685212047689356549237

theorem tailTrace_4881752 : CollatzResearch.WordTrace tailWord_4881752 prefixEnd_4881752 2506685212047689356549237 := by
  unfold tailWord_4881752
  simp only [CollatzResearch.WordTrace]
  refine ⟨89026061505126857854763755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118701415340169143806351673 89026061505126857854763755)
  ·
    refine ⟨133539092257690286782145633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89026061505126857854763755 133539092257690286782145633)
    ·
      refine ⟨100154319193267715086609225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133539092257690286782145633 100154319193267715086609225)
      ·
        refine ⟨75115739394950786314956919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100154319193267715086609225 75115739394950786314956919)
        ·
          refine ⟨112673609092426179472435379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75115739394950786314956919 112673609092426179472435379)
          ·
            refine ⟨169010413638639269208653069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112673609092426179472435379 169010413638639269208653069)
            ·
              refine ⟨63378905114489725953244901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169010413638639269208653069 63378905114489725953244901)
              ·
                refine ⟨11883544708966823616233419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63378905114489725953244901 11883544708966823616233419)
                ·
                  refine ⟨17825317063450235424350129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11883544708966823616233419 17825317063450235424350129)
                  ·
                    refine ⟨13368987797587676568262597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17825317063450235424350129 13368987797587676568262597)
                    ·
                      refine ⟨2506685212047689356549237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13368987797587676568262597 2506685212047689356549237)
                      ·
                        rfl

theorem cell23_4881752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_4881752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881752 prefixEnd_4881752 := by exact prefixLift 4881752
  have htrace : WordTrace (prefixWord ++ tailWord_4881752) baseStart_4881752 baseEnd_4881752 := by
    simpa [prefixWord, tailWord_4881752, baseEnd_4881752] using wordTrace_append hprefix tailTrace_4881752
  have hstable : (prefixWord ++ tailWord_4881752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881752).length < 2 ^ (prefixWord ++ tailWord_4881752).sum := by decide
  have hdescent : baseEnd_4881752 < baseStart_4881752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881762 : List Nat := [3, 3, 2, 1, 1, 1, 12]
def baseStart_4881762 : Nat := 118140960795 + 4881762 * 2 ^ 59
def prefixEnd_4881762 : Nat := 4983230072969 + 3 ^ 40 * 4881762 * 2
def baseEnd_4881762 : Nat := 30946794405607831079311

theorem tailTrace_4881762 : CollatzResearch.WordTrace tailWord_4881762 prefixEnd_4881762 30946794405607831079311 := by
  unfold tailWord_4881762
  simp only [CollatzResearch.WordTrace]
  refine ⟨44513121935054371854347885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118701658493478324944927693 44513121935054371854347885)
  ·
    refine ⟨16692420725645389445380457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44513121935054371854347885 16692420725645389445380457)
    ·
      refine ⟨12519315544234042084035343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16692420725645389445380457 12519315544234042084035343)
      ·
        refine ⟨18778973316351063126053015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12519315544234042084035343 18778973316351063126053015)
        ·
          refine ⟨28168459974526594689079523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18778973316351063126053015 28168459974526594689079523)
          ·
            refine ⟨42252689961789892033619285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28168459974526594689079523 42252689961789892033619285)
            ·
              refine ⟨30946794405607831079311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 42252689961789892033619285 30946794405607831079311)
              ·
                rfl

theorem cell23_4881762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 12].length) (baseStart_4881762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881762 prefixEnd_4881762 := by exact prefixLift 4881762
  have htrace : WordTrace (prefixWord ++ tailWord_4881762) baseStart_4881762 baseEnd_4881762 := by
    simpa [prefixWord, tailWord_4881762, baseEnd_4881762] using wordTrace_append hprefix tailTrace_4881762
  have hstable : (prefixWord ++ tailWord_4881762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881762).length < 2 ^ (prefixWord ++ tailWord_4881762).sum := by decide
  have hdescent : baseEnd_4881762 < baseStart_4881762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881773 : List Nat := [1, 5, 1, 1, 1, 4, 2, 1, 3, 2, 2]
def baseStart_4881773 : Nat := 118140960795 + 4881773 * 2 ^ 59
def prefixEnd_4881773 : Nat := 4983230072969 + 3 ^ 40 * 4881773 * 2
def baseEnd_4881773 : Nat := 2506695995141433774386641

theorem tailTrace_4881773 : CollatzResearch.WordTrace tailWord_4881773 prefixEnd_4881773 2506695995141433774386641 := by
  unfold tailWord_4881773
  simp only [CollatzResearch.WordTrace]
  refine ⟨178052888943177636296041973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118701925962118424197361315 178052888943177636296041973)
  ·
    refine ⟨16692458338422903402753935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 178052888943177636296041973 16692458338422903402753935)
    ·
      refine ⟨25038687507634355104130903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16692458338422903402753935 25038687507634355104130903)
      ·
        refine ⟨37558031261451532656196355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25038687507634355104130903 37558031261451532656196355)
        ·
          refine ⟨56337046892177298984294533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37558031261451532656196355 56337046892177298984294533)
          ·
            refine ⟨10563196292283243559555225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56337046892177298984294533 10563196292283243559555225)
            ·
              refine ⟨7922397219212432669666419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10563196292283243559555225 7922397219212432669666419)
              ·
                refine ⟨11883595828818649004499629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7922397219212432669666419 11883595828818649004499629)
                ·
                  refine ⟨4456348435806993376687361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11883595828818649004499629 4456348435806993376687361)
                  ·
                    refine ⟨3342261326855245032515521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4456348435806993376687361 3342261326855245032515521)
                    ·
                      refine ⟨2506695995141433774386641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3342261326855245032515521 2506695995141433774386641)
                      ·
                        rfl

theorem cell23_4881773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_4881773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881773 prefixEnd_4881773 := by exact prefixLift 4881773
  have htrace : WordTrace (prefixWord ++ tailWord_4881773) baseStart_4881773 baseEnd_4881773 := by
    simpa [prefixWord, tailWord_4881773, baseEnd_4881773] using wordTrace_append hprefix tailTrace_4881773
  have hstable : (prefixWord ++ tailWord_4881773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881773).length < 2 ^ (prefixWord ++ tailWord_4881773).sum := by decide
  have hdescent : baseEnd_4881773 < baseStart_4881773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881790 : List Nat := [4, 2, 3, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_4881790 : Nat := 118140960795 + 4881790 * 2 ^ 59
def prefixEnd_4881790 : Nat := 4983230072969 + 3 ^ 40 * 4881790 * 2
def baseEnd_4881790 : Nat := 2506704724312560207874063

theorem tailTrace_4881790 : CollatzResearch.WordTrace tailWord_4881790 prefixEnd_4881790 2506704724312560207874063 := by
  unfold tailWord_4881790
  simp only [CollatzResearch.WordTrace]
  refine ⟨22256688623014506024926353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118702339322744032132940549 22256688623014506024926353)
  ·
    refine ⟨16692516467260879518694765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22256688623014506024926353 16692516467260879518694765)
    ·
      refine ⟨6259693675222829819510537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16692516467260879518694765 6259693675222829819510537)
      ·
        refine ⟨4694770256417122364632903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6259693675222829819510537 4694770256417122364632903)
        ·
          refine ⟨7042155384625683546949355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4694770256417122364632903 7042155384625683546949355)
          ·
            refine ⟨10563233076938525320424033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7042155384625683546949355 10563233076938525320424033)
            ·
              refine ⟨7922424807703893990318025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10563233076938525320424033 7922424807703893990318025)
              ·
                refine ⟨5941818605777920492738519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7922424807703893990318025 5941818605777920492738519)
                ·
                  refine ⟨8912727908666880739107779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5941818605777920492738519 8912727908666880739107779)
                  ·
                    refine ⟨13369091863000321108661669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8912727908666880739107779 13369091863000321108661669)
                    ·
                      refine ⟨2506704724312560207874063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13369091863000321108661669 2506704724312560207874063)
                      ·
                        rfl

theorem cell23_4881790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_4881790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881790 prefixEnd_4881790 := by exact prefixLift 4881790
  have htrace : WordTrace (prefixWord ++ tailWord_4881790) baseStart_4881790 baseEnd_4881790 := by
    simpa [prefixWord, tailWord_4881790, baseEnd_4881790] using wordTrace_append hprefix tailTrace_4881790
  have hstable : (prefixWord ++ tailWord_4881790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881790).length < 2 ^ (prefixWord ++ tailWord_4881790).sum := by decide
  have hdescent : baseEnd_4881790 < baseStart_4881790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881793 : List Nat := [1, 2, 4, 3, 2, 1, 2, 2, 1, 2, 3]
def baseStart_4881793 : Nat := 118140960795 + 4881793 * 2 ^ 59
def prefixEnd_4881793 : Nat := 4983230072969 + 3 ^ 40 * 4881793 * 2
def baseEnd_4881793 : Nat := 2506706264754523696136549

theorem tailTrace_4881793 : CollatzResearch.WordTrace tailWord_4881793 prefixEnd_4881793 2506706264754523696136549 := by
  unfold tailWord_4881793
  simp only [CollatzResearch.WordTrace]
  refine ⟨178053618403105179711770033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118702412268736786474513355 178053618403105179711770033)
  ·
    refine ⟨133540213802328884783827525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178053618403105179711770033 133540213802328884783827525)
    ·
      refine ⟨25038790087936665896967661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133540213802328884783827525 25038790087936665896967661)
      ·
        refine ⟨9389546282976249711362873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25038790087936665896967661 9389546282976249711362873)
        ·
          refine ⟨7042159712232187283522155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9389546282976249711362873 7042159712232187283522155)
          ·
            refine ⟨10563239568348280925283233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7042159712232187283522155 10563239568348280925283233)
            ·
              refine ⟨7922429676261210693962425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10563239568348280925283233 7922429676261210693962425)
              ·
                refine ⟨5941822257195908020471819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7922429676261210693962425 5941822257195908020471819)
                ·
                  refine ⟨8912733385793862030707729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5941822257195908020471819 8912733385793862030707729)
                  ·
                    refine ⟨6684550039345396523030797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8912733385793862030707729 6684550039345396523030797)
                    ·
                      refine ⟨2506706264754523696136549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6684550039345396523030797 2506706264754523696136549)
                      ·
                        rfl

theorem cell23_4881793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_4881793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881793 prefixEnd_4881793 := by exact prefixLift 4881793
  have htrace : WordTrace (prefixWord ++ tailWord_4881793) baseStart_4881793 baseEnd_4881793 := by
    simpa [prefixWord, tailWord_4881793, baseEnd_4881793] using wordTrace_append hprefix tailTrace_4881793
  have hstable : (prefixWord ++ tailWord_4881793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881793).length < 2 ^ (prefixWord ++ tailWord_4881793).sum := by decide
  have hdescent : baseEnd_4881793 < baseStart_4881793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881829 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 5, 4, 2]
def baseStart_4881829 : Nat := 118140960795 + 4881829 * 2 ^ 59
def prefixEnd_4881829 : Nat := 4983230072969 + 3 ^ 40 * 4881829 * 2
def baseEnd_4881829 : Nat := 2506724750058085555286383

theorem tailTrace_4881829 : CollatzResearch.WordTrace tailWord_4881829 prefixEnd_4881829 2506724750058085555286383 := by
  unfold tailWord_4881829
  simp only [CollatzResearch.WordTrace]
  refine ⟨178054931430974757860080541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118703287620649838573387027 178054931430974757860080541)
  ·
    refine ⟨66770599286615534197530203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178054931430974757860080541 66770599286615534197530203)
    ·
      refine ⟨100155898929923301296295305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66770599286615534197530203 100155898929923301296295305)
      ·
        refine ⟨75116924197442475972221479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100155898929923301296295305 75116924197442475972221479)
        ·
          refine ⟨112675386296163713958332219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75116924197442475972221479 112675386296163713958332219)
          ·
            refine ⟨169013079444245570937498329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112675386296163713958332219 169013079444245570937498329)
            ·
              refine ⟨126759809583184178203123747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169013079444245570937498329 126759809583184178203123747)
              ·
                refine ⟨190139714374776267304685621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126759809583184178203123747 190139714374776267304685621)
                ·
                  refine ⟨17825598222635275059814277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 190139714374776267304685621 17825598222635275059814277)
                  ·
                    refine ⟨3342299666744114073715177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17825598222635275059814277 3342299666744114073715177)
                    ·
                      refine ⟨2506724750058085555286383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3342299666744114073715177 2506724750058085555286383)
                      ·
                        rfl

theorem cell23_4881829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 4, 2].length) (baseStart_4881829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881829 prefixEnd_4881829 := by exact prefixLift 4881829
  have htrace : WordTrace (prefixWord ++ tailWord_4881829) baseStart_4881829 baseEnd_4881829 := by
    simpa [prefixWord, tailWord_4881829, baseEnd_4881829] using wordTrace_append hprefix tailTrace_4881829
  have hstable : (prefixWord ++ tailWord_4881829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881829).length < 2 ^ (prefixWord ++ tailWord_4881829).sum := by decide
  have hdescent : baseEnd_4881829 < baseStart_4881829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881919 : List Nat := [1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 4]
def baseStart_4881919 : Nat := 118140960795 + 4881919 * 2 ^ 59
def prefixEnd_4881919 : Nat := 4983230072969 + 3 ^ 40 * 4881919 * 2
def baseEnd_4881919 : Nat := 2506770963316990203160969

theorem tailTrace_4881919 : CollatzResearch.WordTrace tailWord_4881919 prefixEnd_4881919 2506770963316990203160969 := by
  unfold tailWord_4881919
  simp only [CollatzResearch.WordTrace]
  refine ⟨178058214000648703230856811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118705476000432468820571207 178058214000648703230856811)
  ·
    refine ⟨267087321000973054846285217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178058214000648703230856811 267087321000973054846285217)
    ·
      refine ⟨200315490750729791134713913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267087321000973054846285217 200315490750729791134713913)
      ·
        refine ⟨150236618063047343351035435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200315490750729791134713913 150236618063047343351035435)
        ·
          refine ⟨225354927094571015026553153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150236618063047343351035435 225354927094571015026553153)
          ·
            refine ⟨169016195320928261269914865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225354927094571015026553153 169016195320928261269914865)
            ·
              refine ⟨126762146490696195952436149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169016195320928261269914865 126762146490696195952436149)
              ·
                refine ⟨11883951233502768370540889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126762146490696195952436149 11883951233502768370540889)
                ·
                  refine ⟨8912963425127076277905667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11883951233502768370540889 8912963425127076277905667)
                  ·
                    refine ⟨13369445137690614416858501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8912963425127076277905667 13369445137690614416858501)
                    ·
                      refine ⟨2506770963316990203160969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13369445137690614416858501 2506770963316990203160969)
                      ·
                        rfl

theorem cell23_4881919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_4881919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881919 prefixEnd_4881919 := by exact prefixLift 4881919
  have htrace : WordTrace (prefixWord ++ tailWord_4881919) baseStart_4881919 baseEnd_4881919 := by
    simpa [prefixWord, tailWord_4881919, baseEnd_4881919] using wordTrace_append hprefix tailTrace_4881919
  have hstable : (prefixWord ++ tailWord_4881919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881919).length < 2 ^ (prefixWord ++ tailWord_4881919).sum := by decide
  have hdescent : baseEnd_4881919 < baseStart_4881919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881929 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 5, 4]
def baseStart_4881929 : Nat := 118140960795 + 4881929 * 2 ^ 59
def prefixEnd_4881929 : Nat := 4983230072969 + 3 ^ 40 * 4881929 * 2
def baseEnd_4881929 : Nat := 835592032707845054678641

theorem tailTrace_4881929 : CollatzResearch.WordTrace tailWord_4881929 prefixEnd_4881929 835592032707845054678641 := by
  unfold tailWord_4881929
  simp only [CollatzResearch.WordTrace]
  refine ⟨178058578730612474938720841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118705719153741649959147227 178058578730612474938720841)
  ·
    refine ⟨133543934047959356204040631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178058578730612474938720841 133543934047959356204040631)
    ·
      refine ⟨200315901071939034306060947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133543934047959356204040631 200315901071939034306060947)
      ·
        refine ⟨300473851607908551459091421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200315901071939034306060947 300473851607908551459091421)
        ·
          refine ⟨112677694352965706797159283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 300473851607908551459091421 112677694352965706797159283)
          ·
            refine ⟨169016541529448560195738925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112677694352965706797159283 169016541529448560195738925)
            ·
              refine ⟨63381203073543210073402097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169016541529448560195738925 63381203073543210073402097)
              ·
                refine ⟨47535902305157407555051573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63381203073543210073402097 47535902305157407555051573)
                ·
                  refine ⟨4456490841108506958286085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47535902305157407555051573 4456490841108506958286085)
                  ·
                    refine ⟨835592032707845054678641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4456490841108506958286085 835592032707845054678641)
                    ·
                      rfl

theorem cell23_4881929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 4].length) (baseStart_4881929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881929 prefixEnd_4881929 := by exact prefixLift 4881929
  have htrace : WordTrace (prefixWord ++ tailWord_4881929) baseStart_4881929 baseEnd_4881929 := by
    simpa [prefixWord, tailWord_4881929, baseEnd_4881929] using wordTrace_append hprefix tailTrace_4881929
  have hstable : (prefixWord ++ tailWord_4881929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881929).length < 2 ^ (prefixWord ++ tailWord_4881929).sum := by decide
  have hdescent : baseEnd_4881929 < baseStart_4881929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881949 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_4881949 : Nat := 118140960795 + 4881949 * 2 ^ 59
def prefixEnd_4881949 : Nat := 4983230072969 + 3 ^ 40 * 4881949 * 2
def baseEnd_4881949 : Nat := 2506786367736625085785831

theorem tailTrace_4881949 : CollatzResearch.WordTrace tailWord_4881949 prefixEnd_4881949 2506786367736625085785831 := by
  unfold tailWord_4881949
  simp only [CollatzResearch.WordTrace]
  refine ⟨178059308190540018354448901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118706205460360012236299267 178059308190540018354448901)
  ·
    refine ⟨33386120285726253441459169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178059308190540018354448901 33386120285726253441459169)
    ·
      refine ⟨25039590214294690081094377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33386120285726253441459169 25039590214294690081094377)
      ·
        refine ⟨18779692660721017560820783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25039590214294690081094377 18779692660721017560820783)
        ·
          refine ⟨28169538991081526341231175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18779692660721017560820783 28169538991081526341231175)
          ·
            refine ⟨42254308486622289511846763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28169538991081526341231175 42254308486622289511846763)
            ·
              refine ⟨63381462729933434267770145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42254308486622289511846763 63381462729933434267770145)
              ·
                refine ⟨47536097047450075700827609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63381462729933434267770145 47536097047450075700827609)
                ·
                  refine ⟨35652072785587556775620707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47536097047450075700827609 35652072785587556775620707)
                  ·
                    refine ⟨53478109178381335163431061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35652072785587556775620707 53478109178381335163431061)
                    ·
                      refine ⟨2506786367736625085785831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53478109178381335163431061 2506786367736625085785831)
                      ·
                        rfl

theorem cell23_4881949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_4881949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881949 prefixEnd_4881949 := by exact prefixLift 4881949
  have htrace : WordTrace (prefixWord ++ tailWord_4881949) baseStart_4881949 baseEnd_4881949 := by
    simpa [prefixWord, tailWord_4881949, baseEnd_4881949] using wordTrace_append hprefix tailTrace_4881949
  have hstable : (prefixWord ++ tailWord_4881949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881949).length < 2 ^ (prefixWord ++ tailWord_4881949).sum := by decide
  have hdescent : baseEnd_4881949 < baseStart_4881949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881969 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 1, 7, 3]
def baseStart_4881969 : Nat := 118140960795 + 4881969 * 2 ^ 59
def prefixEnd_4881969 : Nat := 4983230072969 + 3 ^ 40 * 4881969 * 2
def baseEnd_4881969 : Nat := 2506796637349715007535739

theorem tailTrace_4881969 : CollatzResearch.WordTrace tailWord_4881969 prefixEnd_4881969 2506796637349715007535739 := by
  unfold tailWord_4881969
  simp only [CollatzResearch.WordTrace]
  refine ⟨178060037650467561770176961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118706691766978374513451307 178060037650467561770176961)
  ·
    refine ⟨133545028237850671327632721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178060037650467561770176961 133545028237850671327632721)
    ·
      refine ⟨100158771178388003495724541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133545028237850671327632721 100158771178388003495724541)
      ·
        refine ⟨37559539191895501310896703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100158771178388003495724541 37559539191895501310896703)
        ·
          refine ⟨56339308787843251966345055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37559539191895501310896703 56339308787843251966345055)
          ·
            refine ⟨84508963181764877949517583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56339308787843251966345055 84508963181764877949517583)
            ·
              refine ⟨126763444772647316924276375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84508963181764877949517583 126763444772647316924276375)
              ·
                refine ⟨190145167158970975386414563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126763444772647316924276375 190145167158970975386414563)
                ·
                  refine ⟨285217750738456463079621845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190145167158970975386414563 285217750738456463079621845)
                  ·
                    refine ⟨6684791032932573353428637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 285217750738456463079621845 6684791032932573353428637)
                    ·
                      refine ⟨2506796637349715007535739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6684791032932573353428637 2506796637349715007535739)
                      ·
                        rfl

theorem cell23_4881969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_4881969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881969 prefixEnd_4881969 := by exact prefixLift 4881969
  have htrace : WordTrace (prefixWord ++ tailWord_4881969) baseStart_4881969 baseEnd_4881969 := by
    simpa [prefixWord, tailWord_4881969, baseEnd_4881969] using wordTrace_append hprefix tailTrace_4881969
  have hstable : (prefixWord ++ tailWord_4881969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881969).length < 2 ^ (prefixWord ++ tailWord_4881969).sum := by decide
  have hdescent : baseEnd_4881969 < baseStart_4881969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4881997 : List Nat := [1, 6, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_4881997 : Nat := 118140960795 + 4881997 * 2 ^ 59
def prefixEnd_4881997 : Nat := 4983230072969 + 3 ^ 40 * 4881997 * 2
def baseEnd_4881997 : Nat := 835603671602680299328537

theorem tailTrace_4881997 : CollatzResearch.WordTrace tailWord_4881997 prefixEnd_4881997 835603671602680299328537 := by
  unfold tailWord_4881997
  simp only [CollatzResearch.WordTrace]
  refine ⟨178061058894366122552196245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118707372596244081701464163 178061058894366122552196245)
  ·
    refine ⟨8346612135673411994634199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 178061058894366122552196245 8346612135673411994634199)
    ·
      refine ⟨12519918203510117991951299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8346612135673411994634199 12519918203510117991951299)
      ·
        refine ⟨18779877305265176987926949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12519918203510117991951299 18779877305265176987926949)
        ·
          refine ⟨3521226994737220685236303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18779877305265176987926949 3521226994737220685236303)
          ·
            refine ⟨5281840492105831027854455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3521226994737220685236303 5281840492105831027854455)
            ·
              refine ⟨7922760738158746541781683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5281840492105831027854455 7922760738158746541781683)
              ·
                refine ⟨11884141107238119812672525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7922760738158746541781683 11884141107238119812672525)
                ·
                  refine ⟨4456552915214294929752197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11884141107238119812672525 4456552915214294929752197)
                  ·
                    refine ⟨835603671602680299328537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4456552915214294929752197 835603671602680299328537)
                    ·
                      rfl

theorem cell23_4881997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_4881997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4881997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4881997 prefixEnd_4881997 := by exact prefixLift 4881997
  have htrace : WordTrace (prefixWord ++ tailWord_4881997) baseStart_4881997 baseEnd_4881997 := by
    simpa [prefixWord, tailWord_4881997, baseEnd_4881997] using wordTrace_append hprefix tailTrace_4881997
  have hstable : (prefixWord ++ tailWord_4881997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4881997).length < 2 ^ (prefixWord ++ tailWord_4881997).sum := by decide
  have hdescent : baseEnd_4881997 < baseStart_4881997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4881997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882043 : List Nat := [1, 1, 1, 1, 1, 4, 7, 1, 1, 1, 4]
def baseStart_4882043 : Nat := 118140960795 + 4882043 * 2 ^ 59
def prefixEnd_4882043 : Nat := 4983230072969 + 3 ^ 40 * 4882043 * 2
def baseEnd_4882043 : Nat := 2506834634918147718010399

theorem tailTrace_4882043 : CollatzResearch.WordTrace tailWord_4882043 prefixEnd_4882043 2506834634918147718010399 := by
  unfold tailWord_4882043
  simp only [CollatzResearch.WordTrace]
  refine ⟨178062736652199472408370783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118708491101466314938913855 178062736652199472408370783)
  ·
    refine ⟨267094104978299208612556175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178062736652199472408370783 267094104978299208612556175)
    ·
      refine ⟨400641157467448812918834263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267094104978299208612556175 400641157467448812918834263)
      ·
        refine ⟨600961736201173219378251395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400641157467448812918834263 600961736201173219378251395)
        ·
          refine ⟨901442604301759829067377093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600961736201173219378251395 901442604301759829067377093)
          ·
            refine ⟨169020488306579967950133205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 901442604301759829067377093 169020488306579967950133205)
            ·
              refine ⟨3961417694685467998831247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 169020488306579967950133205 3961417694685467998831247)
              ·
                refine ⟨5942126542028201998246871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3961417694685467998831247 5942126542028201998246871)
                ·
                  refine ⟨8913189813042302997370307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5942126542028201998246871 8913189813042302997370307)
                  ·
                    refine ⟨13369784719563454496055461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8913189813042302997370307 13369784719563454496055461)
                    ·
                      refine ⟨2506834634918147718010399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13369784719563454496055461 2506834634918147718010399)
                      ·
                        rfl

theorem cell23_4882043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 1, 1, 4].length) (baseStart_4882043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882043 prefixEnd_4882043 := by exact prefixLift 4882043
  have htrace : WordTrace (prefixWord ++ tailWord_4882043) baseStart_4882043 baseEnd_4882043 := by
    simpa [prefixWord, tailWord_4882043, baseEnd_4882043] using wordTrace_append hprefix tailTrace_4882043
  have hstable : (prefixWord ++ tailWord_4882043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882043).length < 2 ^ (prefixWord ++ tailWord_4882043).sum := by decide
  have hdescent : baseEnd_4882043 < baseStart_4882043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882049 : List Nat := [1, 2, 4, 2, 1, 13]
def baseStart_4882049 : Nat := 118140960795 + 4882049 * 2 ^ 59
def prefixEnd_4882049 : Nat := 4983230072969 + 3 ^ 40 * 4882049 * 2
def baseEnd_4882049 : Nat := 10316204591778085162697

theorem tailTrace_4882049 : CollatzResearch.WordTrace tailWord_4882049 prefixEnd_4882049 10316204591778085162697 := by
  unfold tailWord_4882049
  simp only [CollatzResearch.WordTrace]
  refine ⟨178062955490177735433089201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118708636993451823622059467 178062955490177735433089201)
  ·
    refine ⟨133547216617633301574816901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178062955490177735433089201 133547216617633301574816901)
    ·
      refine ⟨25040103115806244045278169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133547216617633301574816901 25040103115806244045278169)
      ·
        refine ⟨18780077336854683033958627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25040103115806244045278169 18780077336854683033958627)
        ·
          refine ⟨28170116005282024550937941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18780077336854683033958627 28170116005282024550937941)
          ·
            refine ⟨10316204591778085162697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 28170116005282024550937941 10316204591778085162697)
            ·
              rfl

theorem cell23_4882049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 13].length) (baseStart_4882049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882049 prefixEnd_4882049 := by exact prefixLift 4882049
  have htrace : WordTrace (prefixWord ++ tailWord_4882049) baseStart_4882049 baseEnd_4882049 := by
    simpa [prefixWord, tailWord_4882049, baseEnd_4882049] using wordTrace_append hprefix tailTrace_4882049
  have hstable : (prefixWord ++ tailWord_4882049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882049).length < 2 ^ (prefixWord ++ tailWord_4882049).sum := by decide
  have hdescent : baseEnd_4882049 < baseStart_4882049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882053 : List Nat := [1, 3, 1, 1, 4, 1, 4, 2, 2, 4]
def baseStart_4882053 : Nat := 118140960795 + 4882053 * 2 ^ 59
def prefixEnd_4882053 : Nat := 4983230072969 + 3 ^ 40 * 4882053 * 2
def baseEnd_4882053 : Nat := 835613256574897559628451

theorem tailTrace_4882053 : CollatzResearch.WordTrace tailWord_4882053 prefixEnd_4882053 835613256574897559628451 := by
  unfold tailWord_4882053
  simp only [CollatzResearch.WordTrace]
  refine ⟨178063101382163244116234813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118708734254775496077489875 178063101382163244116234813)
  ·
    refine ⟨66773663018311216543588055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178063101382163244116234813 66773663018311216543588055)
    ·
      refine ⟨100160494527466824815382083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66773663018311216543588055 100160494527466824815382083)
      ·
        refine ⟨150240741791200237223073125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100160494527466824815382083 150240741791200237223073125)
        ·
          refine ⟨28170139085850044479326211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150240741791200237223073125 28170139085850044479326211)
          ·
            refine ⟨42255208628775066718989317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28170139085850044479326211 42255208628775066718989317)
            ·
              refine ⟨7922851617895325009810497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42255208628775066718989317 7922851617895325009810497)
              ·
                refine ⟨5942138713421493757357873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7922851617895325009810497 5942138713421493757357873)
                ·
                  refine ⟨4456604035066120318018405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5942138713421493757357873 4456604035066120318018405)
                  ·
                    refine ⟨835613256574897559628451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4456604035066120318018405 835613256574897559628451)
                    ·
                      rfl

theorem cell23_4882053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 4].length) (baseStart_4882053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882053 prefixEnd_4882053 := by exact prefixLift 4882053
  have htrace : WordTrace (prefixWord ++ tailWord_4882053) baseStart_4882053 baseEnd_4882053 := by
    simpa [prefixWord, tailWord_4882053, baseEnd_4882053] using wordTrace_append hprefix tailTrace_4882053
  have hstable : (prefixWord ++ tailWord_4882053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882053).length < 2 ^ (prefixWord ++ tailWord_4882053).sum := by decide
  have hdescent : baseEnd_4882053 < baseStart_4882053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882069 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 2, 2, 6]
def baseStart_4882069 : Nat := 118140960795 + 4882069 * 2 ^ 59
def prefixEnd_4882069 : Nat := 4983230072969 + 3 ^ 40 * 4882069 * 2
def baseEnd_4882069 : Nat := 2506847985415164616285279

theorem tailTrace_4882069 : CollatzResearch.WordTrace tailWord_4882069 prefixEnd_4882069 2506847985415164616285279 := by
  unfold tailWord_4882069
  simp only [CollatzResearch.WordTrace]
  refine ⟨178063684950105278848817261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118709123300070185899211507 178063684950105278848817261)
  ·
    refine ⟨66773881856289479568306473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178063684950105278848817261 66773881856289479568306473)
    ·
      refine ⟨50080411392217109676229855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66773881856289479568306473 50080411392217109676229855)
      ·
        refine ⟨75120617088325664514344783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50080411392217109676229855 75120617088325664514344783)
        ·
          refine ⟨112680925632488496771517175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75120617088325664514344783 112680925632488496771517175)
          ·
            refine ⟨169021388448732745157275763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112680925632488496771517175 169021388448732745157275763)
            ·
              refine ⟨253532082673099117735913645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169021388448732745157275763 253532082673099117735913645)
              ·
                refine ⟨95074531002412169150967617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253532082673099117735913645 95074531002412169150967617)
                ·
                  refine ⟨71305898251809126863225713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95074531002412169150967617 71305898251809126863225713)
                  ·
                    refine ⟨53479423688856845147419285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71305898251809126863225713 53479423688856845147419285)
                    ·
                      refine ⟨2506847985415164616285279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53479423688856845147419285 2506847985415164616285279)
                      ·
                        rfl

theorem cell23_4882069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_4882069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882069 prefixEnd_4882069 := by exact prefixLift 4882069
  have htrace : WordTrace (prefixWord ++ tailWord_4882069) baseStart_4882069 baseEnd_4882069 := by
    simpa [prefixWord, tailWord_4882069, baseEnd_4882069] using wordTrace_append hprefix tailTrace_4882069
  have hstable : (prefixWord ++ tailWord_4882069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882069).length < 2 ^ (prefixWord ++ tailWord_4882069).sum := by decide
  have hdescent : baseEnd_4882069 < baseStart_4882069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882093 : List Nat := [1, 5, 2, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_4882093 : Nat := 118140960795 + 4882093 * 2 ^ 59
def prefixEnd_4882093 : Nat := 4983230072969 + 3 ^ 40 * 4882093 * 2
def baseEnd_4882093 : Nat := 2506860308950872522385169

theorem tailTrace_4882093 : CollatzResearch.WordTrace tailWord_4882093 prefixEnd_4882093 2506860308950872522385169 := by
  unfold tailWord_4882093
  simp only [CollatzResearch.WordTrace]
  refine ⟨178064560302018330947690933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118709706868012220631793955 178064560302018330947690933)
  ·
    refine ⟨16693552528314218526346025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 178064560302018330947690933 16693552528314218526346025)
    ·
      refine ⟨12520164396235663894759519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16693552528314218526346025 12520164396235663894759519)
      ·
        refine ⟨18780246594353495842139279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12520164396235663894759519 18780246594353495842139279)
        ·
          refine ⟨28170369891530243763208919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18780246594353495842139279 28170369891530243763208919)
          ·
            refine ⟨42255554837295365644813379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28170369891530243763208919 42255554837295365644813379)
            ·
              refine ⟨63383332255943048467220069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42255554837295365644813379 63383332255943048467220069)
              ·
                refine ⟨11884374797989321587603763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63383332255943048467220069 11884374797989321587603763)
                ·
                  refine ⟨17826562196983982381405645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11884374797989321587603763 17826562196983982381405645)
                  ·
                    refine ⟨6684960823868993393027117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17826562196983982381405645 6684960823868993393027117)
                    ·
                      refine ⟨2506860308950872522385169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6684960823868993393027117 2506860308950872522385169)
                      ·
                        rfl

theorem cell23_4882093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_4882093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882093 prefixEnd_4882093 := by exact prefixLift 4882093
  have htrace : WordTrace (prefixWord ++ tailWord_4882093) baseStart_4882093 baseEnd_4882093 := by
    simpa [prefixWord, tailWord_4882093, baseEnd_4882093] using wordTrace_append hprefix tailTrace_4882093
  have hstable : (prefixWord ++ tailWord_4882093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882093).length < 2 ^ (prefixWord ++ tailWord_4882093).sum := by decide
  have hdescent : baseEnd_4882093 < baseStart_4882093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882094 : List Nat := [4, 1, 4, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_4882094 : Nat := 118140960795 + 4882094 * 2 ^ 59
def prefixEnd_4882094 : Nat := 4983230072969 + 3 ^ 40 * 4882094 * 2
def baseEnd_4882094 : Nat := 2506860822431527018472665

theorem tailTrace_4882094 : CollatzResearch.WordTrace tailWord_4882094 prefixEnd_4882094 2506860822431527018472665 := by
  unfold tailWord_4882094
  simp only [CollatzResearch.WordTrace]
  refine ⟨22258074596876838514809667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118709731183343138745651557 22258074596876838514809667)
  ·
    refine ⟨33387111895315257772214501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22258074596876838514809667 33387111895315257772214501)
    ·
      refine ⟨6260083480371610832290219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33387111895315257772214501 6260083480371610832290219)
      ·
        refine ⟨9390125220557416248435329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6260083480371610832290219 9390125220557416248435329)
        ·
          refine ⟨7042593915418062186326497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9390125220557416248435329 7042593915418062186326497)
          ·
            refine ⟨5281945436563546639744873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7042593915418062186326497 5281945436563546639744873)
            ·
              refine ⟨3961459077422659979808655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5281945436563546639744873 3961459077422659979808655)
              ·
                refine ⟨5942188616133989969712983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3961459077422659979808655 5942188616133989969712983)
                ·
                  refine ⟨8913282924200984954569475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5942188616133989969712983 8913282924200984954569475)
                  ·
                    refine ⟨13369924386301477431854213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8913282924200984954569475 13369924386301477431854213)
                    ·
                      refine ⟨2506860822431527018472665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13369924386301477431854213 2506860822431527018472665)
                      ·
                        rfl

theorem cell23_4882094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_4882094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882094 prefixEnd_4882094 := by exact prefixLift 4882094
  have htrace : WordTrace (prefixWord ++ tailWord_4882094) baseStart_4882094 baseEnd_4882094 := by
    simpa [prefixWord, tailWord_4882094, baseEnd_4882094] using wordTrace_append hprefix tailTrace_4882094
  have hstable : (prefixWord ++ tailWord_4882094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882094).length < 2 ^ (prefixWord ++ tailWord_4882094).sum := by decide
  have hdescent : baseEnd_4882094 < baseStart_4882094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882110 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3]
def baseStart_4882110 : Nat := 118140960795 + 4882110 * 2 ^ 59
def prefixEnd_4882110 : Nat := 4983230072969 + 3 ^ 40 * 4882110 * 2
def baseEnd_4882110 : Nat := 2506869038121998955872591

theorem tailTrace_4882110 : CollatzResearch.WordTrace tailWord_4882110 prefixEnd_4882110 2506869038121998955872591 := by
  unfold tailWord_4882110
  simp only [CollatzResearch.WordTrace]
  refine ⟨22258147542869592856382473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118710120228637828567373189 22258147542869592856382473)
  ·
    refine ⟨16693610657152194642286855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22258147542869592856382473 16693610657152194642286855)
    ·
      refine ⟨25040415985728291963430283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16693610657152194642286855 25040415985728291963430283)
      ·
        refine ⟨37560623978592437945145425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25040415985728291963430283 37560623978592437945145425)
        ·
          refine ⟨28170467983944328458859069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37560623978592437945145425 28170467983944328458859069)
          ·
            refine ⟨10563925493979123172072151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28170467983944328458859069 10563925493979123172072151)
            ·
              refine ⟨15845888240968684758108227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10563925493979123172072151 15845888240968684758108227)
              ·
                refine ⟨23768832361453027137162341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15845888240968684758108227 23768832361453027137162341)
                ·
                  refine ⟨4456656067772442588217939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23768832361453027137162341 4456656067772442588217939)
                  ·
                    refine ⟨6684984101658663882326909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4456656067772442588217939 6684984101658663882326909)
                    ·
                      refine ⟨2506869038121998955872591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6684984101658663882326909 2506869038121998955872591)
                      ·
                        rfl

theorem cell23_4882110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_4882110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882110 prefixEnd_4882110 := by exact prefixLift 4882110
  have htrace : WordTrace (prefixWord ++ tailWord_4882110) baseStart_4882110 baseEnd_4882110 := by
    simpa [prefixWord, tailWord_4882110, baseEnd_4882110] using wordTrace_append hprefix tailTrace_4882110
  have hstable : (prefixWord ++ tailWord_4882110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882110).length < 2 ^ (prefixWord ++ tailWord_4882110).sum := by decide
  have hdescent : baseEnd_4882110 < baseStart_4882110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882126 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 2, 6]
def baseStart_4882126 : Nat := 118140960795 + 4882126 * 2 ^ 59
def prefixEnd_4882126 : Nat := 4983230072969 + 3 ^ 40 * 4882126 * 2
def baseEnd_4882126 : Nat := 835625751270823631090839

theorem tailTrace_4882126 : CollatzResearch.WordTrace tailWord_4882126 prefixEnd_4882126 835625751270823631090839 := by
  unfold tailWord_4882126
  simp only [CollatzResearch.WordTrace]
  refine ⟨22258220488862347197955279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118710509273932518389094821 22258220488862347197955279)
  ·
    refine ⟨33387330733293520796932919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22258220488862347197955279 33387330733293520796932919)
    ·
      refine ⟨50080996099940281195399379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33387330733293520796932919 50080996099940281195399379)
      ·
        refine ⟨75121494149910421793099069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50080996099940281195399379 75121494149910421793099069)
        ·
          refine ⟨28170560306216408172412151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75121494149910421793099069 28170560306216408172412151)
          ·
            refine ⟨42255840459324612258618227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28170560306216408172412151 42255840459324612258618227)
            ·
              refine ⟨63383760688986918387927341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42255840459324612258618227 63383760688986918387927341)
              ·
                refine ⟨23768910258370094395472753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63383760688986918387927341 23768910258370094395472753)
                ·
                  refine ⟨17826682693777570796604565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23768910258370094395472753 17826682693777570796604565)
                  ·
                    refine ⟨835625751270823631090839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17826682693777570796604565 835625751270823631090839)
                    ·
                      rfl

theorem cell23_4882126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_4882126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882126 prefixEnd_4882126 := by exact prefixLift 4882126
  have htrace : WordTrace (prefixWord ++ tailWord_4882126) baseStart_4882126 baseEnd_4882126 := by
    simpa [prefixWord, tailWord_4882126, baseEnd_4882126] using wordTrace_append hprefix tailTrace_4882126
  have hstable : (prefixWord ++ tailWord_4882126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882126).length < 2 ^ (prefixWord ++ tailWord_4882126).sum := by decide
  have hdescent : baseEnd_4882126 < baseStart_4882126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882134 : List Nat := [5, 2, 1, 3, 2, 1, 2, 7]
def baseStart_4882134 : Nat := 118140960795 + 4882134 * 2 ^ 59
def prefixEnd_4882134 : Nat := 4983230072969 + 3 ^ 40 * 4882134 * 2
def baseEnd_4882134 : Nat := 92847457839174328221203

theorem tailTrace_4882134 : CollatzResearch.WordTrace tailWord_4882134 prefixEnd_4882134 92847457839174328221203 := by
  unfold tailWord_4882134
  simp only [CollatzResearch.WordTrace]
  refine ⟨11129128480929362184370841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118710703796579863299955637 11129128480929362184370841)
  ·
    refine ⟨8346846360697021638278131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11129128480929362184370841 8346846360697021638278131)
    ·
      refine ⟨12520269541045532457417197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8346846360697021638278131 12520269541045532457417197)
      ·
        refine ⟨4695101077892074671531449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12520269541045532457417197 4695101077892074671531449)
        ·
          refine ⟨3521325808419056003648587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4695101077892074671531449 3521325808419056003648587)
          ·
            refine ⟨5281988712628584005472881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3521325808419056003648587 5281988712628584005472881)
            ·
              refine ⟨3961491534471438004104661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5281988712628584005472881 3961491534471438004104661)
              ·
                refine ⟨92847457839174328221203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3961491534471438004104661 92847457839174328221203)
                ·
                  rfl

theorem cell23_4882134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_4882134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882134 prefixEnd_4882134 := by exact prefixLift 4882134
  have htrace : WordTrace (prefixWord ++ tailWord_4882134) baseStart_4882134 baseEnd_4882134 := by
    simpa [prefixWord, tailWord_4882134, baseEnd_4882134] using wordTrace_append hprefix tailTrace_4882134
  have hstable : (prefixWord ++ tailWord_4882134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882134).length < 2 ^ (prefixWord ++ tailWord_4882134).sum := by decide
  have hdescent : baseEnd_4882134 < baseStart_4882134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882136 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 2, 1, 5]
def baseStart_4882136 : Nat := 118140960795 + 4882136 * 2 ^ 59
def prefixEnd_4882136 : Nat := 4983230072969 + 3 ^ 40 * 4882136 * 2
def baseEnd_4882136 : Nat := 2506882388619015854147471

theorem tailTrace_4882136 : CollatzResearch.WordTrace tailWord_4882136 prefixEnd_4882136 2506882388619015854147471 := by
  unfold tailWord_4882136
  simp only [CollatzResearch.WordTrace]
  refine ⟨89033064320431274645753131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118710752427241699527670841 89033064320431274645753131)
  ·
    refine ⟨133549596480646911968629697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89033064320431274645753131 133549596480646911968629697)
    ·
      refine ⟨100162197360485183976472273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133549596480646911968629697 100162197360485183976472273)
      ·
        refine ⟨75121648020363887982354205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100162197360485183976472273 75121648020363887982354205)
        ·
          refine ⟨28170618007636457993382827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75121648020363887982354205 28170618007636457993382827)
          ·
            refine ⟨42255927011454686990074241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28170618007636457993382827 42255927011454686990074241)
            ·
              refine ⟨31691945258591015242555681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42255927011454686990074241 31691945258591015242555681)
              ·
                refine ⟨23768958943943261431916761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31691945258591015242555681 23768958943943261431916761)
                ·
                  refine ⟨17826719207957446073937571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23768958943943261431916761 17826719207957446073937571)
                  ·
                    refine ⟨26740078811936169110906357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17826719207957446073937571 26740078811936169110906357)
                    ·
                      refine ⟨2506882388619015854147471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26740078811936169110906357 2506882388619015854147471)
                      ·
                        rfl

theorem cell23_4882136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_4882136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882136 prefixEnd_4882136 := by exact prefixLift 4882136
  have htrace : WordTrace (prefixWord ++ tailWord_4882136) baseStart_4882136 baseEnd_4882136 := by
    simpa [prefixWord, tailWord_4882136, baseEnd_4882136] using wordTrace_append hprefix tailTrace_4882136
  have hstable : (prefixWord ++ tailWord_4882136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882136).length < 2 ^ (prefixWord ++ tailWord_4882136).sum := by decide
  have hdescent : baseEnd_4882136 < baseStart_4882136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882223 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 4, 4, 2]
def baseStart_4882223 : Nat := 118140960795 + 4882223 * 2 ^ 59
def prefixEnd_4882223 : Nat := 4983230072969 + 3 ^ 40 * 4882223 * 2
def baseEnd_4882223 : Nat := 2506927061435957013759571

theorem tailTrace_4882223 : CollatzResearch.WordTrace tailWord_4882223 prefixEnd_4882223 2506927061435957013759571 := by
  unfold tailWord_4882223
  simp only [CollatzResearch.WordTrace]
  refine ⟨178069301791547363149923323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118712867861031575433282215 178069301791547363149923323)
  ·
    refine ⟨267103952687321044724884985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178069301791547363149923323 267103952687321044724884985)
    ·
      refine ⟨200327964515490783543663739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267103952687321044724884985 200327964515490783543663739)
      ·
        refine ⟨300491946773236175315495609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200327964515490783543663739 300491946773236175315495609)
        ·
          refine ⟨225368960079927131486621707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300491946773236175315495609 225368960079927131486621707)
          ·
            refine ⟨338053440119890697229932561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225368960079927131486621707 338053440119890697229932561)
            ·
              refine ⟨253540080089918022922449421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 338053440119890697229932561 253540080089918022922449421)
              ·
                refine ⟨95077530033719258595918533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253540080089918022922449421 95077530033719258595918533)
                ·
                  refine ⟨17827036881322360986734725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95077530033719258595918533 17827036881322360986734725)
                  ·
                    refine ⟨3342569415247942685012761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17827036881322360986734725 3342569415247942685012761)
                    ·
                      refine ⟨2506927061435957013759571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3342569415247942685012761 2506927061435957013759571)
                      ·
                        rfl

theorem cell23_4882223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 4, 2].length) (baseStart_4882223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882223 prefixEnd_4882223 := by exact prefixLift 4882223
  have htrace : WordTrace (prefixWord ++ tailWord_4882223) baseStart_4882223 baseEnd_4882223 := by
    simpa [prefixWord, tailWord_4882223, baseEnd_4882223] using wordTrace_append hprefix tailTrace_4882223
  have hstable : (prefixWord ++ tailWord_4882223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882223).length < 2 ^ (prefixWord ++ tailWord_4882223).sum := by decide
  have hdescent : baseEnd_4882223 < baseStart_4882223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882230 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_4882230 : Nat := 118140960795 + 4882230 * 2 ^ 59
def prefixEnd_4882230 : Nat := 4983230072969 + 3 ^ 40 * 4882230 * 2
def baseEnd_4882230 : Nat := 2506930655800538486372039

theorem tailTrace_4882230 : CollatzResearch.WordTrace tailWord_4882230 prefixEnd_4882230 2506930655800538486372039 := by
  unfold tailWord_4882230
  simp only [CollatzResearch.WordTrace]
  refine ⟨11129347318907625209089259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118713038068348002230285429 11129347318907625209089259)
  ·
    refine ⟨16694020978361437813633889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11129347318907625209089259 16694020978361437813633889)
    ·
      refine ⟨12520515733771078360225417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16694020978361437813633889 12520515733771078360225417)
      ·
        refine ⟨9390386800328308770169063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12520515733771078360225417 9390386800328308770169063)
        ·
          refine ⟨14085580200492463155253595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9390386800328308770169063 14085580200492463155253595)
          ·
            refine ⟨21128370300738694732880393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14085580200492463155253595 21128370300738694732880393)
            ·
              refine ⟨15846277725554021049660295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21128370300738694732880393 15846277725554021049660295)
              ·
                refine ⟨23769416588331031574490443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15846277725554021049660295 23769416588331031574490443)
                ·
                  refine ⟨35654124882496547361735665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23769416588331031574490443 35654124882496547361735665)
                  ·
                    refine ⟨26740593661872410521301749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35654124882496547361735665 26740593661872410521301749)
                    ·
                      refine ⟨2506930655800538486372039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26740593661872410521301749 2506930655800538486372039)
                      ·
                        rfl

theorem cell23_4882230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_4882230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882230 prefixEnd_4882230 := by exact prefixLift 4882230
  have htrace : WordTrace (prefixWord ++ tailWord_4882230) baseStart_4882230 baseEnd_4882230 := by
    simpa [prefixWord, tailWord_4882230, baseEnd_4882230] using wordTrace_append hprefix tailTrace_4882230
  have hstable : (prefixWord ++ tailWord_4882230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882230).length < 2 ^ (prefixWord ++ tailWord_4882230).sum := by decide
  have hdescent : baseEnd_4882230 < baseStart_4882230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882260 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 1, 4, 3]
def baseStart_4882260 : Nat := 118140960795 + 4882260 * 2 ^ 59
def prefixEnd_4882260 : Nat := 4983230072969 + 3 ^ 40 * 4882260 * 2
def baseEnd_4882260 : Nat := 2506946060220173368996901

theorem tailTrace_4882260 : CollatzResearch.WordTrace tailWord_4882260 prefixEnd_4882260 2506946060220173368996901 := by
  unfold tailWord_4882260
  simp only [CollatzResearch.WordTrace]
  refine ⟨89035325646206659234510117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118713767528275545646013489 89035325646206659234510117)
  ·
    refine ⟨16694123558663748606470647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89035325646206659234510117 16694123558663748606470647)
    ·
      refine ⟨25041185337995622909705971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16694123558663748606470647 25041185337995622909705971)
      ·
        refine ⟨37561778006993434364558957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25041185337995622909705971 37561778006993434364558957)
        ·
          refine ⟨14085666752622537886709609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37561778006993434364558957 14085666752622537886709609)
          ·
            refine ⟨10564250064466903415032207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14085666752622537886709609 10564250064466903415032207)
            ·
              refine ⟨15846375096700355122548311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10564250064466903415032207 15846375096700355122548311)
              ·
                refine ⟨23769562645050532683822467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15846375096700355122548311 23769562645050532683822467)
                ·
                  refine ⟨35654343967575799025733701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23769562645050532683822467 35654343967575799025733701)
                  ·
                    refine ⟨6685189493920462317325069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35654343967575799025733701 6685189493920462317325069)
                    ·
                      refine ⟨2506946060220173368996901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6685189493920462317325069 2506946060220173368996901)
                      ·
                        rfl

theorem cell23_4882260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_4882260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882260 prefixEnd_4882260 := by exact prefixLift 4882260
  have htrace : WordTrace (prefixWord ++ tailWord_4882260) baseStart_4882260 baseEnd_4882260 := by
    simpa [prefixWord, tailWord_4882260, baseEnd_4882260] using wordTrace_append hprefix tailTrace_4882260
  have hstable : (prefixWord ++ tailWord_4882260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882260).length < 2 ^ (prefixWord ++ tailWord_4882260).sum := by decide
  have hdescent : baseEnd_4882260 < baseStart_4882260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882318 : List Nat := [4, 1, 1, 5, 2, 1, 1, 3, 1, 4]
def baseStart_4882318 : Nat := 118140960795 + 4882318 * 2 ^ 59
def prefixEnd_4882318 : Nat := 4983230072969 + 3 ^ 40 * 4882318 * 2
def baseEnd_4882318 : Nat := 835658614032711380690545

theorem tailTrace_4882318 : CollatzResearch.WordTrace tailWord_4882318 prefixEnd_4882318 835658614032711380690545 := by
  unfold tailWord_4882318
  simp only [CollatzResearch.WordTrace]
  refine ⟨22259095840775399296828951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118715177817468796249754405 22259095840775399296828951)
  ·
    refine ⟨33388643761163098945243427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22259095840775399296828951 33388643761163098945243427)
    ·
      refine ⟨50082965641744648417865141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33388643761163098945243427 50082965641744648417865141)
      ·
        refine ⟨4695278028913560789174857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50082965641744648417865141 4695278028913560789174857)
        ·
          refine ⟨3521458521685170591881143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4695278028913560789174857 3521458521685170591881143)
          ·
            refine ⟨5282187782527755887821715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3521458521685170591881143 5282187782527755887821715)
            ·
              refine ⟨7923281673791633831732573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5282187782527755887821715 7923281673791633831732573)
              ·
                refine ⟨2971230627671862686899715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7923281673791633831732573 2971230627671862686899715)
                ·
                  refine ⟨4456845941507794030349573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2971230627671862686899715 4456845941507794030349573)
                  ·
                    refine ⟨835658614032711380690545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4456845941507794030349573 835658614032711380690545)
                    ·
                      rfl

theorem cell23_4882318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_4882318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882318 prefixEnd_4882318 := by exact prefixLift 4882318
  have htrace : WordTrace (prefixWord ++ tailWord_4882318) baseStart_4882318 baseEnd_4882318 := by
    simpa [prefixWord, tailWord_4882318, baseEnd_4882318] using wordTrace_append hprefix tailTrace_4882318
  have hstable : (prefixWord ++ tailWord_4882318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882318).length < 2 ^ (prefixWord ++ tailWord_4882318).sum := by decide
  have hdescent : baseEnd_4882318 < baseStart_4882318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882340 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 4, 4]
def baseStart_4882340 : Nat := 118140960795 + 4882340 * 2 ^ 59
def prefixEnd_4882340 : Nat := 4983230072969 + 3 ^ 40 * 4882340 * 2
def baseEnd_4882340 : Nat := 835662379557511018665511

theorem tailTrace_4882340 : CollatzResearch.WordTrace tailWord_4882340 prefixEnd_4882340 835662379557511018665511 := by
  unfold tailWord_4882340
  simp only [CollatzResearch.WordTrace]
  refine ⟨89036784566061746065966237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118715712754748994754621649 89036784566061746065966237)
  ·
    refine ⟨33388794212273154774737339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89036784566061746065966237 33388794212273154774737339)
    ·
      refine ⟨50083191318409732162106009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33388794212273154774737339 50083191318409732162106009)
      ·
        refine ⟨37562393488807299121579507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50083191318409732162106009 37562393488807299121579507)
        ·
          refine ⟨56343590233210948682369261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37562393488807299121579507 56343590233210948682369261)
          ·
            refine ⟨21128846337454105755888473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56343590233210948682369261 21128846337454105755888473)
            ·
              refine ⟨15846634753090579316916355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21128846337454105755888473 15846634753090579316916355)
              ·
                refine ⟨23769952129635868975374533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15846634753090579316916355 23769952129635868975374533)
                ·
                  refine ⟨4456866024306725432882725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23769952129635868975374533 4456866024306725432882725)
                  ·
                    refine ⟨835662379557511018665511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4456866024306725432882725 835662379557511018665511)
                    ·
                      rfl

theorem cell23_4882340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_4882340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882340 prefixEnd_4882340 := by exact prefixLift 4882340
  have htrace : WordTrace (prefixWord ++ tailWord_4882340) baseStart_4882340 baseEnd_4882340 := by
    simpa [prefixWord, tailWord_4882340, baseEnd_4882340] using wordTrace_append hprefix tailTrace_4882340
  have hstable : (prefixWord ++ tailWord_4882340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882340).length < 2 ^ (prefixWord ++ tailWord_4882340).sum := by decide
  have hdescent : baseEnd_4882340 < baseStart_4882340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882353 : List Nat := [1, 2, 2, 4, 2, 1, 1, 10]
def baseStart_4882353 : Nat := 118140960795 + 4882353 * 2 ^ 59
def prefixEnd_4882353 : Nat := 4983230072969 + 3 ^ 40 * 4882353 * 2
def baseEnd_4882353 : Nat := 92851622737816352041999

theorem tailTrace_4882353 : CollatzResearch.WordTrace tailWord_4882353 prefixEnd_4882353 92851622737816352041999 := by
  unfold tailWord_4882353
  simp only [CollatzResearch.WordTrace]
  refine ⟨178074043281076395352155713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118716028854050930234770475 178074043281076395352155713)
  ·
    refine ⟨133555532460807296514116785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178074043281076395352155713 133555532460807296514116785)
    ·
      refine ⟨100166649345605472385587589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133555532460807296514116785 100166649345605472385587589)
      ·
        refine ⟨18781246752301026072297673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100166649345605472385587589 18781246752301026072297673)
        ·
          refine ⟨14085935064225769554223255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18781246752301026072297673 14085935064225769554223255)
          ·
            refine ⟨21128902596338654331334883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14085935064225769554223255 21128902596338654331334883)
            ·
              refine ⟨31693353894507981497002325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21128902596338654331334883 31693353894507981497002325)
              ·
                refine ⟨92851622737816352041999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31693353894507981497002325 92851622737816352041999)
                ·
                  rfl

theorem cell23_4882353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 10].length) (baseStart_4882353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882353 prefixEnd_4882353 := by exact prefixLift 4882353
  have htrace : WordTrace (prefixWord ++ tailWord_4882353) baseStart_4882353 baseEnd_4882353 := by
    simpa [prefixWord, tailWord_4882353, baseEnd_4882353] using wordTrace_append hprefix tailTrace_4882353
  have hstable : (prefixWord ++ tailWord_4882353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882353).length < 2 ^ (prefixWord ++ tailWord_4882353).sum := by decide
  have hdescent : baseEnd_4882353 < baseStart_4882353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882357 : List Nat := [1, 3, 3, 2, 1, 3, 1, 3, 2, 4]
def baseStart_4882357 : Nat := 118140960795 + 4882357 * 2 ^ 59
def prefixEnd_4882357 : Nat := 4983230072969 + 3 ^ 40 * 4882357 * 2
def baseEnd_4882357 : Nat := 835665289281219829827985

theorem tailTrace_4882357 : CollatzResearch.WordTrace tailWord_4882357 prefixEnd_4882357 835665289281219829827985 := by
  unfold tailWord_4882357
  simp only [CollatzResearch.WordTrace]
  refine ⟨178074189173061904035301325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118716126115374602690200883 178074189173061904035301325)
  ·
    refine ⟨66777820939898214013237997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178074189173061904035301325 66777820939898214013237997)
    ·
      refine ⟨25041682852461830254964249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66777820939898214013237997 25041682852461830254964249)
      ·
        refine ⟨18781262139346372691223187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25041682852461830254964249 18781262139346372691223187)
        ·
          refine ⟨28171893209019559036834781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18781262139346372691223187 28171893209019559036834781)
          ·
            refine ⟨10564459953382334638813043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28171893209019559036834781 10564459953382334638813043)
            ·
              refine ⟨15846689930073501958219565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10564459953382334638813043 15846689930073501958219565)
              ·
                refine ⟨5942508723777563234332337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15846689930073501958219565 5942508723777563234332337)
                ·
                  refine ⟨4456881542833172425749253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5942508723777563234332337 4456881542833172425749253)
                  ·
                    refine ⟨835665289281219829827985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4456881542833172425749253 835665289281219829827985)
                    ·
                      rfl

theorem cell23_4882357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_4882357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882357 prefixEnd_4882357 := by exact prefixLift 4882357
  have htrace : WordTrace (prefixWord ++ tailWord_4882357) baseStart_4882357 baseEnd_4882357 := by
    simpa [prefixWord, tailWord_4882357, baseEnd_4882357] using wordTrace_append hprefix tailTrace_4882357
  have hstable : (prefixWord ++ tailWord_4882357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882357).length < 2 ^ (prefixWord ++ tailWord_4882357).sum := by decide
  have hdescent : baseEnd_4882357 < baseStart_4882357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882380 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 3, 3, 3]
def baseStart_4882380 : Nat := 118140960795 + 4882380 * 2 ^ 59
def prefixEnd_4882380 : Nat := 4983230072969 + 3 ^ 40 * 4882380 * 2
def baseEnd_4882380 : Nat := 2507007677898712899496349

theorem tailTrace_4882380 : CollatzResearch.WordTrace tailWord_4882380 prefixEnd_4882380 2507007677898712899496349 := by
  unfold tailWord_4882380
  simp only [CollatzResearch.WordTrace]
  refine ⟨89037514025989289481694297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118716685367985719308925729 89037514025989289481694297)
  ·
    refine ⟨66778135519491967111270723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89037514025989289481694297 66778135519491967111270723)
    ·
      refine ⟨100167203279237950666906085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66778135519491967111270723 100167203279237950666906085)
      ·
        refine ⟨18781350614857115750044891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100167203279237950666906085 18781350614857115750044891)
        ·
          refine ⟨28172025922285673625067337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18781350614857115750044891 28172025922285673625067337)
          ·
            refine ⟨21129019441714255218800503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28172025922285673625067337 21129019441714255218800503)
            ·
              refine ⟨31693529162571382828200755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21129019441714255218800503 31693529162571382828200755)
              ·
                refine ⟨47540293743857074242301133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31693529162571382828200755 47540293743857074242301133)
                ·
                  refine ⟨17827610153946402840862925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47540293743857074242301133 17827610153946402840862925)
                  ·
                    refine ⟨6685353807729901065323597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17827610153946402840862925 6685353807729901065323597)
                    ·
                      refine ⟨2507007677898712899496349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6685353807729901065323597 2507007677898712899496349)
                      ·
                        rfl

theorem cell23_4882380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_4882380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882380 prefixEnd_4882380 := by exact prefixLift 4882380
  have htrace : WordTrace (prefixWord ++ tailWord_4882380) baseStart_4882380 baseEnd_4882380 := by
    simpa [prefixWord, tailWord_4882380, baseEnd_4882380] using wordTrace_append hprefix tailTrace_4882380
  have hstable : (prefixWord ++ tailWord_4882380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882380).length < 2 ^ (prefixWord ++ tailWord_4882380).sum := by decide
  have hdescent : baseEnd_4882380 < baseStart_4882380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882414 : List Nat := [4, 1, 2, 1, 3, 1, 2, 3, 2, 1, 3]
def baseStart_4882414 : Nat := 118140960795 + 4882414 * 2 ^ 59
def prefixEnd_4882414 : Nat := 4983230072969 + 3 ^ 40 * 4882414 * 2
def baseEnd_4882414 : Nat := 2507025136240965766471193

theorem tailTrace_4882414 : CollatzResearch.WordTrace tailWord_4882414 prefixEnd_4882414 2507025136240965766471193 := by
  unfold tailWord_4882414
  simp only [CollatzResearch.WordTrace]
  refine ⟨22259533516731925346265787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118717512089236935180084197 22259533516731925346265787)
  ·
    refine ⟨33389300275097888019398681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22259533516731925346265787 33389300275097888019398681)
    ·
      refine ⟨25041975206323416014549011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33389300275097888019398681 25041975206323416014549011)
      ·
        refine ⟨37562962809485124021823517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25041975206323416014549011 37562962809485124021823517)
        ·
          refine ⟨14086111053556921508183819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37562962809485124021823517 14086111053556921508183819)
          ·
            refine ⟨21129166580335382262275729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14086111053556921508183819 21129166580335382262275729)
            ·
              refine ⟨15846874935251536696706797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21129166580335382262275729 15846874935251536696706797)
              ·
                refine ⟨5942578100719326261265049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15846874935251536696706797 5942578100719326261265049)
                ·
                  refine ⟨4456933575539494695948787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5942578100719326261265049 4456933575539494695948787)
                  ·
                    refine ⟨6685400363309242043923181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4456933575539494695948787 6685400363309242043923181)
                    ·
                      refine ⟨2507025136240965766471193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6685400363309242043923181 2507025136240965766471193)
                      ·
                        rfl

theorem cell23_4882414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_4882414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882414 prefixEnd_4882414 := by exact prefixLift 4882414
  have htrace : WordTrace (prefixWord ++ tailWord_4882414) baseStart_4882414 baseEnd_4882414 := by
    simpa [prefixWord, tailWord_4882414, baseEnd_4882414] using wordTrace_append hprefix tailTrace_4882414
  have hstable : (prefixWord ++ tailWord_4882414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882414).length < 2 ^ (prefixWord ++ tailWord_4882414).sum := by decide
  have hdescent : baseEnd_4882414 < baseStart_4882414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882437 : List Nat := [1, 3, 1, 1, 2, 4, 2, 2, 1, 4, 2]
def baseStart_4882437 : Nat := 118140960795 + 4882437 * 2 ^ 59
def prefixEnd_4882437 : Nat := 4983230072969 + 3 ^ 40 * 4882437 * 2
def baseEnd_4882437 : Nat := 2507036946296019176483587

theorem tailTrace_4882437 : CollatzResearch.WordTrace tailWord_4882437 prefixEnd_4882437 2507036946296019176483587 := by
  unfold tailWord_4882437
  simp only [CollatzResearch.WordTrace]
  refine ⟨178077107012772077698213565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118718071341848051798809043 178077107012772077698213565)
  ·
    refine ⟨66778915129789529136830087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178077107012772077698213565 66778915129789529136830087)
    ·
      refine ⟨100168372694684293705245131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66778915129789529136830087 100168372694684293705245131)
      ·
        refine ⟨150252559042026440557867697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100168372694684293705245131 150252559042026440557867697)
        ·
          refine ⟨112689419281519830418400773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150252559042026440557867697 112689419281519830418400773)
          ·
            refine ⟨21129266115284968203450145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112689419281519830418400773 21129266115284968203450145)
            ·
              refine ⟨15846949586463726152587609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21129266115284968203450145 15846949586463726152587609)
              ·
                refine ⟨11885212189847794614440707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15846949586463726152587609 11885212189847794614440707)
                ·
                  refine ⟨17827818284771691921661061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11885212189847794614440707 17827818284771691921661061)
                  ·
                    refine ⟨3342715928394692235311449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17827818284771691921661061 3342715928394692235311449)
                    ·
                      refine ⟨2507036946296019176483587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3342715928394692235311449 2507036946296019176483587)
                      ·
                        rfl

theorem cell23_4882437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 4, 2].length) (baseStart_4882437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882437 prefixEnd_4882437 := by exact prefixLift 4882437
  have htrace : WordTrace (prefixWord ++ tailWord_4882437) baseStart_4882437 baseEnd_4882437 := by
    simpa [prefixWord, tailWord_4882437, baseEnd_4882437] using wordTrace_append hprefix tailTrace_4882437
  have hstable : (prefixWord ++ tailWord_4882437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882437).length < 2 ^ (prefixWord ++ tailWord_4882437).sum := by decide
  have hdescent : baseEnd_4882437 < baseStart_4882437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882443 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 9]
def baseStart_4882443 : Nat := 118140960795 + 4882443 * 2 ^ 59
def prefixEnd_4882443 : Nat := 4983230072969 + 3 ^ 40 * 4882443 * 2
def baseEnd_4882443 : Nat := 278560003019994017000951

theorem tailTrace_4882443 : CollatzResearch.WordTrace tailWord_4882443 prefixEnd_4882443 278560003019994017000951 := by
  unfold tailWord_4882443
  simp only [CollatzResearch.WordTrace]
  refine ⟨178077325850750340722931983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118718217233833560481954655 178077325850750340722931983)
  ·
    refine ⟨267115988776125511084397975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178077325850750340722931983 267115988776125511084397975)
    ·
      refine ⟨400673983164188266626596963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267115988776125511084397975 400673983164188266626596963)
      ·
        refine ⟨601010974746282399939895445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400673983164188266626596963 601010974746282399939895445)
        ·
          refine ⟨28172389441231987497182599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 601010974746282399939895445 28172389441231987497182599)
          ·
            refine ⟨42258584161847981245773899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28172389441231987497182599 42258584161847981245773899)
            ·
              refine ⟨63387876242771971868660849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42258584161847981245773899 63387876242771971868660849)
              ·
                refine ⟨47540907182078978901495637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63387876242771971868660849 47540907182078978901495637)
                ·
                  refine ⟨278560003019994017000951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47540907182078978901495637 278560003019994017000951)
                  ·
                    rfl

theorem cell23_4882443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 9].length) (baseStart_4882443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882443 prefixEnd_4882443 := by exact prefixLift 4882443
  have htrace : WordTrace (prefixWord ++ tailWord_4882443) baseStart_4882443 baseEnd_4882443 := by
    simpa [prefixWord, tailWord_4882443, baseEnd_4882443] using wordTrace_append hprefix tailTrace_4882443
  have hstable : (prefixWord ++ tailWord_4882443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882443).length < 2 ^ (prefixWord ++ tailWord_4882443).sum := by decide
  have hdescent : baseEnd_4882443 < baseStart_4882443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882460 : List Nat := [2, 2, 3, 1, 3, 1, 1, 3, 7]
def baseStart_4882460 : Nat := 118140960795 + 4882460 * 2 ^ 59
def prefixEnd_4882460 : Nat := 4983230072969 + 3 ^ 40 * 4882460 * 2
def baseEnd_4882460 : Nat := 278560972927896954055109

theorem tailTrace_4882460 : CollatzResearch.WordTrace tailWord_4882460 prefixEnd_4882460 278560972927896954055109 := by
  unfold tailWord_4882460
  simp only [CollatzResearch.WordTrace]
  refine ⟨89038972945844376313150417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118718630594459168417533889 89038972945844376313150417)
  ·
    refine ⟨66779229709383282234862813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89038972945844376313150417 66779229709383282234862813)
    ·
      refine ⟨25042211141018730838073555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66779229709383282234862813 25042211141018730838073555)
      ·
        refine ⟨37563316711528096257110333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25042211141018730838073555 37563316711528096257110333)
        ·
          refine ⟨14086243766823036096416375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37563316711528096257110333 14086243766823036096416375)
          ·
            refine ⟨21129365650234554144624563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14086243766823036096416375 21129365650234554144624563)
            ·
              refine ⟨31694048475351831216936845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21129365650234554144624563 31694048475351831216936845)
              ·
                refine ⟨11885268178256936706351317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31694048475351831216936845 11885268178256936706351317)
                ·
                  refine ⟨278560972927896954055109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11885268178256936706351317 278560972927896954055109)
                  ·
                    rfl

theorem cell23_4882460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 7].length) (baseStart_4882460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882460 prefixEnd_4882460 := by exact prefixLift 4882460
  have htrace : WordTrace (prefixWord ++ tailWord_4882460) baseStart_4882460 baseEnd_4882460 := by
    simpa [prefixWord, tailWord_4882460, baseEnd_4882460] using wordTrace_append hprefix tailTrace_4882460
  have hstable : (prefixWord ++ tailWord_4882460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882460).length < 2 ^ (prefixWord ++ tailWord_4882460).sum := by decide
  have hdescent : baseEnd_4882460 < baseStart_4882460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882490 : List Nat := [3, 1, 1, 1, 3, 1, 1, 5, 2, 5]
def baseStart_4882490 : Nat := 118140960795 + 4882490 * 2 ^ 59
def prefixEnd_4882490 : Nat := 4983230072969 + 3 ^ 40 * 4882490 * 2
def baseEnd_4882490 : Nat := 835688053590235823040281

theorem tailTrace_4882490 : CollatzResearch.WordTrace tailWord_4882490 prefixEnd_4882490 835688053590235823040281 := by
  unfold tailWord_4882490
  simp only [CollatzResearch.WordTrace]
  refine ⟨44519760020395016937473231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118719360054386711833261949 44519760020395016937473231)
  ·
    refine ⟨66779640030592525406209847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44519760020395016937473231 66779640030592525406209847)
    ·
      refine ⟨100169460045888788109314771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66779640030592525406209847 100169460045888788109314771)
      ·
        refine ⟨150254190068833182163972157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100169460045888788109314771 150254190068833182163972157)
        ·
          refine ⟨56345321275812443311489559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150254190068833182163972157 56345321275812443311489559)
          ·
            refine ⟨84517981913718664967234339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56345321275812443311489559 84517981913718664967234339)
            ·
              refine ⟨126776972870577997450851509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84517981913718664967234339 126776972870577997450851509)
              ·
                refine ⟨11885341206616687261017329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126776972870577997450851509 11885341206616687261017329)
                ·
                  refine ⟨8914005904962515445762997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11885341206616687261017329 8914005904962515445762997)
                  ·
                    refine ⟨835688053590235823040281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8914005904962515445762997 835688053590235823040281)
                    ·
                      rfl

theorem cell23_4882490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_4882490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882490 prefixEnd_4882490 := by exact prefixLift 4882490
  have htrace : WordTrace (prefixWord ++ tailWord_4882490) baseStart_4882490 baseEnd_4882490 := by
    simpa [prefixWord, tailWord_4882490, baseEnd_4882490] using wordTrace_append hprefix tailTrace_4882490
  have hstable : (prefixWord ++ tailWord_4882490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882490).length < 2 ^ (prefixWord ++ tailWord_4882490).sum := by decide
  have hdescent : baseEnd_4882490 < baseStart_4882490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882577 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 9, 1, 3]
def baseStart_4882577 : Nat := 118140960795 + 4882577 * 2 ^ 59
def prefixEnd_4882577 : Nat := 4983230072969 + 3 ^ 40 * 4882577 * 2
def baseEnd_4882577 : Nat := 2507108833587648628732943

theorem tailTrace_4882577 : CollatzResearch.WordTrace tailWord_4882577 prefixEnd_4882577 2507108833587648628732943 := by
  unfold tailWord_4882577
  simp only [CollatzResearch.WordTrace]
  refine ⟨178082213232264881608309985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118721475488176587738873323 178082213232264881608309985)
  ·
    refine ⟨133561659924198661206232489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178082213232264881608309985 133561659924198661206232489)
    ·
      refine ⟨100171244943148995904674367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133561659924198661206232489 100171244943148995904674367)
      ·
        refine ⟨150256867414723493857011551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100171244943148995904674367 150256867414723493857011551)
        ·
          refine ⟨225385301122085240785517327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150256867414723493857011551 225385301122085240785517327)
          ·
            refine ⟨338077951683127861178275991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225385301122085240785517327 338077951683127861178275991)
            ·
              refine ⟨507116927524691791767413987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338077951683127861178275991 507116927524691791767413987)
              ·
                refine ⟨760675391287037687651120981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 507116927524691791767413987 760675391287037687651120981)
                ·
                  refine ⟨4457082370822486451080787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 760675391287037687651120981 4457082370822486451080787)
                  ·
                    refine ⟨6685623556233729676621181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4457082370822486451080787 6685623556233729676621181)
                    ·
                      refine ⟨2507108833587648628732943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6685623556233729676621181 2507108833587648628732943)
                      ·
                        rfl

theorem cell23_4882577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 1, 3].length) (baseStart_4882577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882577 prefixEnd_4882577 := by exact prefixLift 4882577
  have htrace : WordTrace (prefixWord ++ tailWord_4882577) baseStart_4882577 baseEnd_4882577 := by
    simpa [prefixWord, tailWord_4882577, baseEnd_4882577] using wordTrace_append hprefix tailTrace_4882577
  have hstable : (prefixWord ++ tailWord_4882577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882577).length < 2 ^ (prefixWord ++ tailWord_4882577).sum := by decide
  have hdescent : baseEnd_4882577 < baseStart_4882577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882597 : List Nat := [1, 3, 1, 2, 1, 3, 2, 4, 1, 5]
def baseStart_4882597 : Nat := 118140960795 + 4882597 * 2 ^ 59
def prefixEnd_4882597 : Nat := 4983230072969 + 3 ^ 40 * 4882597 * 2
def baseEnd_4882597 : Nat := 835706367733579516827617

theorem tailTrace_4882597 : CollatzResearch.WordTrace tailWord_4882597 prefixEnd_4882597 835706367733579516827617 := by
  unfold tailWord_4882597
  simp only [CollatzResearch.WordTrace]
  refine ⟨178082942692192425024038045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118721961794794950016025363 178082942692192425024038045)
  ·
    refine ⟨66781103509572159384014267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178082942692192425024038045 66781103509572159384014267)
    ·
      refine ⟨100171655264358239076021401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66781103509572159384014267 100171655264358239076021401)
      ·
        refine ⟨75128741448268679307016051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100171655264358239076021401 75128741448268679307016051)
        ·
          refine ⟨112693112172403018960524077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75128741448268679307016051 112693112172403018960524077)
          ·
            refine ⟨42259917064651132110196529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112693112172403018960524077 42259917064651132110196529)
            ·
              refine ⟨31694937798488349082647397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42259917064651132110196529 31694937798488349082647397)
              ·
                refine ⟨5942800837216565452996387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31694937798488349082647397 5942800837216565452996387)
                ·
                  refine ⟨8914201255824848179494581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5942800837216565452996387 8914201255824848179494581)
                  ·
                    refine ⟨835706367733579516827617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8914201255824848179494581 835706367733579516827617)
                    ·
                      rfl

theorem cell23_4882597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 5].length) (baseStart_4882597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882597 prefixEnd_4882597 := by exact prefixLift 4882597
  have htrace : WordTrace (prefixWord ++ tailWord_4882597) baseStart_4882597 baseEnd_4882597 := by
    simpa [prefixWord, tailWord_4882597, baseEnd_4882597] using wordTrace_append hprefix tailTrace_4882597
  have hstable : (prefixWord ++ tailWord_4882597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882597).length < 2 ^ (prefixWord ++ tailWord_4882597).sum := by decide
  have hdescent : baseEnd_4882597 < baseStart_4882597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882628 : List Nat := [2, 3, 3, 1, 2, 1, 2, 4, 1, 1, 3]
def baseStart_4882628 : Nat := 118140960795 + 4882628 * 2 ^ 59
def prefixEnd_4882628 : Nat := 4983230072969 + 3 ^ 40 * 4882628 * 2
def baseEnd_4882628 : Nat := 2507135021101027929195209

theorem tailTrace_4882628 : CollatzResearch.WordTrace tailWord_4882628 prefixEnd_4882628 2507135021101027929195209 := by
  unfold tailWord_4882628
  simp only [CollatzResearch.WordTrace]
  refine ⟨89042036677540058659208269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118722715570053411545611025 89042036677540058659208269)
  ·
    refine ⟨33390763754077521997203101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89042036677540058659208269 33390763754077521997203101)
    ·
      refine ⟨12521536407779070748951163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33390763754077521997203101 12521536407779070748951163)
      ·
        refine ⟨18782304611668606123426745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12521536407779070748951163 18782304611668606123426745)
        ·
          refine ⟨14086728458751454592570059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18782304611668606123426745 14086728458751454592570059)
          ·
            refine ⟨21130092688127181888855089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14086728458751454592570059 21130092688127181888855089)
            ·
              refine ⟨15847569516095386416641317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21130092688127181888855089 15847569516095386416641317)
              ·
                refine ⟨2971419284267884953120247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15847569516095386416641317 2971419284267884953120247)
                ·
                  refine ⟨4457128926401827429680371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2971419284267884953120247 4457128926401827429680371)
                  ·
                    refine ⟨6685693389602741144520557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4457128926401827429680371 6685693389602741144520557)
                    ·
                      refine ⟨2507135021101027929195209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6685693389602741144520557 2507135021101027929195209)
                      ·
                        rfl

theorem cell23_4882628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_4882628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882628 prefixEnd_4882628 := by exact prefixLift 4882628
  have htrace : WordTrace (prefixWord ++ tailWord_4882628) baseStart_4882628 baseEnd_4882628 := by
    simpa [prefixWord, tailWord_4882628, baseEnd_4882628] using wordTrace_append hprefix tailTrace_4882628
  have hstable : (prefixWord ++ tailWord_4882628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882628).length < 2 ^ (prefixWord ++ tailWord_4882628).sum := by decide
  have hdescent : baseEnd_4882628 < baseStart_4882628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882667 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 3]
def baseStart_4882667 : Nat := 118140960795 + 4882667 * 2 ^ 59
def prefixEnd_4882667 : Nat := 4983230072969 + 3 ^ 40 * 4882667 * 2
def baseEnd_4882667 : Nat := 2507155046846553276607529

theorem tailTrace_4882667 : CollatzResearch.WordTrace tailWord_4882667 prefixEnd_4882667 2507155046846553276607529 := by
  unfold tailWord_4882667
  simp only [CollatzResearch.WordTrace]
  refine ⟨178085495801938826979086255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118723663867959217986057503 178085495801938826979086255)
  ·
    refine ⟨267128243702908240468629383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178085495801938826979086255 267128243702908240468629383)
    ·
      refine ⟨400692365554362360702944075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267128243702908240468629383 400692365554362360702944075)
      ·
        refine ⟨601038548331543541054416113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400692365554362360702944075 601038548331543541054416113)
        ·
          refine ⟨450778911248657655790812085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 601038548331543541054416113 450778911248657655790812085)
          ·
            refine ⟨42260522929561655230388633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 450778911248657655790812085 42260522929561655230388633)
            ·
              refine ⟨31695392197171241422791475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42260522929561655230388633 31695392197171241422791475)
              ·
                refine ⟨47543088295756862134187213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31695392197171241422791475 47543088295756862134187213)
                ·
                  refine ⟨17828658110908823300320205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47543088295756862134187213 17828658110908823300320205)
                  ·
                    refine ⟨6685746791590808737620077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17828658110908823300320205 6685746791590808737620077)
                    ·
                      refine ⟨2507155046846553276607529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6685746791590808737620077 2507155046846553276607529)
                      ·
                        rfl

theorem cell23_4882667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 3].length) (baseStart_4882667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882667 prefixEnd_4882667 := by exact prefixLift 4882667
  have htrace : WordTrace (prefixWord ++ tailWord_4882667) baseStart_4882667 baseEnd_4882667 := by
    simpa [prefixWord, tailWord_4882667, baseEnd_4882667] using wordTrace_append hprefix tailTrace_4882667
  have hstable : (prefixWord ++ tailWord_4882667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882667).length < 2 ^ (prefixWord ++ tailWord_4882667).sum := by decide
  have hdescent : baseEnd_4882667 < baseStart_4882667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882695 : List Nat := [1, 1, 4, 5, 1, 2, 2, 1, 2, 4]
def baseStart_4882695 : Nat := 118140960795 + 4882695 * 2 ^ 59
def prefixEnd_4882695 : Nat := 4983230072969 + 3 ^ 40 * 4882695 * 2
def baseEnd_4882695 : Nat := 835723141434959722352467

theorem tailTrace_4882695 : CollatzResearch.WordTrace tailWord_4882695 prefixEnd_4882695 835723141434959722352467 := by
  unfold tailWord_4882695
  simp only [CollatzResearch.WordTrace]
  refine ⟨178086517045837387761105539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118724344697224925174070359 178086517045837387761105539)
  ·
    refine ⟨267129775568756081641658309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178086517045837387761105539 267129775568756081641658309)
    ·
      refine ⟨50086832919141765307810933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 267129775568756081641658309 50086832919141765307810933)
      ·
        refine ⟨4695640586169540497607275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50086832919141765307810933 4695640586169540497607275)
        ·
          refine ⟨7043460879254310746410913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4695640586169540497607275 7043460879254310746410913)
          ·
            refine ⟨5282595659440733059808185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7043460879254310746410913 5282595659440733059808185)
            ·
              refine ⟨3961946744580549794856139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5282595659440733059808185 3961946744580549794856139)
              ·
                refine ⟨5942920116870824692284209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3961946744580549794856139 5942920116870824692284209)
                ·
                  refine ⟨4457190087653118519213157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5942920116870824692284209 4457190087653118519213157)
                  ·
                    refine ⟨835723141434959722352467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4457190087653118519213157 835723141434959722352467)
                    ·
                      rfl

theorem cell23_4882695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_4882695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882695 prefixEnd_4882695 := by exact prefixLift 4882695
  have htrace : WordTrace (prefixWord ++ tailWord_4882695) baseStart_4882695 baseEnd_4882695 := by
    simpa [prefixWord, tailWord_4882695, baseEnd_4882695] using wordTrace_append hprefix tailTrace_4882695
  have hstable : (prefixWord ++ tailWord_4882695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882695).length < 2 ^ (prefixWord ++ tailWord_4882695).sum := by decide
  have hdescent : baseEnd_4882695 < baseStart_4882695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882711 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 3, 3, 2]
def baseStart_4882711 : Nat := 118140960795 + 4882711 * 2 ^ 59
def prefixEnd_4882711 : Nat := 4983230072969 + 3 ^ 40 * 4882711 * 2
def baseEnd_4882711 : Nat := 2507177639995351104457327

theorem tailTrace_4882711 : CollatzResearch.WordTrace tailWord_4882711 prefixEnd_4882711 2507177639995351104457327 := by
  unfold tailWord_4882711
  simp only [CollatzResearch.WordTrace]
  refine ⟨178087100613779422493687987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118724733742519614995791991 178087100613779422493687987)
  ·
    refine ⟨267130650920669133740531981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178087100613779422493687987 267130650920669133740531981)
    ·
      refine ⟨100173994095250925152699493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267130650920669133740531981 100173994095250925152699493)
      ·
        refine ⟨18782623892859548466131155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100173994095250925152699493 18782623892859548466131155)
        ·
          refine ⟨28173935839289322699196733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18782623892859548466131155 28173935839289322699196733)
          ·
            refine ⟨10565225939733496012198775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28173935839289322699196733 10565225939733496012198775)
            ·
              refine ⟨15847838909600244018298163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10565225939733496012198775 15847838909600244018298163)
              ·
                refine ⟨23771758364400366027447245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15847838909600244018298163 23771758364400366027447245)
                ·
                  refine ⟨8914409386650137260292717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23771758364400366027447245 8914409386650137260292717)
                  ·
                    refine ⟨3342903519993801472609769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8914409386650137260292717 3342903519993801472609769)
                    ·
                      refine ⟨2507177639995351104457327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3342903519993801472609769 2507177639995351104457327)
                      ·
                        rfl

theorem cell23_4882711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_4882711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882711 prefixEnd_4882711 := by exact prefixLift 4882711
  have htrace : WordTrace (prefixWord ++ tailWord_4882711) baseStart_4882711 baseEnd_4882711 := by
    simpa [prefixWord, tailWord_4882711, baseEnd_4882711] using wordTrace_append hprefix tailTrace_4882711
  have hstable : (prefixWord ++ tailWord_4882711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882711).length < 2 ^ (prefixWord ++ tailWord_4882711).sum := by decide
  have hdescent : baseEnd_4882711 < baseStart_4882711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882718 : List Nat := [4, 3, 2, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_4882718 : Nat := 118140960795 + 4882718 * 2 ^ 59
def prefixEnd_4882718 : Nat := 4983230072969 + 3 ^ 40 * 4882718 * 2
def baseEnd_4882718 : Nat := 2507181234359932577069795

theorem tailTrace_4882718 : CollatzResearch.WordTrace tailWord_4882718 prefixEnd_4882718 2507181234359932577069795 := by
  unfold tailWord_4882718
  simp only [CollatzResearch.WordTrace]
  refine ⟨22260919490594257836149101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118724903949836041792795205 22260919490594257836149101)
  ·
    refine ⟨8347844808972846688555913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22260919490594257836149101 8347844808972846688555913)
    ·
      refine ⟨6260883606729635016416935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8347844808972846688555913 6260883606729635016416935)
      ·
        refine ⟨9391325410094452524625403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6260883606729635016416935 9391325410094452524625403)
        ·
          refine ⟨14086988115141678786938105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9391325410094452524625403 14086988115141678786938105)
          ·
            refine ⟨10565241086356259090203579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14086988115141678786938105 10565241086356259090203579)
            ·
              refine ⟨15847861629534388635305369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10565241086356259090203579 15847861629534388635305369)
              ·
                refine ⟨11885896222150791476479027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15847861629534388635305369 11885896222150791476479027)
                ·
                  refine ⟨17828844333226187214718541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11885896222150791476479027 17828844333226187214718541)
                  ·
                    refine ⟨6685816624959820205519453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17828844333226187214718541 6685816624959820205519453)
                    ·
                      refine ⟨2507181234359932577069795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6685816624959820205519453 2507181234359932577069795)
                      ·
                        rfl

theorem cell23_4882718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_4882718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882718 prefixEnd_4882718 := by exact prefixLift 4882718
  have htrace : WordTrace (prefixWord ++ tailWord_4882718) baseStart_4882718 baseEnd_4882718 := by
    simpa [prefixWord, tailWord_4882718, baseEnd_4882718] using wordTrace_append hprefix tailTrace_4882718
  have hstable : (prefixWord ++ tailWord_4882718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882718).length < 2 ^ (prefixWord ++ tailWord_4882718).sum := by decide
  have hdescent : baseEnd_4882718 < baseStart_4882718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882851 : List Nat := [1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 3]
def baseStart_4882851 : Nat := 118140960795 + 4882851 * 2 ^ 59
def prefixEnd_4882851 : Nat := 4983230072969 + 3 ^ 40 * 4882851 * 2
def baseEnd_4882851 : Nat := 2507249527286980556706683

theorem tailTrace_4882851 : CollatzResearch.WordTrace tailWord_4882851 prefixEnd_4882851 2507249527286980556706683 := by
  unfold tailWord_4882851
  simp only [CollatzResearch.WordTrace]
  refine ⟨178092206833272226403784407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118728137888848150935856271 178092206833272226403784407)
  ·
    refine ⟨267138310249908339605676611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178092206833272226403784407 267138310249908339605676611)
    ·
      refine ⟨400707465374862509408514917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267138310249908339605676611 400707465374862509408514917)
      ·
        refine ⟨75132649757786720514096547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 400707465374862509408514917 75132649757786720514096547)
        ·
          refine ⟨112698974636680080771144821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75132649757786720514096547 112698974636680080771144821)
          ·
            refine ⟨10565528872188757572294827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112698974636680080771144821 10565528872188757572294827)
            ·
              refine ⟨15848293308283136358442241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10565528872188757572294827 15848293308283136358442241)
              ·
                refine ⟨11886219981212352268831681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15848293308283136358442241 11886219981212352268831681)
                ·
                  refine ⟨8914664985909264201623761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11886219981212352268831681 8914664985909264201623761)
                  ·
                    refine ⟨6685998739431948151217821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8914664985909264201623761 6685998739431948151217821)
                    ·
                      refine ⟨2507249527286980556706683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6685998739431948151217821 2507249527286980556706683)
                      ·
                        rfl

theorem cell23_4882851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_4882851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882851 prefixEnd_4882851 := by exact prefixLift 4882851
  have htrace : WordTrace (prefixWord ++ tailWord_4882851) baseStart_4882851 baseEnd_4882851 := by
    simpa [prefixWord, tailWord_4882851, baseEnd_4882851] using wordTrace_append hprefix tailTrace_4882851
  have hstable : (prefixWord ++ tailWord_4882851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882851).length < 2 ^ (prefixWord ++ tailWord_4882851).sum := by decide
  have hdescent : baseEnd_4882851 < baseStart_4882851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882857 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 8]
def baseStart_4882857 : Nat := 118140960795 + 4882857 * 2 ^ 59
def prefixEnd_4882857 : Nat := 4983230072969 + 3 ^ 40 * 4882857 * 2
def baseEnd_4882857 : Nat := 2507252608170907533231655

theorem tailTrace_4882857 : CollatzResearch.WordTrace tailWord_4882857 prefixEnd_4882857 2507252608170907533231655 := by
  unfold tailWord_4882857
  simp only [CollatzResearch.WordTrace]
  refine ⟨178092425671250489428502825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118728283780833659619001883 178092425671250489428502825)
  ·
    refine ⟨133569319253437867071377119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178092425671250489428502825 133569319253437867071377119)
    ·
      refine ⟨200353978880156800607065679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133569319253437867071377119 200353978880156800607065679)
      ·
        refine ⟨300530968320235200910598519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200353978880156800607065679 300530968320235200910598519)
        ·
          refine ⟨450796452480352801365897779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300530968320235200910598519 450796452480352801365897779)
          ·
            refine ⟨676194678720529202048846669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450796452480352801365897779 676194678720529202048846669)
            ·
              refine ⟨253573004520198450768317501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 676194678720529202048846669 253573004520198450768317501)
              ·
                refine ⟨95089876695074419038119063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253573004520198450768317501 95089876695074419038119063)
                ·
                  refine ⟨142634815042611628557178595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95089876695074419038119063 142634815042611628557178595)
                  ·
                    refine ⟨213952222563917442835767893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 142634815042611628557178595 213952222563917442835767893)
                    ·
                      refine ⟨2507252608170907533231655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 213952222563917442835767893 2507252608170907533231655)
                      ·
                        rfl

theorem cell23_4882857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_4882857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882857 prefixEnd_4882857 := by exact prefixLift 4882857
  have htrace : WordTrace (prefixWord ++ tailWord_4882857) baseStart_4882857 baseEnd_4882857 := by
    simpa [prefixWord, tailWord_4882857, baseEnd_4882857] using wordTrace_append hprefix tailTrace_4882857
  have hstable : (prefixWord ++ tailWord_4882857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882857).length < 2 ^ (prefixWord ++ tailWord_4882857).sum := by decide
  have hdescent : baseEnd_4882857 < baseStart_4882857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882867 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 1, 11]
def baseStart_4882867 : Nat := 118140960795 + 4882867 * 2 ^ 59
def prefixEnd_4882867 : Nat := 4983230072969 + 3 ^ 40 * 4882867 * 2
def baseEnd_4882867 : Nat := 835752580992484164702203

theorem tailTrace_4882867 : CollatzResearch.WordTrace tailWord_4882867 prefixEnd_4882867 835752580992484164702203 := by
  unfold tailWord_4882867
  simp only [CollatzResearch.WordTrace]
  refine ⟨178092790401214261136366855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118728526934142840757577903 178092790401214261136366855)
  ·
    refine ⟨267139185601821391704550283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178092790401214261136366855 267139185601821391704550283)
    ·
      refine ⟨400708778402732087556825425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267139185601821391704550283 400708778402732087556825425)
      ·
        refine ⟨300531583802049065667619069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400708778402732087556825425 300531583802049065667619069)
        ·
          refine ⟨112699343925768399625357151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 300531583802049065667619069 112699343925768399625357151)
          ·
            refine ⟨169049015888652599438035727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112699343925768399625357151 169049015888652599438035727)
            ·
              refine ⟨253573523832978899157053591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169049015888652599438035727 253573523832978899157053591)
              ·
                refine ⟨380360285749468348735580387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253573523832978899157053591 380360285749468348735580387)
                ·
                  refine ⟨570540428624202523103370581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380360285749468348735580387 570540428624202523103370581)
                  ·
                    refine ⟨835752580992484164702203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 570540428624202523103370581 835752580992484164702203)
                    ·
                      rfl

theorem cell23_4882867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 11].length) (baseStart_4882867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882867 prefixEnd_4882867 := by exact prefixLift 4882867
  have htrace : WordTrace (prefixWord ++ tailWord_4882867) baseStart_4882867 baseEnd_4882867 := by
    simpa [prefixWord, tailWord_4882867, baseEnd_4882867] using wordTrace_append hprefix tailTrace_4882867
  have hstable : (prefixWord ++ tailWord_4882867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882867).length < 2 ^ (prefixWord ++ tailWord_4882867).sum := by decide
  have hdescent : baseEnd_4882867 < baseStart_4882867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882871 : List Nat := [1, 1, 3, 1, 3, 3, 4, 1, 6]
def baseStart_4882871 : Nat := 118140960795 + 4882871 * 2 ^ 59
def prefixEnd_4882871 : Nat := 4983230072969 + 3 ^ 40 * 4882871 * 2
def baseEnd_4882871 : Nat := 278584421877785608717399

theorem tailTrace_4882871 : CollatzResearch.WordTrace tailWord_4882871 prefixEnd_4882871 278584421877785608717399 := by
  unfold tailWord_4882871
  simp only [CollatzResearch.WordTrace]
  refine ⟨178092936293199769819512467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118728624195466513213008311 178092936293199769819512467)
  ·
    refine ⟨267139404439799654729268701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178092936293199769819512467 267139404439799654729268701)
    ·
      refine ⟨100177276664924870523475763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267139404439799654729268701 100177276664924870523475763)
      ·
        refine ⟨150265914997387305785213645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100177276664924870523475763 150265914997387305785213645)
        ·
          refine ⟨56349718124020239669455117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150265914997387305785213645 56349718124020239669455117)
          ·
            refine ⟨21131144296507589876045669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56349718124020239669455117 21131144296507589876045669)
            ·
              refine ⟨3962089555595173101758563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21131144296507589876045669 3962089555595173101758563)
              ·
                refine ⟨5943134333392759652637845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3962089555595173101758563 5943134333392759652637845)
                ·
                  refine ⟨278584421877785608717399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5943134333392759652637845 278584421877785608717399)
                  ·
                    rfl

theorem cell23_4882871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 6].length) (baseStart_4882871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882871 prefixEnd_4882871 := by exact prefixLift 4882871
  have htrace : WordTrace (prefixWord ++ tailWord_4882871) baseStart_4882871 baseEnd_4882871 := by
    simpa [prefixWord, tailWord_4882871, baseEnd_4882871] using wordTrace_append hprefix tailTrace_4882871
  have hstable : (prefixWord ++ tailWord_4882871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882871).length < 2 ^ (prefixWord ++ tailWord_4882871).sum := by decide
  have hdescent : baseEnd_4882871 < baseStart_4882871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882924 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 5]
def baseStart_4882924 : Nat := 118140960795 + 4882924 * 2 ^ 59
def prefixEnd_4882924 : Nat := 4983230072969 + 3 ^ 40 * 4882924 * 2
def baseEnd_4882924 : Nat := 2507287011374758771093847

theorem tailTrace_4882924 : CollatzResearch.WordTrace tailWord_4882924 prefixEnd_4882924 2507287011374758771093847 := by
  unfold tailWord_4882924
  simp only [CollatzResearch.WordTrace]
  refine ⟨89047434681003879935595913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118729912908005173247461217 89047434681003879935595913)
  ·
    refine ⟨66785576010752909951696935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89047434681003879935595913 66785576010752909951696935)
    ·
      refine ⟨100178364016129364927545403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66785576010752909951696935 100178364016129364927545403)
      ·
        refine ⟨150267546024194047391318105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100178364016129364927545403 150267546024194047391318105)
        ·
          refine ⟨112700659518145535543488579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150267546024194047391318105 112700659518145535543488579)
          ·
            refine ⟨169050989277218303315232869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112700659518145535543488579 169050989277218303315232869)
            ·
              refine ⟨31697060489478431871606163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169050989277218303315232869 31697060489478431871606163)
              ·
                refine ⟨47545590734217647807409245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31697060489478431871606163 47545590734217647807409245)
                ·
                  refine ⟨17829596525331617927778467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47545590734217647807409245 17829596525331617927778467)
                  ·
                    refine ⟨26744394787997426891667701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17829596525331617927778467 26744394787997426891667701)
                    ·
                      refine ⟨2507287011374758771093847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26744394787997426891667701 2507287011374758771093847)
                      ·
                        rfl

theorem cell23_4882924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_4882924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882924 prefixEnd_4882924 := by exact prefixLift 4882924
  have htrace : WordTrace (prefixWord ++ tailWord_4882924) baseStart_4882924 baseEnd_4882924 := by
    simpa [prefixWord, tailWord_4882924, baseEnd_4882924] using wordTrace_append hprefix tailTrace_4882924
  have hstable : (prefixWord ++ tailWord_4882924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882924).length < 2 ^ (prefixWord ++ tailWord_4882924).sum := by decide
  have hdescent : baseEnd_4882924 < baseStart_4882924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882931 : List Nat := [1, 1, 1, 2, 2, 2, 3, 5, 2, 4]
def baseStart_4882931 : Nat := 118140960795 + 4882931 * 2 ^ 59
def prefixEnd_4882931 : Nat := 4983230072969 + 3 ^ 40 * 4882931 * 2
def baseEnd_4882931 : Nat := 835763535246446747902105

theorem tailTrace_4882931 : CollatzResearch.WordTrace tailWord_4882931 prefixEnd_4882931 835763535246446747902105 := by
  unfold tailWord_4882931
  simp only [CollatzResearch.WordTrace]
  refine ⟨178095124672982400066696647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118730083115321600044464431 178095124672982400066696647)
  ·
    refine ⟨267142687009473600100044971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178095124672982400066696647 267142687009473600100044971)
    ·
      refine ⟨400714030514210400150067457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267142687009473600100044971 400714030514210400150067457)
      ·
        refine ⟨300535522885657800112550593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400714030514210400150067457 300535522885657800112550593)
        ·
          refine ⟨225401642164243350084412945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300535522885657800112550593 225401642164243350084412945)
          ·
            refine ⟨169051231623182512563309709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225401642164243350084412945 169051231623182512563309709)
            ·
              refine ⟨63394211858693442211241141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169051231623182512563309709 63394211858693442211241141)
              ·
                refine ⟨5943207361752510207303857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63394211858693442211241141 5943207361752510207303857)
                ·
                  refine ⟨4457405521314382655477893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5943207361752510207303857 4457405521314382655477893)
                  ·
                    refine ⟨835763535246446747902105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4457405521314382655477893 835763535246446747902105)
                    ·
                      rfl

theorem cell23_4882931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 4].length) (baseStart_4882931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882931 prefixEnd_4882931 := by exact prefixLift 4882931
  have htrace : WordTrace (prefixWord ++ tailWord_4882931) baseStart_4882931 baseEnd_4882931 := by
    simpa [prefixWord, tailWord_4882931, baseEnd_4882931] using wordTrace_append hprefix tailTrace_4882931
  have hstable : (prefixWord ++ tailWord_4882931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882931).length < 2 ^ (prefixWord ++ tailWord_4882931).sum := by decide
  have hdescent : baseEnd_4882931 < baseStart_4882931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882941 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 3, 2, 3]
def baseStart_4882941 : Nat := 118140960795 + 4882941 * 2 ^ 59
def prefixEnd_4882941 : Nat := 4983230072969 + 3 ^ 40 * 4882941 * 2
def baseEnd_4882941 : Nat := 2507295740545885204581269

theorem tailTrace_4882941 : CollatzResearch.WordTrace tailWord_4882941 prefixEnd_4882941 2507295740545885204581269 := by
  unfold tailWord_4882941
  simp only [CollatzResearch.WordTrace]
  refine ⟨178095489402946171774560677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118730326268630781183040451 178095489402946171774560677)
  ·
    refine ⟨33392904263052407207730127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178095489402946171774560677 33392904263052407207730127)
    ·
      refine ⟨50089356394578610811595191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33392904263052407207730127 50089356394578610811595191)
      ·
        refine ⟨75134034591867916217392787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50089356394578610811595191 75134034591867916217392787)
        ·
          refine ⟨112701051887801874326089181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75134034591867916217392787 112701051887801874326089181)
          ·
            refine ⟨42262894457925702872283443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112701051887801874326089181 42262894457925702872283443)
            ·
              refine ⟨63394341686888554308425165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42262894457925702872283443 63394341686888554308425165)
              ·
                refine ⟨23772878132583207865659437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63394341686888554308425165 23772878132583207865659437)
                ·
                  refine ⟨8914829299718702949622289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23772878132583207865659437 8914829299718702949622289)
                  ·
                    refine ⟨6686121974789027212216717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8914829299718702949622289 6686121974789027212216717)
                    ·
                      refine ⟨2507295740545885204581269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6686121974789027212216717 2507295740545885204581269)
                      ·
                        rfl

theorem cell23_4882941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_4882941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882941 prefixEnd_4882941 := by exact prefixLift 4882941
  have htrace : WordTrace (prefixWord ++ tailWord_4882941) baseStart_4882941 baseEnd_4882941 := by
    simpa [prefixWord, tailWord_4882941, baseEnd_4882941] using wordTrace_append hprefix tailTrace_4882941
  have hstable : (prefixWord ++ tailWord_4882941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882941).length < 2 ^ (prefixWord ++ tailWord_4882941).sum := by decide
  have hdescent : baseEnd_4882941 < baseStart_4882941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882955 : List Nat := [1, 1, 1, 1, 7, 3, 2, 1, 1, 1, 4]
def baseStart_4882955 : Nat := 118140960795 + 4882955 * 2 ^ 59
def prefixEnd_4882955 : Nat := 4983230072969 + 3 ^ 40 * 4882955 * 2
def baseEnd_4882955 : Nat := 2507302929275048149806205

theorem tailTrace_4882955 : CollatzResearch.WordTrace tailWord_4882955 prefixEnd_4882955 2507302929275048149806205 := by
  unfold tailWord_4882955
  simp only [CollatzResearch.WordTrace]
  refine ⟨178096000024895452165570319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118730666683263634777046879 178096000024895452165570319)
  ·
    refine ⟨267144000037343178248355479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178096000024895452165570319 267144000037343178248355479)
    ·
      refine ⟨400716000056014767372533219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267144000037343178248355479 400716000056014767372533219)
      ·
        refine ⟨601074000084022151058799829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400716000056014767372533219 601074000084022151058799829)
        ·
          refine ⟨14087671876969269165440621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 601074000084022151058799829 14087671876969269165440621)
          ·
            refine ⟨5282876953863475937040233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14087671876969269165440621 5282876953863475937040233)
            ·
              refine ⟨3962157715397606952780175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5282876953863475937040233 3962157715397606952780175)
              ·
                refine ⟨5943236573096410429170263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3962157715397606952780175 5943236573096410429170263)
                ·
                  refine ⟨8914854859644615643755395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5943236573096410429170263 8914854859644615643755395)
                  ·
                    refine ⟨13372282289466923465633093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8914854859644615643755395 13372282289466923465633093)
                    ·
                      refine ⟨2507302929275048149806205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13372282289466923465633093 2507302929275048149806205)
                      ·
                        rfl

theorem cell23_4882955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 1, 1, 4].length) (baseStart_4882955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882955 prefixEnd_4882955 := by exact prefixLift 4882955
  have htrace : WordTrace (prefixWord ++ tailWord_4882955) baseStart_4882955 baseEnd_4882955 := by
    simpa [prefixWord, tailWord_4882955, baseEnd_4882955] using wordTrace_append hprefix tailTrace_4882955
  have hstable : (prefixWord ++ tailWord_4882955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882955).length < 2 ^ (prefixWord ++ tailWord_4882955).sum := by decide
  have hdescent : baseEnd_4882955 < baseStart_4882955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882972 : List Nat := [2, 2, 3, 1, 2, 2, 2, 4, 1, 2, 2]
def baseStart_4882972 : Nat := 118140960795 + 4882972 * 2 ^ 59
def prefixEnd_4882972 : Nat := 4983230072969 + 3 ^ 40 * 4882972 * 2
def baseEnd_4882972 : Nat := 2507311658446174583293627

theorem tailTrace_4882972 : CollatzResearch.WordTrace tailWord_4882972 prefixEnd_4882972 2507311658446174583293627 := by
  unfold tailWord_4882972
  simp only [CollatzResearch.WordTrace]
  refine ⟨89048310032916932034469585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118731080043889242712626113 89048310032916932034469585)
  ·
    refine ⟨66786232524687699025852189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89048310032916932034469585 66786232524687699025852189)
    ·
      refine ⟨25044837196757887134694571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66786232524687699025852189 25044837196757887134694571)
      ·
        refine ⟨37567255795136830702041857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25044837196757887134694571 37567255795136830702041857)
        ·
          refine ⟨28175441846352623026531393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37567255795136830702041857 28175441846352623026531393)
          ·
            refine ⟨21131581384764467269898545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28175441846352623026531393 21131581384764467269898545)
            ·
              refine ⟨15848686038573350452423909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21131581384764467269898545 15848686038573350452423909)
              ·
                refine ⟨2971628632232503209829483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15848686038573350452423909 2971628632232503209829483)
                ·
                  refine ⟨4457442948348754814744225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2971628632232503209829483 4457442948348754814744225)
                  ·
                    refine ⟨3343082211261566111058169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4457442948348754814744225 3343082211261566111058169)
                    ·
                      refine ⟨2507311658446174583293627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3343082211261566111058169 2507311658446174583293627)
                      ·
                        rfl

theorem cell23_4882972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_4882972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882972 prefixEnd_4882972 := by exact prefixLift 4882972
  have htrace : WordTrace (prefixWord ++ tailWord_4882972) baseStart_4882972 baseEnd_4882972 := by
    simpa [prefixWord, tailWord_4882972, baseEnd_4882972] using wordTrace_append hprefix tailTrace_4882972
  have hstable : (prefixWord ++ tailWord_4882972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882972).length < 2 ^ (prefixWord ++ tailWord_4882972).sum := by decide
  have hdescent : baseEnd_4882972 < baseStart_4882972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882988 : List Nat := [2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 3]
def baseStart_4882988 : Nat := 118140960795 + 4882988 * 2 ^ 59
def prefixEnd_4882988 : Nat := 4983230072969 + 3 ^ 40 * 4882988 * 2
def baseEnd_4882988 : Nat := 2507319874136646520693553

theorem tailTrace_4882988 : CollatzResearch.WordTrace tailWord_4882988 prefixEnd_4882988 2507319874136646520693553 := by
  unfold tailWord_4882988
  simp only [CollatzResearch.WordTrace]
  refine ⟨89048601816887949400760809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118731469089183932534347745 89048601816887949400760809)
  ·
    refine ⟨66786451362665962050570607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89048601816887949400760809 66786451362665962050570607)
    ·
      refine ⟨100179677043998943075855911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66786451362665962050570607 100179677043998943075855911)
      ·
        refine ⟨150269515565998414613783867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100179677043998943075855911 150269515565998414613783867)
        ·
          refine ⟨225404273348997621920675801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150269515565998414613783867 225404273348997621920675801)
          ·
            refine ⟨169053205011748216440506851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225404273348997621920675801 169053205011748216440506851)
            ·
              refine ⟨253579807517622324660760277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169053205011748216440506851 253579807517622324660760277)
              ·
                refine ⟨5943276738694273234236569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 253579807517622324660760277 5943276738694273234236569)
                ·
                  refine ⟨4457457554020704925677427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5943276738694273234236569 4457457554020704925677427)
                  ·
                    refine ⟨6686186331031057388516141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4457457554020704925677427 6686186331031057388516141)
                    ·
                      refine ⟨2507319874136646520693553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6686186331031057388516141 2507319874136646520693553)
                      ·
                        rfl

theorem cell23_4882988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 3].length) (baseStart_4882988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882988 prefixEnd_4882988 := by exact prefixLift 4882988
  have htrace : WordTrace (prefixWord ++ tailWord_4882988) baseStart_4882988 baseEnd_4882988 := by
    simpa [prefixWord, tailWord_4882988, baseEnd_4882988] using wordTrace_append hprefix tailTrace_4882988
  have hstable : (prefixWord ++ tailWord_4882988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882988).length < 2 ^ (prefixWord ++ tailWord_4882988).sum := by decide
  have hdescent : baseEnd_4882988 < baseStart_4882988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4882989 : List Nat := [1, 5, 4, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_4882989 : Nat := 118140960795 + 4882989 * 2 ^ 59
def prefixEnd_4882989 : Nat := 4983230072969 + 3 ^ 40 * 4882989 * 2
def baseEnd_4882989 : Nat := 2507320387617301016781049

theorem tailTrace_4882989 : CollatzResearch.WordTrace tailWord_4882989 prefixEnd_4882989 2507320387617301016781049 := by
  unfold tailWord_4882989
  simp only [CollatzResearch.WordTrace]
  refine ⟨178097240106772275972308021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118731493404514850648205347 178097240106772275972308021)
  ·
    refine ⟨16696616260009900872403877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 178097240106772275972308021 16696616260009900872403877)
    ·
      refine ⟨3130615548751856413575727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16696616260009900872403877 3130615548751856413575727)
      ·
        refine ⟨4695923323127784620363591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3130615548751856413575727 4695923323127784620363591)
        ·
          refine ⟨7043884984691676930545387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4695923323127784620363591 7043884984691676930545387)
          ·
            refine ⟨10565827477037515395818081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7043884984691676930545387 10565827477037515395818081)
            ·
              refine ⟨7924370607778136546863561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10565827477037515395818081 7924370607778136546863561)
              ·
                refine ⟨5943277955833602410147671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7924370607778136546863561 5943277955833602410147671)
                ·
                  refine ⟨8914916933750403615221507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5943277955833602410147671 8914916933750403615221507)
                  ·
                    refine ⟨13372375400625605422832261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8914916933750403615221507 13372375400625605422832261)
                    ·
                      refine ⟨2507320387617301016781049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13372375400625605422832261 2507320387617301016781049)
                      ·
                        rfl

theorem cell23_4882989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_4882989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4882989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4882989 prefixEnd_4882989 := by exact prefixLift 4882989
  have htrace : WordTrace (prefixWord ++ tailWord_4882989) baseStart_4882989 baseEnd_4882989 := by
    simpa [prefixWord, tailWord_4882989, baseEnd_4882989] using wordTrace_append hprefix tailTrace_4882989
  have hstable : (prefixWord ++ tailWord_4882989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4882989).length < 2 ^ (prefixWord ++ tailWord_4882989).sum := by decide
  have hdescent : baseEnd_4882989 < baseStart_4882989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4882989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883012 : List Nat := [2, 3, 5, 1, 2, 1, 9]
def baseStart_4883012 : Nat := 118140960795 + 4883012 * 2 ^ 59
def prefixEnd_4883012 : Nat := 4983230072969 + 3 ^ 40 * 4883012 * 2
def baseEnd_4883012 : Nat := 30954718489782153417203

theorem tailTrace_4883012 : CollatzResearch.WordTrace tailWord_4883012 prefixEnd_4883012 30954718489782153417203 := by
  unfold tailWord_4883012
  simp only [CollatzResearch.WordTrace]
  refine ⟨89049039492844475450197645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118732052657125967266930193 89049039492844475450197645)
  ·
    refine ⟨33393389809816678293824117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89049039492844475450197645 33393389809816678293824117)
    ·
      refine ⟨3130630294670313590046011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33393389809816678293824117 3130630294670313590046011)
      ·
        refine ⟨4695945442005470385069017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3130630294670313590046011 4695945442005470385069017)
        ·
          refine ⟨3521959081504102788801763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4695945442005470385069017 3521959081504102788801763)
          ·
            refine ⟨5282938622256154183202645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3521959081504102788801763 5282938622256154183202645)
            ·
              refine ⟨30954718489782153417203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5282938622256154183202645 30954718489782153417203)
              ·
                rfl

theorem cell23_4883012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 9].length) (baseStart_4883012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883012 prefixEnd_4883012 := by exact prefixLift 4883012
  have htrace : WordTrace (prefixWord ++ tailWord_4883012) baseStart_4883012 baseEnd_4883012 := by
    simpa [prefixWord, tailWord_4883012, baseEnd_4883012] using wordTrace_append hprefix tailTrace_4883012
  have hstable : (prefixWord ++ tailWord_4883012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883012).length < 2 ^ (prefixWord ++ tailWord_4883012).sum := by decide
  have hdescent : baseEnd_4883012 < baseStart_4883012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883015 : List Nat := [1, 1, 4, 1, 4, 1, 2, 3, 1, 3, 2]
def baseStart_4883015 : Nat := 118140960795 + 4883015 * 2 ^ 59
def prefixEnd_4883015 : Nat := 4983230072969 + 3 ^ 40 * 4883015 * 2
def baseEnd_4883015 : Nat := 2507333738114317915055929

theorem tailTrace_4883015 : CollatzResearch.WordTrace tailWord_4883015 prefixEnd_4883015 2507333738114317915055929 := by
  unfold tailWord_4883015
  simp only [CollatzResearch.WordTrace]
  refine ⟨178098188404678082412754499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118732125603118721608502999 178098188404678082412754499)
  ·
    refine ⟨267147282607017123619131749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178098188404678082412754499 267147282607017123619131749)
    ·
      refine ⟨50090115488815710678587203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 267147282607017123619131749 50090115488815710678587203)
      ·
        refine ⟨75135173233223566017880805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50090115488815710678587203 75135173233223566017880805)
        ·
          refine ⟨14087844981229418628352651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75135173233223566017880805 14087844981229418628352651)
          ·
            refine ⟨21131767471844127942528977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14087844981229418628352651 21131767471844127942528977)
            ·
              refine ⟨15848825603883095956896733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21131767471844127942528977 15848825603883095956896733)
              ·
                refine ⟨5943309601456160983836275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15848825603883095956896733 5943309601456160983836275)
                ·
                  refine ⟨8914964402184241475754413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5943309601456160983836275 8914964402184241475754413)
                  ·
                    refine ⟨3343111650819090553407905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8914964402184241475754413 3343111650819090553407905)
                    ·
                      refine ⟨2507333738114317915055929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3343111650819090553407905 2507333738114317915055929)
                      ·
                        rfl

theorem cell23_4883015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 3, 2].length) (baseStart_4883015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883015 prefixEnd_4883015 := by exact prefixLift 4883015
  have htrace : WordTrace (prefixWord ++ tailWord_4883015) baseStart_4883015 baseEnd_4883015 := by
    simpa [prefixWord, tailWord_4883015, baseEnd_4883015] using wordTrace_append hprefix tailTrace_4883015
  have hstable : (prefixWord ++ tailWord_4883015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883015).length < 2 ^ (prefixWord ++ tailWord_4883015).sum := by decide
  have hdescent : baseEnd_4883015 < baseStart_4883015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883024 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 6]
def baseStart_4883024 : Nat := 118140960795 + 4883024 * 2 ^ 59
def prefixEnd_4883024 : Nat := 4983230072969 + 3 ^ 40 * 4883024 * 2
def baseEnd_4883024 : Nat := 2507338359440208379843387

theorem tailTrace_4883024 : CollatzResearch.WordTrace tailWord_4883024 prefixEnd_4883024 2507338359440208379843387 := by
  unfold tailWord_4883024
  simp only [CollatzResearch.WordTrace]
  refine ⟨89049258330822738474916063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118732344441096984633221417 89049258330822738474916063)
  ·
    refine ⟨133573887496234107712374095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89049258330822738474916063 133573887496234107712374095)
    ·
      refine ⟨200360831244351161568561143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133573887496234107712374095 200360831244351161568561143)
      ·
        refine ⟨300541246866526742352841715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200360831244351161568561143 300541246866526742352841715)
        ·
          refine ⟨450811870299790113529262573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300541246866526742352841715 450811870299790113529262573)
          ·
            refine ⟨169054451362421292573473465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 450811870299790113529262573 169054451362421292573473465)
            ·
              refine ⟨126790838521815969430105099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169054451362421292573473465 126790838521815969430105099)
              ·
                refine ⟨190186257782723954145157649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126790838521815969430105099 190186257782723954145157649)
                ·
                  refine ⟨142639693337042965608868237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190186257782723954145157649 142639693337042965608868237)
                  ·
                    refine ⟨53489885001391112103325589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 142639693337042965608868237 53489885001391112103325589)
                    ·
                      refine ⟨2507338359440208379843387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53489885001391112103325589 2507338359440208379843387)
                      ·
                        rfl

theorem cell23_4883024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_4883024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883024 prefixEnd_4883024 := by exact prefixLift 4883024
  have htrace : WordTrace (prefixWord ++ tailWord_4883024) baseStart_4883024 baseEnd_4883024 := by
    simpa [prefixWord, tailWord_4883024, baseEnd_4883024] using wordTrace_append hprefix tailTrace_4883024
  have hstable : (prefixWord ++ tailWord_4883024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883024).length < 2 ^ (prefixWord ++ tailWord_4883024).sum := by decide
  have hdescent : baseEnd_4883024 < baseStart_4883024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883031 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 3]
def baseStart_4883031 : Nat := 118140960795 + 4883031 * 2 ^ 59
def prefixEnd_4883031 : Nat := 4983230072969 + 3 ^ 40 * 4883031 * 2
def baseEnd_4883031 : Nat := 2507341953804789852455855

theorem tailTrace_4883031 : CollatzResearch.WordTrace tailWord_4883031 prefixEnd_4883031 2507341953804789852455855 := by
  unfold tailWord_4883031
  simp only [CollatzResearch.WordTrace]
  refine ⟨178098771972620117145336947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118732514648413411430224631 178098771972620117145336947)
  ·
    refine ⟨267148157958930175718005421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178098771972620117145336947 267148157958930175718005421)
    ·
      refine ⟨100180559234598815894252033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267148157958930175718005421 100180559234598815894252033)
      ·
        refine ⟨75135419425949111920689025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100180559234598815894252033 75135419425949111920689025)
        ·
          refine ⟨56351564569461833940516769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75135419425949111920689025 56351564569461833940516769)
          ·
            refine ⟨42263673427096375455387577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56351564569461833940516769 42263673427096375455387577)
            ·
              refine ⟨31697755070322281591540683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42263673427096375455387577 31697755070322281591540683)
              ·
                refine ⟨47546632605483422387311025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31697755070322281591540683 47546632605483422387311025)
                ·
                  refine ⟨35659974454112566790483269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47546632605483422387311025 35659974454112566790483269)
                  ·
                    refine ⟨6686245210146106273215613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35659974454112566790483269 6686245210146106273215613)
                    ·
                      refine ⟨2507341953804789852455855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6686245210146106273215613 2507341953804789852455855)
                      ·
                        rfl

theorem cell23_4883031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_4883031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883031 prefixEnd_4883031 := by exact prefixLift 4883031
  have htrace : WordTrace (prefixWord ++ tailWord_4883031) baseStart_4883031 baseEnd_4883031 := by
    simpa [prefixWord, tailWord_4883031, baseEnd_4883031] using wordTrace_append hprefix tailTrace_4883031
  have hstable : (prefixWord ++ tailWord_4883031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883031).length < 2 ^ (prefixWord ++ tailWord_4883031).sum := by decide
  have hdescent : baseEnd_4883031 < baseStart_4883031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883062 : List Nat := [5, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2]
def baseStart_4883062 : Nat := 118140960795 + 4883062 * 2 ^ 59
def prefixEnd_4883062 : Nat := 4983230072969 + 3 ^ 40 * 4883062 * 2
def baseEnd_4883062 : Nat := 2507357871705079231168213

theorem tailTrace_4883062 : CollatzResearch.WordTrace tailWord_4883062 prefixEnd_4883062 2507357871705079231168213 := by
  unfold tailWord_4883062
  simp only [CollatzResearch.WordTrace]
  refine ⟨11131243914719238089982215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118733268423671872959810293 11131243914719238089982215)
  ·
    refine ⟨16696865872078857134973323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11131243914719238089982215 16696865872078857134973323)
    ·
      refine ⟨25045298808118285702459985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16696865872078857134973323 25045298808118285702459985)
      ·
        refine ⟨18783974106088714276844989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25045298808118285702459985 18783974106088714276844989)
        ·
          refine ⟨7043990289783267853816871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18783974106088714276844989 7043990289783267853816871)
          ·
            refine ⟨10565985434674901780725307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7043990289783267853816871 10565985434674901780725307)
            ·
              refine ⟨15848978152012352671087961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10565985434674901780725307 15848978152012352671087961)
              ·
                refine ⟨11886733614009264503315971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15848978152012352671087961 11886733614009264503315971)
                ·
                  refine ⟨17830100421013896754973957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11886733614009264503315971 17830100421013896754973957)
                  ·
                    refine ⟨3343143828940105641557617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17830100421013896754973957 3343143828940105641557617)
                    ·
                      refine ⟨2507357871705079231168213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3343143828940105641557617 2507357871705079231168213)
                      ·
                        rfl

theorem cell23_4883062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_4883062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883062 prefixEnd_4883062 := by exact prefixLift 4883062
  have htrace : WordTrace (prefixWord ++ tailWord_4883062) baseStart_4883062 baseEnd_4883062 := by
    simpa [prefixWord, tailWord_4883062, baseEnd_4883062] using wordTrace_append hprefix tailTrace_4883062
  have hstable : (prefixWord ++ tailWord_4883062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883062).length < 2 ^ (prefixWord ++ tailWord_4883062).sum := by decide
  have hdescent : baseEnd_4883062 < baseStart_4883062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883161 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 6]
def baseStart_4883161 : Nat := 118140960795 + 4883161 * 2 ^ 59
def prefixEnd_4883161 : Nat := 4983230072969 + 3 ^ 40 * 4883161 * 2
def baseEnd_4883161 : Nat := 2507408706289874343830257

theorem tailTrace_4883161 : CollatzResearch.WordTrace tailWord_4883161 prefixEnd_4883161 2507408706289874343830257 := by
  unfold tailWord_4883161
  simp only [CollatzResearch.WordTrace]
  refine ⟨178103513462149149347569337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118735675641432766231712891 178103513462149149347569337)
  ·
    refine ⟨133577635096611862010677003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178103513462149149347569337 133577635096611862010677003)
    ·
      refine ⟨200366452644917793016015505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133577635096611862010677003 200366452644917793016015505)
      ·
        refine ⟨150274839483688344762011629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200366452644917793016015505 150274839483688344762011629)
        ·
          refine ⟨56353064806383129285754361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150274839483688344762011629 56353064806383129285754361)
          ·
            refine ⟨42264798604787346964315771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56353064806383129285754361 42264798604787346964315771)
            ·
              refine ⟨63397197907181020446473657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42264798604787346964315771 63397197907181020446473657)
              ·
                refine ⟨47547898430385765334855243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63397197907181020446473657 47547898430385765334855243)
                ·
                  refine ⟨71321847645578648002282865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47547898430385765334855243 71321847645578648002282865)
                  ·
                    refine ⟨53491385734183986001712149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71321847645578648002282865 53491385734183986001712149)
                    ·
                      refine ⟨2507408706289874343830257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53491385734183986001712149 2507408706289874343830257)
                      ·
                        rfl

theorem cell23_4883161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_4883161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883161 prefixEnd_4883161 := by exact prefixLift 4883161
  have htrace : WordTrace (prefixWord ++ tailWord_4883161) baseStart_4883161 baseEnd_4883161 := by
    simpa [prefixWord, tailWord_4883161, baseEnd_4883161] using wordTrace_append hprefix tailTrace_4883161
  have hstable : (prefixWord ++ tailWord_4883161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883161).length < 2 ^ (prefixWord ++ tailWord_4883161).sum := by decide
  have hdescent : baseEnd_4883161 < baseStart_4883161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883292 : List Nat := [2, 2, 4, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_4883292 : Nat := 118140960795 + 4883292 * 2 ^ 59
def prefixEnd_4883292 : Nat := 4983230072969 + 3 ^ 40 * 4883292 * 2
def baseEnd_4883292 : Nat := 2507475972255613331292155

theorem tailTrace_4883292 : CollatzResearch.WordTrace tailWord_4883292 prefixEnd_4883292 2507475972255613331292155 := by
  unfold tailWord_4883292
  simp only [CollatzResearch.WordTrace]
  refine ⟨89054145712337279360294065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118738860949783039147058753 89054145712337279360294065)
  ·
    refine ⟨66790609284252959520220549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89054145712337279360294065 66790609284252959520220549)
    ·
      refine ⟨12523239240797429910041353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66790609284252959520220549 12523239240797429910041353)
      ·
        refine ⟨9392429430598072432531015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12523239240797429910041353 9392429430598072432531015)
        ·
          refine ⟨14088644145897108648796523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9392429430598072432531015 14088644145897108648796523)
          ·
            refine ⟨21132966218845662973194785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14088644145897108648796523 21132966218845662973194785)
            ·
              refine ⟨15849724664134247229896089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21132966218845662973194785 15849724664134247229896089)
              ·
                refine ⟨11887293498100685422422067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15849724664134247229896089 11887293498100685422422067)
                ·
                  refine ⟨17830940247151028133633101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11887293498100685422422067 17830940247151028133633101)
                  ·
                    refine ⟨6686602592681635550112413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17830940247151028133633101 6686602592681635550112413)
                    ·
                      refine ⟨2507475972255613331292155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6686602592681635550112413 2507475972255613331292155)
                      ·
                        rfl

theorem cell23_4883292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_4883292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883292 prefixEnd_4883292 := by exact prefixLift 4883292
  have htrace : WordTrace (prefixWord ++ tailWord_4883292) baseStart_4883292 baseEnd_4883292 := by
    simpa [prefixWord, tailWord_4883292, baseEnd_4883292] using wordTrace_append hprefix tailTrace_4883292
  have hstable : (prefixWord ++ tailWord_4883292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883292).length < 2 ^ (prefixWord ++ tailWord_4883292).sum := by decide
  have hdescent : baseEnd_4883292 < baseStart_4883292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883308 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 4, 6]
def baseStart_4883308 : Nat := 118140960795 + 4883308 * 2 ^ 59
def prefixEnd_4883308 : Nat := 4983230072969 + 3 ^ 40 * 4883308 * 2
def baseEnd_4883308 : Nat := 835828062648695089564027

theorem tailTrace_4883308 : CollatzResearch.WordTrace tailWord_4883308 prefixEnd_4883308 835828062648695089564027 := by
  unfold tailWord_4883308
  simp only [CollatzResearch.WordTrace]
  refine ⟨89054437496308296726585289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118739249995077728968780385 89054437496308296726585289)
  ·
    refine ⟨66790828122231222544938967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89054437496308296726585289 66790828122231222544938967)
    ·
      refine ⟨100186242183346833817408451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66790828122231222544938967 100186242183346833817408451)
      ·
        refine ⟨150279363275020250726112677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100186242183346833817408451 150279363275020250726112677)
        ·
          refine ⟨28177380614066297011146127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150279363275020250726112677 28177380614066297011146127)
          ·
            refine ⟨42266070921099445516719191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28177380614066297011146127 42266070921099445516719191)
            ·
              refine ⟨63399106381649168275078787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42266070921099445516719191 63399106381649168275078787)
              ·
                refine ⟨95098659572473752412618181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63399106381649168275078787 95098659572473752412618181)
                ·
                  refine ⟨17830998669838828577365909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95098659572473752412618181 17830998669838828577365909)
                  ·
                    refine ⟨835828062648695089564027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17830998669838828577365909 835828062648695089564027)
                    ·
                      rfl

theorem cell23_4883308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_4883308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883308 prefixEnd_4883308 := by exact prefixLift 4883308
  have htrace : WordTrace (prefixWord ++ tailWord_4883308) baseStart_4883308 baseEnd_4883308 := by
    simpa [prefixWord, tailWord_4883308, baseEnd_4883308] using wordTrace_append hprefix tailTrace_4883308
  have hstable : (prefixWord ++ tailWord_4883308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883308).length < 2 ^ (prefixWord ++ tailWord_4883308).sum := by decide
  have hdescent : baseEnd_4883308 < baseStart_4883308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883315 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 3, 4, 2]
def baseStart_4883315 : Nat := 118140960795 + 4883315 * 2 ^ 59
def prefixEnd_4883315 : Nat := 4983230072969 + 3 ^ 40 * 4883315 * 2
def baseEnd_4883315 : Nat := 2507487782310666741304549

theorem tailTrace_4883315 : CollatzResearch.WordTrace tailWord_4883315 prefixEnd_4883315 2507487782310666741304549 := by
  unfold tailWord_4883315
  simp only [CollatzResearch.WordTrace]
  refine ⟨178109130303591233648675399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118739420202394155765783599 178109130303591233648675399)
  ·
    refine ⟨267163695455386850473013099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178109130303591233648675399 267163695455386850473013099)
    ·
      refine ⟨400745543183080275709519649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267163695455386850473013099 400745543183080275709519649)
      ·
        refine ⟨300559157387310206782139737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400745543183080275709519649 300559157387310206782139737)
        ·
          refine ⟨225419368040482655086604803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300559157387310206782139737 225419368040482655086604803)
          ·
            refine ⟨338129052060723982629907205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225419368040482655086604803 338129052060723982629907205)
            ·
              refine ⟨63399197261385746743107601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 338129052060723982629907205 63399197261385746743107601)
              ·
                refine ⟨47549397946039310057330701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63399197261385746743107601 47549397946039310057330701)
                ·
                  refine ⟨17831024229764741271499013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47549397946039310057330701 17831024229764741271499013)
                  ·
                    refine ⟨3343317043080888988406065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17831024229764741271499013 3343317043080888988406065)
                    ·
                      refine ⟨2507487782310666741304549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3343317043080888988406065 2507487782310666741304549)
                      ·
                        rfl

theorem cell23_4883315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 4, 2].length) (baseStart_4883315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883315 prefixEnd_4883315 := by exact prefixLift 4883315
  have htrace : WordTrace (prefixWord ++ tailWord_4883315) baseStart_4883315 baseEnd_4883315 := by
    simpa [prefixWord, tailWord_4883315, baseEnd_4883315] using wordTrace_append hprefix tailTrace_4883315
  have hstable : (prefixWord ++ tailWord_4883315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883315).length < 2 ^ (prefixWord ++ tailWord_4883315).sum := by decide
  have hdescent : baseEnd_4883315 < baseStart_4883315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883326 : List Nat := [4, 2, 3, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_4883326 : Nat := 118140960795 + 4883326 * 2 ^ 59
def prefixEnd_4883326 : Nat := 4983230072969 + 3 ^ 40 * 4883326 * 2
def baseEnd_4883326 : Nat := 2507493430597866198266999

theorem tailTrace_4883326 : CollatzResearch.WordTrace tailWord_4883326 prefixEnd_4883326 2507493430597866198266999 := by
  unfold tailWord_4883326
  simp only [CollatzResearch.WordTrace]
  refine ⟨22263691438318922815915729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118739687671034255018217221 22263691438318922815915729)
  ·
    refine ⟨16697768578739192111936797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22263691438318922815915729 16697768578739192111936797)
    ·
      refine ⟨6261663217027197041976299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16697768578739192111936797 6261663217027197041976299)
      ·
        refine ⟨9392494825540795562964449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6261663217027197041976299 9392494825540795562964449)
        ·
          refine ⟨7044371119155596672223337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9392494825540795562964449 7044371119155596672223337)
          ·
            refine ⟨5283278339366697504167503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7044371119155596672223337 5283278339366697504167503)
            ·
              refine ⟨7924917509050046256251255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5283278339366697504167503 7924917509050046256251255)
              ·
                refine ⟨11887376263575069384376883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7924917509050046256251255 11887376263575069384376883)
                ·
                  refine ⟨17831064395362604076565325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11887376263575069384376883 17831064395362604076565325)
                  ·
                    refine ⟨6686649148260976528711997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17831064395362604076565325 6686649148260976528711997)
                    ·
                      refine ⟨2507493430597866198266999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6686649148260976528711997 2507493430597866198266999)
                      ·
                        rfl

theorem cell23_4883326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_4883326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883326 prefixEnd_4883326 := by exact prefixLift 4883326
  have htrace : WordTrace (prefixWord ++ tailWord_4883326) baseStart_4883326 baseEnd_4883326 := by
    simpa [prefixWord, tailWord_4883326, baseEnd_4883326] using wordTrace_append hprefix tailTrace_4883326
  have hstable : (prefixWord ++ tailWord_4883326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883326).length < 2 ^ (prefixWord ++ tailWord_4883326).sum := by decide
  have hdescent : baseEnd_4883326 < baseStart_4883326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883328 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 4]
def baseStart_4883328 : Nat := 118140960795 + 4883328 * 2 ^ 59
def prefixEnd_4883328 : Nat := 4983230072969 + 3 ^ 40 * 4883328 * 2
def baseEnd_4883328 : Nat := 2507494457559175190441989

theorem tailTrace_4883328 : CollatzResearch.WordTrace tailWord_4883328 prefixEnd_4883328 2507494457559175190441989 := by
  unfold tailWord_4883328
  simp only [CollatzResearch.WordTrace]
  refine ⟨89054802226272068434449319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118739736301696091245932425 89054802226272068434449319)
  ·
    refine ⟨133582203339408102651673979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89054802226272068434449319 133582203339408102651673979)
    ·
      refine ⟨200373305009112153977510969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133582203339408102651673979 200373305009112153977510969)
      ·
        refine ⟨150279978756834115483133227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200373305009112153977510969 150279978756834115483133227)
        ·
          refine ⟨225419968135251173224699841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150279978756834115483133227 225419968135251173224699841)
          ·
            refine ⟨169064976101438379918524881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225419968135251173224699841 169064976101438379918524881)
            ·
              refine ⟨126798732076078784938893661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169064976101438379918524881 126798732076078784938893661)
              ·
                refine ⟨47549524528529544352085123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126798732076078784938893661 47549524528529544352085123)
                ·
                  refine ⟨71324286792794316528127685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47549524528529544352085123 71324286792794316528127685)
                  ·
                    refine ⟨13373303773648934349023941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71324286792794316528127685 13373303773648934349023941)
                    ·
                      refine ⟨2507494457559175190441989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13373303773648934349023941 2507494457559175190441989)
                      ·
                        rfl

theorem cell23_4883328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_4883328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883328 prefixEnd_4883328 := by exact prefixLift 4883328
  have htrace : WordTrace (prefixWord ++ tailWord_4883328) baseStart_4883328 baseEnd_4883328 := by
    simpa [prefixWord, tailWord_4883328, baseEnd_4883328] using wordTrace_append hprefix tailTrace_4883328
  have hstable : (prefixWord ++ tailWord_4883328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883328).length < 2 ^ (prefixWord ++ tailWord_4883328).sum := by decide
  have hdescent : baseEnd_4883328 < baseStart_4883328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883415 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 7, 4]
def baseStart_4883415 : Nat := 118140960795 + 4883415 * 2 ^ 59
def prefixEnd_4883415 : Nat := 4983230072969 + 3 ^ 40 * 4883415 * 2
def baseEnd_4883415 : Nat := 835846376792038783351363

theorem tailTrace_4883415 : CollatzResearch.WordTrace tailWord_4883415 prefixEnd_4883415 835846376792038783351363 := by
  unfold tailWord_4883415
  simp only [CollatzResearch.WordTrace]
  refine ⟨178112777603228950727315699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118741851735485967151543799 178112777603228950727315699)
  ·
    refine ⟨267169166404843426090973549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178112777603228950727315699 267169166404843426090973549)
    ·
      refine ⟨100188437401816284784115081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267169166404843426090973549 100188437401816284784115081)
      ·
        refine ⟨75141328051362213588086311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100188437401816284784115081 75141328051362213588086311)
        ·
          refine ⟨112711992077043320382129467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75141328051362213588086311 112711992077043320382129467)
          ·
            refine ⟨169067988115564980573194201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112711992077043320382129467 169067988115564980573194201)
            ·
              refine ⟨126800991086673735429895651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169067988115564980573194201 126800991086673735429895651)
              ·
                refine ⟨190201486630010603144843477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126800991086673735429895651 190201486630010603144843477)
                ·
                  refine ⟨4457847342890873511207269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 190201486630010603144843477 4457847342890873511207269)
                  ·
                    refine ⟨835846376792038783351363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4457847342890873511207269 835846376792038783351363)
                    ·
                      rfl

theorem cell23_4883415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 4].length) (baseStart_4883415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883415 prefixEnd_4883415 := by exact prefixLift 4883415
  have htrace : WordTrace (prefixWord ++ tailWord_4883415) baseStart_4883415 baseEnd_4883415 := by
    simpa [prefixWord, tailWord_4883415, baseEnd_4883415] using wordTrace_append hprefix tailTrace_4883415
  have hstable : (prefixWord ++ tailWord_4883415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883415).length < 2 ^ (prefixWord ++ tailWord_4883415).sum := by decide
  have hdescent : baseEnd_4883415 < baseStart_4883415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883425 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 3, 4, 3]
def baseStart_4883425 : Nat := 118140960795 + 4883425 * 2 ^ 59
def prefixEnd_4883425 : Nat := 4983230072969 + 3 ^ 40 * 4883425 * 2
def baseEnd_4883425 : Nat := 2507544265182661310929043

theorem tailTrace_4883425 : CollatzResearch.WordTrace tailWord_4883425 prefixEnd_4883425 2507544265182661310929043 := by
  unfold tailWord_4883425
  simp only [CollatzResearch.WordTrace]
  refine ⟨178113142333192722435179729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118742094888795148290119819 178113142333192722435179729)
  ·
    refine ⟨133584856749894541826384797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178113142333192722435179729 133584856749894541826384797)
    ·
      refine ⟨50094321281210453184894299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133584856749894541826384797 50094321281210453184894299)
      ·
        refine ⟨75141481921815679777341449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50094321281210453184894299 75141481921815679777341449)
        ·
          refine ⟨56356111441361759833006087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75141481921815679777341449 56356111441361759833006087)
          ·
            refine ⟨84534167162042639749509131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56356111441361759833006087 84534167162042639749509131)
            ·
              refine ⟨126801250743063959624263697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84534167162042639749509131 126801250743063959624263697)
              ·
                refine ⟨95100938057297969718197773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126801250743063959624263697 95100938057297969718197773)
                ·
                  refine ⟨35662851771486738644324165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95100938057297969718197773 35662851771486738644324165)
                  ·
                    refine ⟨6686784707153763495810781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35662851771486738644324165 6686784707153763495810781)
                    ·
                      refine ⟨2507544265182661310929043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6686784707153763495810781 2507544265182661310929043)
                      ·
                        rfl

theorem cell23_4883425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_4883425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883425 prefixEnd_4883425 := by exact prefixLift 4883425
  have htrace : WordTrace (prefixWord ++ tailWord_4883425) baseStart_4883425 baseEnd_4883425 := by
    simpa [prefixWord, tailWord_4883425, baseEnd_4883425] using wordTrace_append hprefix tailTrace_4883425
  have hstable : (prefixWord ++ tailWord_4883425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883425).length < 2 ^ (prefixWord ++ tailWord_4883425).sum := by decide
  have hdescent : baseEnd_4883425 < baseStart_4883425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883466 : List Nat := [3, 1, 2, 2, 3, 2, 2, 3, 1, 4]
def baseStart_4883466 : Nat := 118140960795 + 4883466 * 2 ^ 59
def prefixEnd_4883466 : Nat := 4983230072969 + 3 ^ 40 * 4883466 * 2
def baseEnd_4883466 : Nat := 835855105963165216838785

theorem tailTrace_4883466 : CollatzResearch.WordTrace tailWord_4883466 prefixEnd_4883466 835855105963165216838785 := by
  unfold tailWord_4883466
  simp only [CollatzResearch.WordTrace]
  refine ⟨44528659431511046609355563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118743091817362790958281501 44528659431511046609355563)
  ·
    refine ⟨66792989147266569914033345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44528659431511046609355563 66792989147266569914033345)
    ·
      refine ⟨50094741860449927435525009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66792989147266569914033345 50094741860449927435525009)
      ·
        refine ⟨37571056395337445576643757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50094741860449927435525009 37571056395337445576643757)
        ·
          refine ⟨14089146148251542091241409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37571056395337445576643757 14089146148251542091241409)
          ·
            refine ⟨10566859611188656568431057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14089146148251542091241409 10566859611188656568431057)
            ·
              refine ⟨7925144708391492426323293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10566859611188656568431057 7925144708391492426323293)
              ·
                refine ⟨2971929265646809659871235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7925144708391492426323293 2971929265646809659871235)
                ·
                  refine ⟨4457893898470214489806853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2971929265646809659871235 4457893898470214489806853)
                  ·
                    refine ⟨835855105963165216838785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4457893898470214489806853 835855105963165216838785)
                    ·
                      rfl

theorem cell23_4883466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_4883466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883466 prefixEnd_4883466 := by exact prefixLift 4883466
  have htrace : WordTrace (prefixWord ++ tailWord_4883466) baseStart_4883466 baseEnd_4883466 := by
    simpa [prefixWord, tailWord_4883466, baseEnd_4883466] using wordTrace_append hprefix tailTrace_4883466
  have hstable : (prefixWord ++ tailWord_4883466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883466).length < 2 ^ (prefixWord ++ tailWord_4883466).sum := by decide
  have hdescent : baseEnd_4883466 < baseStart_4883466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883479 : List Nat := [1, 1, 3, 5, 1, 3, 1, 2, 6]
def baseStart_4883479 : Nat := 118140960795 + 4883479 * 2 ^ 59
def prefixEnd_4883479 : Nat := 4983230072969 + 3 ^ 40 * 4883479 * 2
def baseEnd_4883479 : Nat := 278619110348667122183755

theorem tailTrace_4883479 : CollatzResearch.WordTrace tailWord_4883479 prefixEnd_4883479 278619110348667122183755 := by
  unfold tailWord_4883479
  simp only [CollatzResearch.WordTrace]
  refine ⟨178115111874997089657645491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118743407916664726438430327 178115111874997089657645491)
  ·
    refine ⟨267172667812495634486468237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178115111874997089657645491 267172667812495634486468237)
    ·
      refine ⟨100189750429685862932425589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267172667812495634486468237 100189750429685862932425589)
      ·
        refine ⟨9392789102783049649914899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100189750429685862932425589 9392789102783049649914899)
        ·
          refine ⟨14089183654174574474872349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9392789102783049649914899 14089183654174574474872349)
          ·
            refine ⟨5283443870315465428077131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14089183654174574474872349 5283443870315465428077131)
            ·
              refine ⟨7925165805473198142115697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5283443870315465428077131 7925165805473198142115697)
              ·
                refine ⟨5943874354104898606586773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7925165805473198142115697 5943874354104898606586773)
                ·
                  refine ⟨278619110348667122183755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5943874354104898606586773 278619110348667122183755)
                  ·
                    rfl

theorem cell23_4883479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 6].length) (baseStart_4883479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883479 prefixEnd_4883479 := by exact prefixLift 4883479
  have htrace : WordTrace (prefixWord ++ tailWord_4883479) baseStart_4883479 baseEnd_4883479 := by
    simpa [prefixWord, tailWord_4883479, baseEnd_4883479] using wordTrace_append hprefix tailTrace_4883479
  have hstable : (prefixWord ++ tailWord_4883479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883479).length < 2 ^ (prefixWord ++ tailWord_4883479).sum := by decide
  have hdescent : baseEnd_4883479 < baseStart_4883479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883489 : List Nat := [1, 2, 3, 2, 3, 1, 1, 3, 3, 1, 3]
def baseStart_4883489 : Nat := 118140960795 + 4883489 * 2 ^ 59
def prefixEnd_4883489 : Nat := 4983230072969 + 3 ^ 40 * 4883489 * 2
def baseEnd_4883489 : Nat := 2507577127944549060528749

theorem tailTrace_4883489 : CollatzResearch.WordTrace tailWord_4883489 prefixEnd_4883489 2507577127944549060528749 := by
  unfold tailWord_4883489
  simp only [CollatzResearch.WordTrace]
  refine ⟨178115476604960861365509521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118743651069973907577006347 178115476604960861365509521)
  ·
    refine ⟨133586607453720646024132141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178115476604960861365509521 133586607453720646024132141)
    ·
      refine ⟨50094977795145242259049553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133586607453720646024132141 50094977795145242259049553)
      ·
        refine ⟨37571233346358931694287165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50094977795145242259049553 37571233346358931694287165)
        ·
          refine ⟨14089212504884599385357687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37571233346358931694287165 14089212504884599385357687)
          ·
            refine ⟨21133818757326899078036531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14089212504884599385357687 21133818757326899078036531)
            ·
              refine ⟨31700728135990348617054797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21133818757326899078036531 31700728135990348617054797)
              ·
                refine ⟨11887773050996380731395549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31700728135990348617054797 11887773050996380731395549)
                ·
                  refine ⟨4457914894123642774273331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11887773050996380731395549 4457914894123642774273331)
                  ·
                    refine ⟨6686872341185464161409997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4457914894123642774273331 6686872341185464161409997)
                    ·
                      refine ⟨2507577127944549060528749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6686872341185464161409997 2507577127944549060528749)
                      ·
                        rfl

theorem cell23_4883489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_4883489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883489 prefixEnd_4883489 := by exact prefixLift 4883489
  have htrace : WordTrace (prefixWord ++ tailWord_4883489) baseStart_4883489 baseEnd_4883489 := by
    simpa [prefixWord, tailWord_4883489, baseEnd_4883489] using wordTrace_append hprefix tailTrace_4883489
  have hstable : (prefixWord ++ tailWord_4883489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883489).length < 2 ^ (prefixWord ++ tailWord_4883489).sum := by decide
  have hdescent : baseEnd_4883489 < baseStart_4883489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883526 : List Nat := [6, 1, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_4883526 : Nat := 118140960795 + 4883526 * 2 ^ 59
def prefixEnd_4883526 : Nat := 4983230072969 + 3 ^ 40 * 4883526 * 2
def baseEnd_4883526 : Nat := 835865375576255138588693

theorem tailTrace_4883526 : CollatzResearch.WordTrace tailWord_4883526 prefixEnd_4883526 835865375576255138588693 := by
  unfold tailWord_4883526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5566150815807088021393951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 118744550737217877789737621 5566150815807088021393951)
  ·
    refine ⟨8349226223710632032090927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5566150815807088021393951 8349226223710632032090927)
    ·
      refine ⟨12523839335565948048136391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8349226223710632032090927 12523839335565948048136391)
      ·
        refine ⟨18785759003348922072204587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12523839335565948048136391 18785759003348922072204587)
        ·
          refine ⟨28178638505023383108306881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18785759003348922072204587 28178638505023383108306881)
          ·
            refine ⟨21133978878767537331230161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28178638505023383108306881 21133978878767537331230161)
            ·
              refine ⟨15850484159075652998422621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21133978878767537331230161 15850484159075652998422621)
              ·
                refine ⟨5943931559653369874408483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15850484159075652998422621 5943931559653369874408483)
                ·
                  refine ⟨8915897339480054811612725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5943931559653369874408483 8915897339480054811612725)
                  ·
                    refine ⟨835865375576255138588693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8915897339480054811612725 835865375576255138588693)
                    ·
                      rfl

theorem cell23_4883526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_4883526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883526 prefixEnd_4883526 := by exact prefixLift 4883526
  have htrace : WordTrace (prefixWord ++ tailWord_4883526) baseStart_4883526 baseEnd_4883526 := by
    simpa [prefixWord, tailWord_4883526, baseEnd_4883526] using wordTrace_append hprefix tailTrace_4883526
  have hstable : (prefixWord ++ tailWord_4883526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883526).length < 2 ^ (prefixWord ++ tailWord_4883526).sum := by decide
  have hdescent : baseEnd_4883526 < baseStart_4883526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883532 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 5, 2, 3]
def baseStart_4883532 : Nat := 118140960795 + 4883532 * 2 ^ 59
def prefixEnd_4883532 : Nat := 4983230072969 + 3 ^ 40 * 4883532 * 2
def baseEnd_4883532 : Nat := 2507599207612692392291051

theorem tailTrace_4883532 : CollatzResearch.WordTrace tailWord_4883532 prefixEnd_4883532 2507599207612692392291051 := by
  unfold tailWord_4883532
  simp only [CollatzResearch.WordTrace]
  refine ⟨89058522471902539854662425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118744696629203386472883233 89058522471902539854662425)
  ·
    refine ⟨66793891853926904890996819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89058522471902539854662425 66793891853926904890996819)
    ·
      refine ⟨100190837780890357336495229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66793891853926904890996819 100190837780890357336495229)
      ·
        refine ⟨37571564167833884001185711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100190837780890357336495229 37571564167833884001185711)
        ·
          refine ⟨56357346251750826001778567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37571564167833884001185711 56357346251750826001778567)
          ·
            refine ⟨84536019377626239002667851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56357346251750826001778567 84536019377626239002667851)
            ·
              refine ⟨126804029066439358504001777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84536019377626239002667851 126804029066439358504001777)
              ·
                refine ⟨95103021799829518878001333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126804029066439358504001777 95103021799829518878001333)
                ·
                  refine ⟨8915908293734017394812625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95103021799829518878001333 8915908293734017394812625)
                  ·
                    refine ⟨6686931220300513046109469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8915908293734017394812625 6686931220300513046109469)
                    ·
                      refine ⟨2507599207612692392291051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6686931220300513046109469 2507599207612692392291051)
                      ·
                        rfl

theorem cell23_4883532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_4883532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883532 prefixEnd_4883532 := by exact prefixLift 4883532
  have htrace : WordTrace (prefixWord ++ tailWord_4883532) baseStart_4883532 baseEnd_4883532 := by
    simpa [prefixWord, tailWord_4883532, baseEnd_4883532] using wordTrace_append hprefix tailTrace_4883532
  have hstable : (prefixWord ++ tailWord_4883532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883532).length < 2 ^ (prefixWord ++ tailWord_4883532).sum := by decide
  have hdescent : baseEnd_4883532 < baseStart_4883532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883555 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 6]
def baseStart_4883555 : Nat := 118140960795 + 4883555 * 2 ^ 59
def prefixEnd_4883555 : Nat := 4983230072969 + 3 ^ 40 * 4883555 * 2
def baseEnd_4883555 : Nat := 2507611017667745802303445

theorem tailTrace_4883555 : CollatzResearch.WordTrace tailWord_4883555 prefixEnd_4883555 2507611017667745802303445 := by
  unfold tailWord_4883555
  simp only [CollatzResearch.WordTrace]
  refine ⟨178117883822721754637412119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118745255881814503091608079 178117883822721754637412119)
  ·
    refine ⟨267176825734082631956118179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178117883822721754637412119 267176825734082631956118179)
    ·
      refine ⟨400765238601123947934177269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267176825734082631956118179 400765238601123947934177269)
      ·
        refine ⟨37571741118855370118829119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 400765238601123947934177269 37571741118855370118829119)
        ·
          refine ⟨56357611678283055178243679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37571741118855370118829119 56357611678283055178243679)
          ·
            refine ⟨84536417517424582767365519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56357611678283055178243679 84536417517424582767365519)
            ·
              refine ⟨126804626276136874151048279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84536417517424582767365519 126804626276136874151048279)
              ·
                refine ⟨190206939414205311226572419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126804626276136874151048279 190206939414205311226572419)
                ·
                  refine ⟨285310409121307966839858629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190206939414205311226572419 285310409121307966839858629)
                  ·
                    refine ⟨53495701710245243782473493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 285310409121307966839858629 53495701710245243782473493)
                    ·
                      refine ⟨2507611017667745802303445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53495701710245243782473493 2507611017667745802303445)
                      ·
                        rfl

theorem cell23_4883555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_4883555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883555 prefixEnd_4883555 := by exact prefixLift 4883555
  have htrace : WordTrace (prefixWord ++ tailWord_4883555) baseStart_4883555 baseEnd_4883555 := by
    simpa [prefixWord, tailWord_4883555, baseEnd_4883555] using wordTrace_append hprefix tailTrace_4883555
  have hstable : (prefixWord ++ tailWord_4883555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883555).length < 2 ^ (prefixWord ++ tailWord_4883555).sum := by decide
  have hdescent : baseEnd_4883555 < baseStart_4883555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883566 : List Nat := [4, 1, 2, 2, 1, 2, 3, 2, 1, 2, 3]
def baseStart_4883566 : Nat := 118140960795 + 4883566 * 2 ^ 59
def prefixEnd_4883566 : Nat := 4983230072969 + 3 ^ 40 * 4883566 * 2
def baseEnd_4883566 : Nat := 2507616665954945259265895

theorem tailTrace_4883566 : CollatzResearch.WordTrace tailWord_4883566 prefixEnd_4883566 2507616665954945259265895 := by
  unfold tailWord_4883566
  simp only [CollatzResearch.WordTrace]
  refine ⟨22264785628210237939507819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118745523350454602344041701 22264785628210237939507819)
  ·
    refine ⟨33397178442315356909261729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22264785628210237939507819 33397178442315356909261729)
    ·
      refine ⟨25047883831736517681946297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33397178442315356909261729 25047883831736517681946297)
      ·
        refine ⟨18785912873802388261459723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25047883831736517681946297 18785912873802388261459723)
        ·
          refine ⟨28178869310703582392189585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18785912873802388261459723 28178869310703582392189585)
          ·
            refine ⟨21134151983027686794142189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28178869310703582392189585 21134151983027686794142189)
            ·
              refine ⟨7925306993635382547803321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21134151983027686794142189 7925306993635382547803321)
              ·
                refine ⟨5943980245226536910852491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7925306993635382547803321 5943980245226536910852491)
                ·
                  refine ⟨8915970367839805366278737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5943980245226536910852491 8915970367839805366278737)
                  ·
                    refine ⟨6686977775879854024709053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8915970367839805366278737 6686977775879854024709053)
                    ·
                      refine ⟨2507616665954945259265895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6686977775879854024709053 2507616665954945259265895)
                      ·
                        rfl

theorem cell23_4883566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_4883566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883566 prefixEnd_4883566 := by exact prefixLift 4883566
  have htrace : WordTrace (prefixWord ++ tailWord_4883566) baseStart_4883566 baseEnd_4883566 := by
    simpa [prefixWord, tailWord_4883566, baseEnd_4883566] using wordTrace_append hprefix tailTrace_4883566
  have hstable : (prefixWord ++ tailWord_4883566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883566).length < 2 ^ (prefixWord ++ tailWord_4883566).sum := by decide
  have hdescent : baseEnd_4883566 < baseStart_4883566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883595 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 3, 8]
def baseStart_4883595 : Nat := 118140960795 + 4883595 * 2 ^ 59
def prefixEnd_4883595 : Nat := 4983230072969 + 3 ^ 40 * 4883595 * 2
def baseEnd_4883595 : Nat := 835877185631308548601087

theorem tailTrace_4883595 : CollatzResearch.WordTrace tailWord_4883595 prefixEnd_4883595 835877185631308548601087 := by
  unfold tailWord_4883595
  simp only [CollatzResearch.WordTrace]
  refine ⟨178119342742576841468868239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118746228495051227645912159 178119342742576841468868239)
  ·
    refine ⟨267179014113865262203302359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178119342742576841468868239 267179014113865262203302359)
    ·
      refine ⟨400768521170797893304953539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267179014113865262203302359 400768521170797893304953539)
      ·
        refine ⟨601152781756196839957430309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400768521170797893304953539 601152781756196839957430309)
        ·
          refine ⟨112716146579286907492018183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 601152781756196839957430309 112716146579286907492018183)
          ·
            refine ⟨169074219868930361238027275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112716146579286907492018183 169074219868930361238027275)
            ·
              refine ⟨253611329803395541857040913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169074219868930361238027275 253611329803395541857040913)
              ·
                refine ⟨190208497352546656392780685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 253611329803395541857040913 190208497352546656392780685)
                ·
                  refine ⟨71328186507204996147292757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190208497352546656392780685 71328186507204996147292757)
                  ·
                    refine ⟨835877185631308548601087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71328186507204996147292757 835877185631308548601087)
                    ·
                      rfl

theorem cell23_4883595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 8].length) (baseStart_4883595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883595 prefixEnd_4883595 := by exact prefixLift 4883595
  have htrace : WordTrace (prefixWord ++ tailWord_4883595) baseStart_4883595 baseEnd_4883595 := by
    simpa [prefixWord, tailWord_4883595, baseEnd_4883595] using wordTrace_append hprefix tailTrace_4883595
  have hstable : (prefixWord ++ tailWord_4883595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883595).length < 2 ^ (prefixWord ++ tailWord_4883595).sum := by decide
  have hdescent : baseEnd_4883595 < baseStart_4883595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883612 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 1, 8]
def baseStart_4883612 : Nat := 118140960795 + 4883612 * 2 ^ 59
def prefixEnd_4883612 : Nat := 4983230072969 + 3 ^ 40 * 4883612 * 2
def baseEnd_4883612 : Nat := 835880095355017359763561

theorem tailTrace_4883612 : CollatzResearch.WordTrace tailWord_4883612 prefixEnd_4883612 835880095355017359763561 := by
  unfold tailWord_4883612
  simp only [CollatzResearch.WordTrace]
  refine ⟨89059981391757626686118545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118746641855676835581491393 89059981391757626686118545)
  ·
    refine ⟨66794986043818220014588909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89059981391757626686118545 66794986043818220014588909)
    ·
      refine ⟨25048119766431832505470841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66794986043818220014588909 25048119766431832505470841)
      ·
        refine ⟨18786089824823874379103131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25048119766431832505470841 18786089824823874379103131)
        ·
          refine ⟨28179134737235811568654697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18786089824823874379103131 28179134737235811568654697)
          ·
            refine ⟨21134351052926858676491023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28179134737235811568654697 21134351052926858676491023)
            ·
              refine ⟨31701526579390288014736535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21134351052926858676491023 31701526579390288014736535)
              ·
                refine ⟨47552289869085432022104803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31701526579390288014736535 47552289869085432022104803)
                ·
                  refine ⟨71328434803628148033157205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47552289869085432022104803 71328434803628148033157205)
                  ·
                    refine ⟨835880095355017359763561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71328434803628148033157205 835880095355017359763561)
                    ·
                      rfl

theorem cell23_4883612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_4883612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883612 prefixEnd_4883612 := by exact prefixLift 4883612
  have htrace : WordTrace (prefixWord ++ tailWord_4883612) baseStart_4883612 baseEnd_4883612 := by
    simpa [prefixWord, tailWord_4883612, baseEnd_4883612] using wordTrace_append hprefix tailTrace_4883612
  have hstable : (prefixWord ++ tailWord_4883612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883612).length < 2 ^ (prefixWord ++ tailWord_4883612).sum := by decide
  have hdescent : baseEnd_4883612 < baseStart_4883612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883679 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 2, 5, 2]
def baseStart_4883679 : Nat := 118140960795 + 4883679 * 2 ^ 59
def prefixEnd_4883679 : Nat := 4983230072969 + 3 ^ 40 * 4883679 * 2
def baseEnd_4883679 : Nat := 2507674689268903317152875

theorem tailTrace_4883679 : CollatzResearch.WordTrace tailWord_4883679 prefixEnd_4883679 2507674689268903317152875 := by
  unfold tailWord_4883679
  simp only [CollatzResearch.WordTrace]
  refine ⟨178122406474272523814926091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118748270982848349209950727 178122406474272523814926091)
  ·
    refine ⟨267183609711408785722389137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178122406474272523814926091 267183609711408785722389137)
    ·
      refine ⟨200387707283556589291791853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267183609711408785722389137 200387707283556589291791853)
      ·
        refine ⟨75145390231333720984421945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200387707283556589291791853 75145390231333720984421945)
        ·
          refine ⟨56359042673500290738316459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75145390231333720984421945 56359042673500290738316459)
          ·
            refine ⟨84538564010250436107474689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56359042673500290738316459 84538564010250436107474689)
            ·
              refine ⟨63403923007687827080606017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84538564010250436107474689 63403923007687827080606017)
              ·
                refine ⟨47552942255765870310454513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63403923007687827080606017 47552942255765870310454513)
                ·
                  refine ⟨35664706691824402732840885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47552942255765870310454513 35664706691824402732840885)
                  ·
                    refine ⟨3343566252358537756203833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35664706691824402732840885 3343566252358537756203833)
                    ·
                      refine ⟨2507674689268903317152875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3343566252358537756203833 2507674689268903317152875)
                      ·
                        rfl

theorem cell23_4883679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 5, 2].length) (baseStart_4883679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883679 prefixEnd_4883679 := by exact prefixLift 4883679
  have htrace : WordTrace (prefixWord ++ tailWord_4883679) baseStart_4883679 baseEnd_4883679 := by
    simpa [prefixWord, tailWord_4883679, baseEnd_4883679] using wordTrace_append hprefix tailTrace_4883679
  have hstable : (prefixWord ++ tailWord_4883679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883679).length < 2 ^ (prefixWord ++ tailWord_4883679).sum := by decide
  have hdescent : baseEnd_4883679 < baseStart_4883679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883693 : List Nat := [1, 5, 1, 2, 2, 3, 1, 3, 5]
def baseStart_4883693 : Nat := 118140960795 + 4883693 * 2 ^ 59
def prefixEnd_4883693 : Nat := 4983230072969 + 3 ^ 40 * 4883693 * 2
def baseEnd_4883693 : Nat := 278631319777562918041979

theorem tailTrace_4883693 : CollatzResearch.WordTrace tailWord_4883693 prefixEnd_4883693 278631319777562918041979 := by
  unfold tailWord_4883693
  simp only [CollatzResearch.WordTrace]
  refine ⟨178122917096221804205935733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118748611397481202803957155 178122917096221804205935733)
  ·
    refine ⟨16699023477770794144306475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 178122917096221804205935733 16699023477770794144306475)
    ·
      refine ⟨25048535216656191216459713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16699023477770794144306475 25048535216656191216459713)
      ·
        refine ⟨18786401412492143412344785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25048535216656191216459713 18786401412492143412344785)
        ·
          refine ⟨14089801059369107559258589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18786401412492143412344785 14089801059369107559258589)
          ·
            refine ⟨5283675397263415334721971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14089801059369107559258589 5283675397263415334721971)
            ·
              refine ⟨7925513095895123002082957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5283675397263415334721971 7925513095895123002082957)
              ·
                refine ⟨2972067410960671125781109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7925513095895123002082957 2972067410960671125781109)
                ·
                  refine ⟨278631319777562918041979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2972067410960671125781109 278631319777562918041979)
                  ·
                    rfl

theorem cell23_4883693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_4883693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883693 prefixEnd_4883693 := by exact prefixLift 4883693
  have htrace : WordTrace (prefixWord ++ tailWord_4883693) baseStart_4883693 baseEnd_4883693 := by
    simpa [prefixWord, tailWord_4883693, baseEnd_4883693] using wordTrace_append hprefix tailTrace_4883693
  have hstable : (prefixWord ++ tailWord_4883693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883693).length < 2 ^ (prefixWord ++ tailWord_4883693).sum := by decide
  have hdescent : baseEnd_4883693 < baseStart_4883693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883729 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 3]
def baseStart_4883729 : Nat := 118140960795 + 4883729 * 2 ^ 59
def prefixEnd_4883729 : Nat := 4983230072969 + 3 ^ 40 * 4883729 * 2
def baseEnd_4883729 : Nat := 2507700363301628121527645

theorem tailTrace_4883729 : CollatzResearch.WordTrace tailWord_4883729 prefixEnd_4883729 2507700363301628121527645 := by
  unfold tailWord_4883729
  simp only [CollatzResearch.WordTrace]
  refine ⟨178124230124091382354246241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118749486749394254902830827 178124230124091382354246241)
  ·
    refine ⟨133593172593068536765684681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178124230124091382354246241 133593172593068536765684681)
    ·
      refine ⟨100194879444801402574263511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133593172593068536765684681 100194879444801402574263511)
      ·
        refine ⟨150292319167202103861395267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100194879444801402574263511 150292319167202103861395267)
        ·
          refine ⟨225438478750803155792092901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150292319167202103861395267 225438478750803155792092901)
          ·
            refine ⟨42269714765775591711017419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 225438478750803155792092901 42269714765775591711017419)
            ·
              refine ⟨63404572148663387566526129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42269714765775591711017419 63404572148663387566526129)
              ·
                refine ⟨47553429111497540674894597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63404572148663387566526129 47553429111497540674894597)
                ·
                  refine ⟨8916267958405788876542737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47553429111497540674894597 8916267958405788876542737)
                  ·
                    refine ⟨6687200968804341657407053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8916267958405788876542737 6687200968804341657407053)
                    ·
                      refine ⟨2507700363301628121527645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6687200968804341657407053 2507700363301628121527645)
                      ·
                        rfl

theorem cell23_4883729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 3].length) (baseStart_4883729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883729 prefixEnd_4883729 := by exact prefixLift 4883729
  have htrace : WordTrace (prefixWord ++ tailWord_4883729) baseStart_4883729 baseEnd_4883729 := by
    simpa [prefixWord, tailWord_4883729, baseEnd_4883729] using wordTrace_append hprefix tailTrace_4883729
  have hstable : (prefixWord ++ tailWord_4883729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883729).length < 2 ^ (prefixWord ++ tailWord_4883729).sum := by decide
  have hdescent : baseEnd_4883729 < baseStart_4883729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883776 : List Nat := [2, 1, 1, 2, 2, 1, 4, 3, 3, 1, 3]
def baseStart_4883776 : Nat := 118140960795 + 4883776 * 2 ^ 59
def prefixEnd_4883776 : Nat := 4983230072969 + 3 ^ 40 * 4883776 * 2
def baseEnd_4883776 : Nat := 2507724496892389437639929

theorem tailTrace_4883776 : CollatzResearch.WordTrace tailWord_4883776 prefixEnd_4883776 2507724496892389437639929 := by
  unfold tailWord_4883776
  simp only [CollatzResearch.WordTrace]
  refine ⟨89062972177460554690603591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118750629569947406254138121 89062972177460554690603591)
  ·
    refine ⟨133594458266190832035905387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89062972177460554690603591 133594458266190832035905387)
    ·
      refine ⟨200391687399286248053858081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133594458266190832035905387 200391687399286248053858081)
      ·
        refine ⟨150293765549464686040393561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200391687399286248053858081 150293765549464686040393561)
        ·
          refine ⟨112720324162098514530295171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150293765549464686040393561 112720324162098514530295171)
          ·
            refine ⟨169080486243147771795442757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112720324162098514530295171 169080486243147771795442757)
            ·
              refine ⟨31702591170590207211645517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169080486243147771795442757 31702591170590207211645517)
              ·
                refine ⟨11888471688971327704367069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31702591170590207211645517 11888471688971327704367069)
                ·
                  refine ⟨4458176883364247889137651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11888471688971327704367069 4458176883364247889137651)
                  ·
                    refine ⟨6687265325046371833706477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4458176883364247889137651 6687265325046371833706477)
                    ·
                      refine ⟨2507724496892389437639929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6687265325046371833706477 2507724496892389437639929)
                      ·
                        rfl

theorem cell23_4883776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 3, 1, 3].length) (baseStart_4883776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883776 prefixEnd_4883776 := by exact prefixLift 4883776
  have htrace : WordTrace (prefixWord ++ tailWord_4883776) baseStart_4883776 baseEnd_4883776 := by
    simpa [prefixWord, tailWord_4883776, baseEnd_4883776] using wordTrace_append hprefix tailTrace_4883776
  have hstable : (prefixWord ++ tailWord_4883776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883776).length < 2 ^ (prefixWord ++ tailWord_4883776).sum := by decide
  have hdescent : baseEnd_4883776 < baseStart_4883776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883786 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 4, 3, 2]
def baseStart_4883786 : Nat := 118140960795 + 4883786 * 2 ^ 59
def prefixEnd_4883786 : Nat := 4983230072969 + 3 ^ 40 * 4883786 * 2
def baseEnd_4883786 : Nat := 2507729631698934398514883

theorem tailTrace_4883786 : CollatzResearch.WordTrace tailWord_4883786 prefixEnd_4883786 2507729631698934398514883 := by
  unfold tailWord_4883786
  simp only [CollatzResearch.WordTrace]
  refine ⟨44531577271221220272267803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118750872723256587392714141 44531577271221220272267803)
  ·
    refine ⟨66797365906831830408401705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44531577271221220272267803 66797365906831830408401705)
    ·
      refine ⟨50098024430123872806301279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66797365906831830408401705 50098024430123872806301279)
      ·
        refine ⟨75147036645185809209451919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50098024430123872806301279 75147036645185809209451919)
        ·
          refine ⟨112720554967778713814177879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75147036645185809209451919 112720554967778713814177879)
          ·
            refine ⟨169080832451668070721266819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112720554967778713814177879 169080832451668070721266819)
            ·
              refine ⟨253621248677502106081900229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169080832451668070721266819 253621248677502106081900229)
              ·
                refine ⟨47553984127031644890356293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 253621248677502106081900229 47553984127031644890356293)
                ·
                  refine ⟨8916372023818433416941805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47553984127031644890356293 8916372023818433416941805)
                  ·
                    refine ⟨3343639508931912531353177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8916372023818433416941805 3343639508931912531353177)
                    ·
                      refine ⟨2507729631698934398514883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3343639508931912531353177 2507729631698934398514883)
                      ·
                        rfl

theorem cell23_4883786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 4, 3, 2].length) (baseStart_4883786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883786 prefixEnd_4883786 := by exact prefixLift 4883786
  have htrace : WordTrace (prefixWord ++ tailWord_4883786) baseStart_4883786 baseEnd_4883786 := by
    simpa [prefixWord, tailWord_4883786, baseEnd_4883786] using wordTrace_append hprefix tailTrace_4883786
  have hstable : (prefixWord ++ tailWord_4883786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883786).length < 2 ^ (prefixWord ++ tailWord_4883786).sum := by decide
  have hdescent : baseEnd_4883786 < baseStart_4883786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883796 : List Nat := [2, 4, 1, 1, 2, 1, 2, 4, 1, 5]
def baseStart_4883796 : Nat := 118140960795 + 4883796 * 2 ^ 59
def prefixEnd_4883796 : Nat := 4983230072969 + 3 ^ 40 * 4883796 * 2
def baseEnd_4883796 : Nat := 835911588835159786463279

theorem tailTrace_4883796 : CollatzResearch.WordTrace tailWord_4883796 prefixEnd_4883796 835911588835159786463279 := by
  unfold tailWord_4883796
  simp only [CollatzResearch.WordTrace]
  refine ⟨89063336907424326398467621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118751115876565768531290161 89063336907424326398467621)
  ·
    refine ⟨16699375670142061199712679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89063336907424326398467621 16699375670142061199712679)
    ·
      refine ⟨25049063505213091799569019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16699375670142061199712679 25049063505213091799569019)
      ·
        refine ⟨37573595257819637699353529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25049063505213091799569019 37573595257819637699353529)
        ·
          refine ⟨28180196443364728274515147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37573595257819637699353529 28180196443364728274515147)
          ·
            refine ⟨42270294665047092411772721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28180196443364728274515147 42270294665047092411772721)
            ·
              refine ⟨31702720998785319308829541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42270294665047092411772721 31702720998785319308829541)
              ·
                refine ⟨5944260187272247370405539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31702720998785319308829541 5944260187272247370405539)
                ·
                  refine ⟨8916390280908371055608309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5944260187272247370405539 8916390280908371055608309)
                  ·
                    refine ⟨835911588835159786463279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8916390280908371055608309 835911588835159786463279)
                    ·
                      rfl

theorem cell23_4883796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_4883796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883796 prefixEnd_4883796 := by exact prefixLift 4883796
  have htrace : WordTrace (prefixWord ++ tailWord_4883796) baseStart_4883796 baseEnd_4883796 := by
    simpa [prefixWord, tailWord_4883796, baseEnd_4883796] using wordTrace_append hprefix tailTrace_4883796
  have hstable : (prefixWord ++ tailWord_4883796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883796).length < 2 ^ (prefixWord ++ tailWord_4883796).sum := by decide
  have hdescent : baseEnd_4883796 < baseStart_4883796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883826 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 4, 4]
def baseStart_4883826 : Nat := 118140960795 + 4883826 * 2 ^ 59
def prefixEnd_4883826 : Nat := 4983230072969 + 3 ^ 40 * 4883826 * 2
def baseEnd_4883826 : Nat := 835916723641704747338233

theorem tailTrace_4883826 : CollatzResearch.WordTrace tailWord_4883826 prefixEnd_4883826 835916723641704747338233 := by
  unfold tailWord_4883826
  simp only [CollatzResearch.WordTrace]
  refine ⟨44531942001184991980131833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118751845336493311947018221 44531942001184991980131833)
  ·
    refine ⟨33398956500888743985098875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44531942001184991980131833 33398956500888743985098875)
    ·
      refine ⟨50098434751333115977648313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33398956500888743985098875 50098434751333115977648313)
      ·
        refine ⟨37573826063499836983236235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50098434751333115977648313 37573826063499836983236235)
        ·
          refine ⟨56360739095249755474854353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37573826063499836983236235 56360739095249755474854353)
          ·
            refine ⟨42270554321437316606140765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56360739095249755474854353 42270554321437316606140765)
            ·
              refine ⟨15851457870538993727302787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42270554321437316606140765 15851457870538993727302787)
              ·
                refine ⟨23777186805808490590954181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15851457870538993727302787 23777186805808490590954181)
                ·
                  refine ⟨4458222526089091985803909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23777186805808490590954181 4458222526089091985803909)
                  ·
                    refine ⟨835916723641704747338233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4458222526089091985803909 835916723641704747338233)
                    ·
                      rfl

theorem cell23_4883826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_4883826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883826 prefixEnd_4883826 := by exact prefixLift 4883826
  have htrace : WordTrace (prefixWord ++ tailWord_4883826) baseStart_4883826 baseEnd_4883826 := by
    simpa [prefixWord, tailWord_4883826, baseEnd_4883826] using wordTrace_append hprefix tailTrace_4883826
  have hstable : (prefixWord ++ tailWord_4883826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883826).length < 2 ^ (prefixWord ++ tailWord_4883826).sum := by decide
  have hdescent : baseEnd_4883826 < baseStart_4883826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883833 : List Nat := [1, 2, 1, 3, 2, 1, 3, 3, 3, 2, 2]
def baseStart_4883833 : Nat := 118140960795 + 4883833 * 2 ^ 59
def prefixEnd_4883833 : Nat := 4983230072969 + 3 ^ 40 * 4883833 * 2
def baseEnd_4883833 : Nat := 2507753765289695714627167

theorem tailTrace_4883833 : CollatzResearch.WordTrace tailWord_4883833 prefixEnd_4883833 2507753765289695714627167 := by
  unfold tailWord_4883833
  simp only [CollatzResearch.WordTrace]
  refine ⟨178128023315714608116032153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118752015543809738744021435 178128023315714608116032153)
  ·
    refine ⟨133596017486785956087024115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178128023315714608116032153 133596017486785956087024115)
    ·
      refine ⟨200394026230178934130536173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133596017486785956087024115 200394026230178934130536173)
      ·
        refine ⟨75147759836317100298951065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200394026230178934130536173 75147759836317100298951065)
        ·
          refine ⟨56360819877237825224213299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75147759836317100298951065 56360819877237825224213299)
          ·
            refine ⟨84541229815856737836319949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56360819877237825224213299 84541229815856737836319949)
            ·
              refine ⟨31702961180946276688619981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84541229815856737836319949 31702961180946276688619981)
              ·
                refine ⟨11888610442854853758232493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31702961180946276688619981 11888610442854853758232493)
                ·
                  refine ⟨4458228916070570159337185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11888610442854853758232493 4458228916070570159337185)
                  ·
                    refine ⟨3343671687052927619502889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4458228916070570159337185 3343671687052927619502889)
                    ·
                      refine ⟨2507753765289695714627167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3343671687052927619502889 2507753765289695714627167)
                      ·
                        rfl

theorem cell23_4883833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 2, 2].length) (baseStart_4883833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883833 prefixEnd_4883833 := by exact prefixLift 4883833
  have htrace : WordTrace (prefixWord ++ tailWord_4883833) baseStart_4883833 baseEnd_4883833 := by
    simpa [prefixWord, tailWord_4883833, baseEnd_4883833] using wordTrace_append hprefix tailTrace_4883833
  have hstable : (prefixWord ++ tailWord_4883833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883833).length < 2 ^ (prefixWord ++ tailWord_4883833).sum := by decide
  have hdescent : baseEnd_4883833 < baseStart_4883833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883866 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3]
def baseStart_4883866 : Nat := 118140960795 + 4883866 * 2 ^ 59
def prefixEnd_4883866 : Nat := 4983230072969 + 3 ^ 40 * 4883866 * 2
def baseEnd_4883866 : Nat := 2507770710151294085514515

theorem tailTrace_4883866 : CollatzResearch.WordTrace tailWord_4883866 prefixEnd_4883866 2507770710151294085514515 := by
  unfold tailWord_4883866
  simp only [CollatzResearch.WordTrace]
  refine ⟨44532306731148763687995863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118752817949730036501322301 44532306731148763687995863)
  ·
    refine ⟨66798460096723145531993795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44532306731148763687995863 66798460096723145531993795)
    ·
      refine ⟨100197690145084718297990693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66798460096723145531993795 100197690145084718297990693)
      ·
        refine ⟨18787066902203384680873255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100197690145084718297990693 18787066902203384680873255)
        ·
          refine ⟨28180600353305077021309883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18787066902203384680873255 28180600353305077021309883)
          ·
            refine ⟨42270900529957615531964825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28180600353305077021309883 42270900529957615531964825)
            ·
              refine ⟨31703175397468211648973619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42270900529957615531964825 31703175397468211648973619)
              ·
                refine ⟨47554763096202317473460429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31703175397468211648973619 47554763096202317473460429)
                ·
                  refine ⟨17833036161075869052547661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47554763096202317473460429 17833036161075869052547661)
                  ·
                    refine ⟨6687388560403450894705373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17833036161075869052547661 6687388560403450894705373)
                    ·
                      refine ⟨2507770710151294085514515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6687388560403450894705373 2507770710151294085514515)
                      ·
                        rfl

theorem cell23_4883866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_4883866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883866 prefixEnd_4883866 := by exact prefixLift 4883866
  have htrace : WordTrace (prefixWord ++ tailWord_4883866) baseStart_4883866 baseEnd_4883866 := by
    simpa [prefixWord, tailWord_4883866, baseEnd_4883866] using wordTrace_append hprefix tailTrace_4883866
  have hstable : (prefixWord ++ tailWord_4883866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883866).length < 2 ^ (prefixWord ++ tailWord_4883866).sum := by decide
  have hdescent : baseEnd_4883866 < baseStart_4883866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883870 : List Nat := [4, 3, 1, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_4883870 : Nat := 118140960795 + 4883870 * 2 ^ 59
def prefixEnd_4883870 : Nat := 4983230072969 + 3 ^ 40 * 4883870 * 2
def baseEnd_4883870 : Nat := 2507772764073912069864497

theorem tailTrace_4883870 : CollatzResearch.WordTrace tailWord_4883870 prefixEnd_4883870 2507772764073912069864497 := by
  unfold tailWord_4883870
  simp only [CollatzResearch.WordTrace]
  refine ⟨22266171602072570429391133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118752915211053708956752709 22266171602072570429391133)
  ·
    refine ⟨8349814350777213911021675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22266171602072570429391133 8349814350777213911021675)
    ·
      refine ⟨12524721526165820866532513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8349814350777213911021675 12524721526165820866532513)
      ·
        refine ⟨9393541144624365649899385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12524721526165820866532513 9393541144624365649899385)
        ·
          refine ⟨7045155858468274237424539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9393541144624365649899385 7045155858468274237424539)
          ·
            refine ⟨10567733787702411356136809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7045155858468274237424539 10567733787702411356136809)
            ·
              refine ⟨7925800340776808517102607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10567733787702411356136809 7925800340776808517102607)
              ·
                refine ⟨11888700511165212775653911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7925800340776808517102607 11888700511165212775653911)
                ·
                  refine ⟨17833050766747819163480867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11888700511165212775653911 17833050766747819163480867)
                  ·
                    refine ⟨26749576150121728745221301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17833050766747819163480867 26749576150121728745221301)
                    ·
                      refine ⟨2507772764073912069864497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26749576150121728745221301 2507772764073912069864497)
                      ·
                        rfl

theorem cell23_4883870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_4883870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883870 prefixEnd_4883870 := by exact prefixLift 4883870
  have htrace : WordTrace (prefixWord ++ tailWord_4883870) baseStart_4883870 baseEnd_4883870 := by
    simpa [prefixWord, tailWord_4883870, baseEnd_4883870] using wordTrace_append hprefix tailTrace_4883870
  have hstable : (prefixWord ++ tailWord_4883870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883870).length < 2 ^ (prefixWord ++ tailWord_4883870).sum := by decide
  have hdescent : baseEnd_4883870 < baseStart_4883870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883957 : List Nat := [1, 3, 5, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_4883957 : Nat := 118140960795 + 4883957 * 2 ^ 59
def prefixEnd_4883957 : Nat := 4983230072969 + 3 ^ 40 * 4883957 * 2
def baseEnd_4883957 : Nat := 2507817436890853229476597

theorem tailTrace_4883957 : CollatzResearch.WordTrace tailWord_4883957 prefixEnd_4883957 2507817436890853229476597 := by
  unfold tailWord_4883957
  simp only [CollatzResearch.WordTrace]
  refine ⟨178132545967265377293546125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118755030644843584862364083 178132545967265377293546125)
  ·
    refine ⟨66799704737724516485079797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178132545967265377293546125 66799704737724516485079797)
    ·
      refine ⟨6262472319161673420476231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66799704737724516485079797 6262472319161673420476231)
      ·
        refine ⟨9393708478742510130714347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6262472319161673420476231 9393708478742510130714347)
        ·
          refine ⟨14090562718113765196071521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9393708478742510130714347 14090562718113765196071521)
          ·
            refine ⟨10567922038585323897053641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14090562718113765196071521 10567922038585323897053641)
            ·
              refine ⟨7925941528938992922790231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10567922038585323897053641 7925941528938992922790231)
              ·
                refine ⟨11888912293408489384185347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7925941528938992922790231 11888912293408489384185347)
                ·
                  refine ⟨17833368440112734076278021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11888912293408489384185347 17833368440112734076278021)
                  ·
                    refine ⟨3343756582521137639302129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17833368440112734076278021 3343756582521137639302129)
                    ·
                      refine ⟨2507817436890853229476597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3343756582521137639302129 2507817436890853229476597)
                      ·
                        rfl

theorem cell23_4883957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_4883957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883957 prefixEnd_4883957 := by exact prefixLift 4883957
  have htrace : WordTrace (prefixWord ++ tailWord_4883957) baseStart_4883957 baseEnd_4883957 := by
    simpa [prefixWord, tailWord_4883957, baseEnd_4883957] using wordTrace_append hprefix tailTrace_4883957
  have hstable : (prefixWord ++ tailWord_4883957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883957).length < 2 ^ (prefixWord ++ tailWord_4883957).sum := by decide
  have hdescent : baseEnd_4883957 < baseStart_4883957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4883980 : List Nat := [2, 2, 1, 2, 5, 1, 2, 3, 5]
def baseStart_4883980 : Nat := 118140960795 + 4883980 * 2 ^ 59
def prefixEnd_4883980 : Nat := 4983230072969 + 3 ^ 40 * 4883980 * 2
def baseEnd_4883980 : Nat := 278647694105100737720999

theorem tailTrace_4883980 : CollatzResearch.WordTrace tailWord_4883980 prefixEnd_4883980 278647694105100737720999 := by
  unfold tailWord_4883980
  simp only [CollatzResearch.WordTrace]
  refine ⟨89066692423091026110816697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118755589897454701481088929 89066692423091026110816697)
  ·
    refine ⟨66800019317318269583112523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89066692423091026110816697 66800019317318269583112523)
    ·
      refine ⟨100200028975977404374668785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66800019317318269583112523 100200028975977404374668785)
      ·
        refine ⟨75150021731983053281001589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100200028975977404374668785 75150021731983053281001589)
        ·
          refine ⟨7045314537373411245093899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75150021731983053281001589 7045314537373411245093899)
          ·
            refine ⟨10567971806060116867640849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7045314537373411245093899 10567971806060116867640849)
            ·
              refine ⟨7925978854545087650730637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10567971806060116867640849 7925978854545087650730637)
              ·
                refine ⟨2972242070454407869023989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7925978854545087650730637 2972242070454407869023989)
                ·
                  refine ⟨278647694105100737720999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2972242070454407869023989 278647694105100737720999)
                  ·
                    rfl

theorem cell23_4883980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 5].length) (baseStart_4883980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4883980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4883980 prefixEnd_4883980 := by exact prefixLift 4883980
  have htrace : WordTrace (prefixWord ++ tailWord_4883980) baseStart_4883980 baseEnd_4883980 := by
    simpa [prefixWord, tailWord_4883980, baseEnd_4883980] using wordTrace_append hprefix tailTrace_4883980
  have hstable : (prefixWord ++ tailWord_4883980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4883980).length < 2 ^ (prefixWord ++ tailWord_4883980).sum := by decide
  have hdescent : baseEnd_4883980 < baseStart_4883980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4883980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884023 : List Nat := [1, 1, 3, 1, 2, 4, 2, 2, 3, 4]
def baseStart_4884023 : Nat := 118140960795 + 4884023 * 2 ^ 59
def prefixEnd_4884023 : Nat := 4983230072969 + 3 ^ 40 * 4884023 * 2
def baseEnd_4884023 : Nat := 835950442204683323750431

theorem tailTrace_4884023 : CollatzResearch.WordTrace tailWord_4884023 prefixEnd_4884023 835950442204683323750431 := by
  unfold tailWord_4884023
  simp only [CollatzResearch.WordTrace]
  refine ⟨178134953185026270565448723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118756635456684180376965815 178134953185026270565448723)
  ·
    refine ⟨267202429777539405848173085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178134953185026270565448723 267202429777539405848173085)
    ·
      refine ⟨100200911166577277193064907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267202429777539405848173085 100200911166577277193064907)
      ·
        refine ⟨150301366749865915789597361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100200911166577277193064907 150301366749865915789597361)
        ·
          refine ⟨112726025062399436842198021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150301366749865915789597361 112726025062399436842198021)
          ·
            refine ⟨21136129699199894407912129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112726025062399436842198021 21136129699199894407912129)
            ·
              refine ⟨15852097274399920805934097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21136129699199894407912129 15852097274399920805934097)
              ·
                refine ⟨11889072955799940604450573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15852097274399920805934097 11889072955799940604450573)
                ·
                  refine ⟨4458402358424977726668965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11889072955799940604450573 4458402358424977726668965)
                  ·
                    refine ⟨835950442204683323750431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4458402358424977726668965 835950442204683323750431)
                    ·
                      rfl

theorem cell23_4884023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 4].length) (baseStart_4884023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884023 prefixEnd_4884023 := by exact prefixLift 4884023
  have htrace : WordTrace (prefixWord ++ tailWord_4884023) baseStart_4884023 baseEnd_4884023 := by
    simpa [prefixWord, tailWord_4884023, baseEnd_4884023] using wordTrace_append hprefix tailTrace_4884023
  have hstable : (prefixWord ++ tailWord_4884023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884023).length < 2 ^ (prefixWord ++ tailWord_4884023).sum := by decide
  have hdescent : baseEnd_4884023 < baseStart_4884023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884026 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4]
def baseStart_4884026 : Nat := 118140960795 + 4884026 * 2 ^ 59
def prefixEnd_4884026 : Nat := 4983230072969 + 3 ^ 40 * 4884026 * 2
def baseEnd_4884026 : Nat := 2507852867056013459513779

theorem tailTrace_4884026 : CollatzResearch.WordTrace tailWord_4884026 prefixEnd_4884026 2507852867056013459513779 := by
  unfold tailWord_4884026
  simp only [CollatzResearch.WordTrace]
  refine ⟨44533765651003850519451983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118756708402676934718538621 44533765651003850519451983)
  ·
    refine ⟨66800648476505775779177975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44533765651003850519451983 66800648476505775779177975)
    ·
      refine ⟨100200972714758663668766963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66800648476505775779177975 100200972714758663668766963)
      ·
        refine ⟨150301459072137995503150445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100200972714758663668766963 150301459072137995503150445)
        ·
          refine ⟨56363047152051748313681417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150301459072137995503150445 56363047152051748313681417)
          ·
            refine ⟨42272285364038811235261063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56363047152051748313681417 42272285364038811235261063)
            ·
              refine ⟨63408428046058216852891595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42272285364038811235261063 63408428046058216852891595)
              ·
                refine ⟨95112642069087325279337393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63408428046058216852891595 95112642069087325279337393)
                ·
                  refine ⟨71334481551815493959503045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95112642069087325279337393 71334481551815493959503045)
                  ·
                    refine ⟨13375215290965405117406821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71334481551815493959503045 13375215290965405117406821)
                    ·
                      refine ⟨2507852867056013459513779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13375215290965405117406821 2507852867056013459513779)
                      ·
                        rfl

theorem cell23_4884026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_4884026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884026 prefixEnd_4884026 := by exact prefixLift 4884026
  have htrace : WordTrace (prefixWord ++ tailWord_4884026) baseStart_4884026 baseEnd_4884026 := by
    simpa [prefixWord, tailWord_4884026, baseEnd_4884026] using wordTrace_append hprefix tailTrace_4884026
  have hstable : (prefixWord ++ tailWord_4884026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884026).length < 2 ^ (prefixWord ++ tailWord_4884026).sum := by decide
  have hdescent : baseEnd_4884026 < baseStart_4884026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884033 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_4884033 : Nat := 118140960795 + 4884033 * 2 ^ 59
def prefixEnd_4884033 : Nat := 4983230072969 + 3 ^ 40 * 4884033 * 2
def baseEnd_4884033 : Nat := 2507856461420594932126247

theorem tailTrace_4884033 : CollatzResearch.WordTrace tailWord_4884033 prefixEnd_4884033 2507856461420594932126247 := by
  unfold tailWord_4884033
  simp only [CollatzResearch.WordTrace]
  refine ⟨178135317914990042273312753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118756878609993361515541835 178135317914990042273312753)
  ·
    refine ⟨133601488436242531704984565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178135317914990042273312753 133601488436242531704984565)
    ·
      refine ⟨12525139540897737347342303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133601488436242531704984565 12525139540897737347342303)
      ·
        refine ⟨18787709311346606021013455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12525139540897737347342303 18787709311346606021013455)
        ·
          refine ⟨28181563967019909031520183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18787709311346606021013455 28181563967019909031520183)
          ·
            refine ⟨42272345950529863547280275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28181563967019909031520183 42272345950529863547280275)
            ·
              refine ⟨63408518925794795320920413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42272345950529863547280275 63408518925794795320920413)
              ·
                refine ⟨23778194597173048245345155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63408518925794795320920413 23778194597173048245345155)
                ·
                  refine ⟨35667291895759572368017733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23778194597173048245345155 35667291895759572368017733)
                  ·
                    refine ⟨6687617230454919819003325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35667291895759572368017733 6687617230454919819003325)
                    ·
                      refine ⟨2507856461420594932126247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6687617230454919819003325 2507856461420594932126247)
                      ·
                        rfl

theorem cell23_4884033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_4884033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884033 prefixEnd_4884033 := by exact prefixLift 4884033
  have htrace : WordTrace (prefixWord ++ tailWord_4884033) baseStart_4884033 baseEnd_4884033 := by
    simpa [prefixWord, tailWord_4884033, baseEnd_4884033] using wordTrace_append hprefix tailTrace_4884033
  have hstable : (prefixWord ++ tailWord_4884033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884033).length < 2 ^ (prefixWord ++ tailWord_4884033).sum := by decide
  have hdescent : baseEnd_4884033 < baseStart_4884033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884050 : List Nat := [3, 2, 2, 1, 2, 3, 1, 2, 2, 2, 3]
def baseStart_4884050 : Nat := 118140960795 + 4884050 * 2 ^ 59
def prefixEnd_4884050 : Nat := 4983230072969 + 3 ^ 40 * 4884050 * 2
def baseEnd_4884050 : Nat := 2507865190591721365613669

theorem tailTrace_4884050 : CollatzResearch.WordTrace tailWord_4884050 prefixEnd_4884050 2507865190591721365613669 := by
  unfold tailWord_4884050
  simp only [CollatzResearch.WordTrace]
  refine ⟨44533984488982113544170401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118757291970618969451121069 44533984488982113544170401)
  ·
    refine ⟨33400488366736585158127801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44533984488982113544170401 33400488366736585158127801)
    ·
      refine ⟨25050366275052438868595851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33400488366736585158127801 25050366275052438868595851)
      ·
        refine ⟨37575549412578658302893777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25050366275052438868595851 37575549412578658302893777)
        ·
          refine ⟨28181662059433993727170333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37575549412578658302893777 28181662059433993727170333)
          ·
            refine ⟨10568123272287747647688875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28181662059433993727170333 10568123272287747647688875)
            ·
              refine ⟨15852184908431621471533313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10568123272287747647688875 15852184908431621471533313)
              ·
                refine ⟨11889138681323716103649985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15852184908431621471533313 11889138681323716103649985)
                ·
                  refine ⟨8916854010992787077737489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11889138681323716103649985 8916854010992787077737489)
                  ·
                    refine ⟨6687640508244590308303117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8916854010992787077737489 6687640508244590308303117)
                    ·
                      refine ⟨2507865190591721365613669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6687640508244590308303117 2507865190591721365613669)
                      ·
                        rfl

theorem cell23_4884050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_4884050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884050 prefixEnd_4884050 := by exact prefixLift 4884050
  have htrace : WordTrace (prefixWord ++ tailWord_4884050) baseStart_4884050 baseEnd_4884050 := by
    simpa [prefixWord, tailWord_4884050, baseEnd_4884050] using wordTrace_append hprefix tailTrace_4884050
  have hstable : (prefixWord ++ tailWord_4884050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884050).length < 2 ^ (prefixWord ++ tailWord_4884050).sum := by decide
  have hdescent : baseEnd_4884050 < baseStart_4884050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884073 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 3, 5, 2]
def baseStart_4884073 : Nat := 118140960795 + 4884073 * 2 ^ 59
def prefixEnd_4884073 : Nat := 4983230072969 + 3 ^ 40 * 4884073 * 2
def baseEnd_4884073 : Nat := 2507877000646774775626063

theorem tailTrace_4884073 : CollatzResearch.WordTrace tailWord_4884073 prefixEnd_4884073 2507877000646774775626063 := by
  unfold tailWord_4884073
  simp only [CollatzResearch.WordTrace]
  refine ⟨178136776834845129104768873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118757851223230086069845915 178136776834845129104768873)
  ·
    refine ⟨133602582626133846828576655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178136776834845129104768873 133602582626133846828576655)
    ·
      refine ⟨200403873939200770242864983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133602582626133846828576655 200403873939200770242864983)
      ·
        refine ⟨300605810908801155364297475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200403873939200770242864983 300605810908801155364297475)
        ·
          refine ⟨450908716363201733046446213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300605810908801155364297475 450908716363201733046446213)
          ·
            refine ⟨84545384318100324946208665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 450908716363201733046446213 84545384318100324946208665)
            ·
              refine ⟨63409038238575243709656499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84545384318100324946208665 63409038238575243709656499)
              ·
                refine ⟨95113557357862865564484749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63409038238575243709656499 95113557357862865564484749)
                ·
                  refine ⟨35667584009198574586681781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95113557357862865564484749 35667584009198574586681781)
                  ·
                    refine ⟨3343836000862366367501417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35667584009198574586681781 3343836000862366367501417)
                    ·
                      refine ⟨2507877000646774775626063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3343836000862366367501417 2507877000646774775626063)
                      ·
                        rfl

theorem cell23_4884073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 5, 2].length) (baseStart_4884073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884073 prefixEnd_4884073 := by exact prefixLift 4884073
  have htrace : WordTrace (prefixWord ++ tailWord_4884073) baseStart_4884073 baseEnd_4884073 := by
    simpa [prefixWord, tailWord_4884073, baseEnd_4884073] using wordTrace_append hprefix tailTrace_4884073
  have hstable : (prefixWord ++ tailWord_4884073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884073).length < 2 ^ (prefixWord ++ tailWord_4884073).sum := by decide
  have hdescent : baseEnd_4884073 < baseStart_4884073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884133 : List Nat := [1, 3, 1, 2, 1, 2, 3, 3, 1, 2, 4]
def baseStart_4884133 : Nat := 118140960795 + 4884133 * 2 ^ 59
def prefixEnd_4884133 : Nat := 4983230072969 + 3 ^ 40 * 4884133 * 2
def baseEnd_4884133 : Nat := 2507907809486044540875787

theorem tailTrace_4884133 : CollatzResearch.WordTrace tailWord_4884133 prefixEnd_4884133 2507907809486044540875787 := by
  unfold tailWord_4884133
  simp only [CollatzResearch.WordTrace]
  refine ⟨178138965214627759351953053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118759310143085172901302035 178138965214627759351953053)
  ·
    refine ⟨66802111955485409756982395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178138965214627759351953053 66802111955485409756982395)
    ·
      refine ⟨100203167933228114635473593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66802111955485409756982395 100203167933228114635473593)
      ·
        refine ⟨75152375949921085976605195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100203167933228114635473593 75152375949921085976605195)
        ·
          refine ⟨112728563924881628964907793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75152375949921085976605195 112728563924881628964907793)
          ·
            refine ⟨84546422943661221723680845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112728563924881628964907793 84546422943661221723680845)
            ·
              refine ⟨31704908603872958146380317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84546422943661221723680845 31704908603872958146380317)
              ·
                refine ⟨11889340726452359304892619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31704908603872958146380317 11889340726452359304892619)
                ·
                  refine ⟨17834011089678538957338929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11889340726452359304892619 17834011089678538957338929)
                  ·
                    refine ⟨13375508317258904218004197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17834011089678538957338929 13375508317258904218004197)
                    ·
                      refine ⟨2507907809486044540875787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13375508317258904218004197 2507907809486044540875787)
                      ·
                        rfl

theorem cell23_4884133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_4884133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884133 prefixEnd_4884133 := by exact prefixLift 4884133
  have htrace : WordTrace (prefixWord ++ tailWord_4884133) baseStart_4884133 baseEnd_4884133 := by
    simpa [prefixWord, tailWord_4884133, baseEnd_4884133] using wordTrace_append hprefix tailTrace_4884133
  have hstable : (prefixWord ++ tailWord_4884133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884133).length < 2 ^ (prefixWord ++ tailWord_4884133).sum := by decide
  have hdescent : baseEnd_4884133 < baseStart_4884133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884143 : List Nat := [1, 1, 2, 1, 2, 4, 5, 7]
def baseStart_4884143 : Nat := 118140960795 + 4884143 * 2 ^ 59
def prefixEnd_4884143 : Nat := 4983230072969 + 3 ^ 40 * 4884143 * 2
def baseEnd_4884143 : Nat := 92885664603429240805583

theorem tailTrace_4884143 : CollatzResearch.WordTrace tailWord_4884143 prefixEnd_4884143 92885664603429240805583 := by
  unfold tailWord_4884143
  simp only [CollatzResearch.WordTrace]
  refine ⟨178139329944591531059817083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118759553296394354039878055 178139329944591531059817083)
  ·
    refine ⟨267208994916887296589725625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178139329944591531059817083 267208994916887296589725625)
    ·
      refine ⟨200406746187665472442294219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267208994916887296589725625 200406746187665472442294219)
      ·
        refine ⟨300610119281498208663441329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200406746187665472442294219 300610119281498208663441329)
        ·
          refine ⟨225457589461123656497580997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300610119281498208663441329 225457589461123656497580997)
          ·
            refine ⟨42273298023960685593296437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 225457589461123656497580997 42273298023960685593296437)
            ·
              refine ⟨3963121689746314274371541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42273298023960685593296437 3963121689746314274371541)
              ·
                refine ⟨92885664603429240805583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3963121689746314274371541 92885664603429240805583)
                ·
                  rfl

theorem cell23_4884143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 7].length) (baseStart_4884143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884143 prefixEnd_4884143 := by exact prefixLift 4884143
  have htrace : WordTrace (prefixWord ++ tailWord_4884143) baseStart_4884143 baseEnd_4884143 := by
    simpa [prefixWord, tailWord_4884143, baseEnd_4884143] using wordTrace_append hprefix tailTrace_4884143
  have hstable : (prefixWord ++ tailWord_4884143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884143).length < 2 ^ (prefixWord ++ tailWord_4884143).sum := by decide
  have hdescent : baseEnd_4884143 < baseStart_4884143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884154 : List Nat := [3, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2]
def baseStart_4884154 : Nat := 118140960795 + 4884154 * 2 ^ 59
def prefixEnd_4884154 : Nat := 4983230072969 + 3 ^ 40 * 4884154 * 2
def baseEnd_4884154 : Nat := 2507918592579788958713191

theorem tailTrace_4884154 : CollatzResearch.WordTrace tailWord_4884154 prefixEnd_4884154 2507918592579788958713191 := by
  unfold tailWord_4884154
  simp only [CollatzResearch.WordTrace]
  refine ⟨44534932786887919984616879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118759820765034453292311677 44534932786887919984616879)
  ·
    refine ⟨66802399180331879976925319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44534932786887919984616879 66802399180331879976925319)
    ·
      refine ⟨100203598770497819965387979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66802399180331879976925319 100203598770497819965387979)
      ·
        refine ⟨150305398155746729948081969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100203598770497819965387979 150305398155746729948081969)
        ·
          refine ⟨112729048616810047461061477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150305398155746729948081969 112729048616810047461061477)
          ·
            refine ⟨21136696615651883898949027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112729048616810047461061477 21136696615651883898949027)
            ·
              refine ⟨31705044923477825848423541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21136696615651883898949027 31705044923477825848423541)
              ·
                refine ⟨2972347961576046173289707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31705044923477825848423541 2972347961576046173289707)
                ·
                  refine ⟨4458521942364069259934561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2972347961576046173289707 4458521942364069259934561)
                  ·
                    refine ⟨3343891456773051944950921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4458521942364069259934561 3343891456773051944950921)
                    ·
                      refine ⟨2507918592579788958713191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3343891456773051944950921 2507918592579788958713191)
                      ·
                        rfl

theorem cell23_4884154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2].length) (baseStart_4884154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884154 prefixEnd_4884154 := by exact prefixLift 4884154
  have htrace : WordTrace (prefixWord ++ tailWord_4884154) baseStart_4884154 baseEnd_4884154 := by
    simpa [prefixWord, tailWord_4884154, baseEnd_4884154] using wordTrace_append hprefix tailTrace_4884154
  have hstable : (prefixWord ++ tailWord_4884154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884154).length < 2 ^ (prefixWord ++ tailWord_4884154).sum := by decide
  have hdescent : baseEnd_4884154 < baseStart_4884154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884214 : List Nat := [5, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2]
def baseStart_4884214 : Nat := 118140960795 + 4884214 * 2 ^ 59
def prefixEnd_4884214 : Nat := 4983230072969 + 3 ^ 40 * 4884214 * 2
def baseEnd_4884214 : Nat := 2507949401419058723962915

theorem tailTrace_4884214 : CollatzResearch.WordTrace tailWord_4884214 prefixEnd_4884214 2507949401419058723962915 := by
  unfold tailWord_4884214
  simp only [CollatzResearch.WordTrace]
  refine ⟨11133869970458394386603231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118761279684889540123767797 11133869970458394386603231)
  ·
    refine ⟨16700804955687591579904847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11133869970458394386603231 16700804955687591579904847)
    ·
      refine ⟨25051207433531387369857271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16700804955687591579904847 25051207433531387369857271)
      ·
        refine ⟨37576811150297081054785907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25051207433531387369857271 37576811150297081054785907)
        ·
          refine ⟨56365216725445621582178861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37576811150297081054785907 56365216725445621582178861)
          ·
            refine ⟨21136956272042108093317073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56365216725445621582178861 21136956272042108093317073)
            ·
              refine ⟨15852717204031581069987805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21136956272042108093317073 15852717204031581069987805)
              ·
                refine ⟨5944768951511842901245427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15852717204031581069987805 5944768951511842901245427)
                ·
                  refine ⟨8917153427267764351868141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5944768951511842901245427 8917153427267764351868141)
                  ·
                    refine ⟨3343932535225411631950553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8917153427267764351868141 3343932535225411631950553)
                    ·
                      refine ⟨2507949401419058723962915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3343932535225411631950553 2507949401419058723962915)
                      ·
                        rfl

theorem cell23_4884214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_4884214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884214 prefixEnd_4884214 := by exact prefixLift 4884214
  have htrace : WordTrace (prefixWord ++ tailWord_4884214) baseStart_4884214 baseEnd_4884214 := by
    simpa [prefixWord, tailWord_4884214, baseEnd_4884214] using wordTrace_append hprefix tailTrace_4884214
  have hstable : (prefixWord ++ tailWord_4884214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884214).length < 2 ^ (prefixWord ++ tailWord_4884214).sum := by decide
  have hdescent : baseEnd_4884214 < baseStart_4884214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884223 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 4]
def baseStart_4884223 : Nat := 118140960795 + 4884223 * 2 ^ 59
def prefixEnd_4884223 : Nat := 4983230072969 + 3 ^ 40 * 4884223 * 2
def baseEnd_4884223 : Nat := 2507954022744949188750373

theorem tailTrace_4884223 : CollatzResearch.WordTrace tailWord_4884223 prefixEnd_4884223 2507954022744949188750373 := by
  unfold tailWord_4884223
  simp only [CollatzResearch.WordTrace]
  refine ⟨178142247784301704722729323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118761498522867803148486215 178142247784301704722729323)
  ·
    refine ⟨267213371676452557084093985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178142247784301704722729323 267213371676452557084093985)
    ·
      refine ⟨200410028757339417813070489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267213371676452557084093985 200410028757339417813070489)
      ·
        refine ⟨150307521568004563359802867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200410028757339417813070489 150307521568004563359802867)
        ·
          refine ⟨225461282352006845039704301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150307521568004563359802867 225461282352006845039704301)
          ·
            refine ⟨84547980882002566889889113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225461282352006845039704301 84547980882002566889889113)
            ·
              refine ⟨63410985661501925167416835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84547980882002566889889113 63410985661501925167416835)
              ·
                refine ⟨95116478492252887751125253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63410985661501925167416835 95116478492252887751125253)
                ·
                  refine ⟨17834339717297416453335985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95116478492252887751125253 17834339717297416453335985)
                  ·
                    refine ⟨13375754787973062340001989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17834339717297416453335985 13375754787973062340001989)
                    ·
                      refine ⟨2507954022744949188750373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13375754787973062340001989 2507954022744949188750373)
                      ·
                        rfl

theorem cell23_4884223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_4884223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884223 prefixEnd_4884223 := by exact prefixLift 4884223
  have htrace : WordTrace (prefixWord ++ tailWord_4884223) baseStart_4884223 baseEnd_4884223 := by
    simpa [prefixWord, tailWord_4884223, baseEnd_4884223] using wordTrace_append hprefix tailTrace_4884223
  have hstable : (prefixWord ++ tailWord_4884223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884223).length < 2 ^ (prefixWord ++ tailWord_4884223).sum := by decide
  have hdescent : baseEnd_4884223 < baseStart_4884223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884227 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 4, 2, 2]
def baseStart_4884227 : Nat := 118140960795 + 4884227 * 2 ^ 59
def prefixEnd_4884227 : Nat := 4983230072969 + 3 ^ 40 * 4884227 * 2
def baseEnd_4884227 : Nat := 2507956076667567173100355

theorem tailTrace_4884227 : CollatzResearch.WordTrace tailWord_4884227 prefixEnd_4884227 2507956076667567173100355 := by
  unfold tailWord_4884227
  simp only [CollatzResearch.WordTrace]
  refine ⟨178142393676287213405874935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118761595784191475603916623 178142393676287213405874935)
  ·
    refine ⟨267213590514430820108812403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178142393676287213405874935 267213590514430820108812403)
    ·
      refine ⟨400820385771646230163218605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267213590514430820108812403 400820385771646230163218605)
      ·
        refine ⟨150307644664367336311206977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 400820385771646230163218605 150307644664367336311206977)
        ·
          refine ⟨112730733498275502233405233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150307644664367336311206977 112730733498275502233405233)
          ·
            refine ⟨84548050123706626675053925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112730733498275502233405233 84548050123706626675053925)
            ·
              refine ⟨15852759398194992501572611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84548050123706626675053925 15852759398194992501572611)
              ·
                refine ⟨23779139097292488752358917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15852759398194992501572611 23779139097292488752358917)
                ·
                  refine ⟨4458588580742341641067297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23779139097292488752358917 4458588580742341641067297)
                  ·
                    refine ⟨3343941435556756230800473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4458588580742341641067297 3343941435556756230800473)
                    ·
                      refine ⟨2507956076667567173100355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3343941435556756230800473 2507956076667567173100355)
                      ·
                        rfl

theorem cell23_4884227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 2, 2].length) (baseStart_4884227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884227 prefixEnd_4884227 := by exact prefixLift 4884227
  have htrace : WordTrace (prefixWord ++ tailWord_4884227) baseStart_4884227 baseEnd_4884227 := by
    simpa [prefixWord, tailWord_4884227, baseEnd_4884227] using wordTrace_append hprefix tailTrace_4884227
  have hstable : (prefixWord ++ tailWord_4884227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884227).length < 2 ^ (prefixWord ++ tailWord_4884227).sum := by decide
  have hdescent : baseEnd_4884227 < baseStart_4884227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884278 : List Nat := [5, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2]
def baseStart_4884278 : Nat := 118140960795 + 4884278 * 2 ^ 59
def prefixEnd_4884278 : Nat := 4983230072969 + 3 ^ 40 * 4884278 * 2
def baseEnd_4884278 : Nat := 2507982264180946473562621

theorem tailTrace_4884278 : CollatzResearch.WordTrace tailWord_4884278 prefixEnd_4884278 2507982264180946473562621 := by
  unfold tailWord_4884278
  simp only [CollatzResearch.WordTrace]
  refine ⟨11134015862443903069748843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118762835866068299410654325 11134015862443903069748843)
  ·
    refine ⟨16701023793665854604623265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11134015862443903069748843 16701023793665854604623265)
    ·
      refine ⟨12525767845249390953467449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16701023793665854604623265 12525767845249390953467449)
      ·
        refine ⟨9394325883937043215100587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12525767845249390953467449 9394325883937043215100587)
        ·
          refine ⟨14091488825905564822650881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9394325883937043215100587 14091488825905564822650881)
          ·
            refine ⟨10568616619429173616988161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14091488825905564822650881 10568616619429173616988161)
            ·
              refine ⟨7926462464571880212741121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10568616619429173616988161 7926462464571880212741121)
              ·
                refine ⟨5944846848428910159555841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7926462464571880212741121 5944846848428910159555841)
                ·
                  refine ⟨4458635136321682619666881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5944846848428910159555841 4458635136321682619666881)
                  ·
                    refine ⟨3343976352241261964750161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4458635136321682619666881 3343976352241261964750161)
                    ·
                      refine ⟨2507982264180946473562621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3343976352241261964750161 2507982264180946473562621)
                      ·
                        rfl

theorem cell23_4884278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_4884278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884278 prefixEnd_4884278 := by exact prefixLift 4884278
  have htrace : WordTrace (prefixWord ++ tailWord_4884278) baseStart_4884278 baseEnd_4884278 := by
    simpa [prefixWord, tailWord_4884278, baseEnd_4884278] using wordTrace_append hprefix tailTrace_4884278
  have hstable : (prefixWord ++ tailWord_4884278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884278).length < 2 ^ (prefixWord ++ tailWord_4884278).sum := by decide
  have hdescent : baseEnd_4884278 < baseStart_4884278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884280 : List Nat := [2, 1, 2, 1, 3, 3, 2, 2, 2, 5]
def baseStart_4884280 : Nat := 118140960795 + 4884280 * 2 ^ 59
def prefixEnd_4884280 : Nat := 4983230072969 + 3 ^ 40 * 4884280 * 2
def baseEnd_4884280 : Nat := 835994430380751821912537

theorem tailTrace_4884280 : CollatzResearch.WordTrace tailWord_4884280 prefixEnd_4884280 835994430380751821912537 := by
  unfold tailWord_4884280
  simp only [CollatzResearch.WordTrace]
  refine ⟨89072163372547601728777147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118762884496730135638369529 89072163372547601728777147)
  ·
    refine ⟨133608245058821402593165721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89072163372547601728777147 133608245058821402593165721)
    ·
      refine ⟨100206183794116051944874291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133608245058821402593165721 100206183794116051944874291)
      ·
        refine ⟨150309275691174077917311437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100206183794116051944874291 150309275691174077917311437)
        ·
          refine ⟨56365978384190279218991789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150309275691174077917311437 56365978384190279218991789)
          ·
            refine ⟨21137241894071354707121921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56365978384190279218991789 21137241894071354707121921)
            ·
              refine ⟨15852931420553516030341441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21137241894071354707121921 15852931420553516030341441)
              ·
                refine ⟨11889698565415137022756081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15852931420553516030341441 11889698565415137022756081)
                ·
                  refine ⟨8917273924061352767067061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11889698565415137022756081 8917273924061352767067061)
                  ·
                    refine ⟨835994430380751821912537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8917273924061352767067061 835994430380751821912537)
                    ·
                      rfl

theorem cell23_4884280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_4884280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884280 prefixEnd_4884280 := by exact prefixLift 4884280
  have htrace : WordTrace (prefixWord ++ tailWord_4884280) baseStart_4884280 baseEnd_4884280 := by
    simpa [prefixWord, tailWord_4884280, baseEnd_4884280] using wordTrace_append hprefix tailTrace_4884280
  have hstable : (prefixWord ++ tailWord_4884280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884280).length < 2 ^ (prefixWord ++ tailWord_4884280).sum := by decide
  have hdescent : baseEnd_4884280 < baseStart_4884280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884294 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_4884294 : Nat := 118140960795 + 4884294 * 2 ^ 59
def prefixEnd_4884294 : Nat := 4983230072969 + 3 ^ 40 * 4884294 * 2
def baseEnd_4884294 : Nat := 2507990479871418410962547

theorem tailTrace_4884294 : CollatzResearch.WordTrace tailWord_4884294 prefixEnd_4884294 2507990479871418410962547 := by
  unfold tailWord_4884294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5567026167720140120267623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 118763224911362989232375957 5567026167720140120267623)
  ·
    refine ⟨8350539251580210180401435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5567026167720140120267623 8350539251580210180401435)
    ·
      refine ⟨12525808877370315270602153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8350539251580210180401435 12525808877370315270602153)
      ·
        refine ⟨9394356658027736452951615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12525808877370315270602153 9394356658027736452951615)
        ·
          refine ⟨14091534987041604679427423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9394356658027736452951615 14091534987041604679427423)
          ·
            refine ⟨21137302480562407019141135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14091534987041604679427423 21137302480562407019141135)
            ·
              refine ⟨31705953720843610528711703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21137302480562407019141135 31705953720843610528711703)
              ·
                refine ⟨47558930581265415793067555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31705953720843610528711703 47558930581265415793067555)
                ·
                  refine ⟨71338395871898123689601333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47558930581265415793067555 71338395871898123689601333)
                  ·
                    refine ⟨6687974612990449095900125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71338395871898123689601333 6687974612990449095900125)
                    ·
                      refine ⟨2507990479871418410962547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6687974612990449095900125 2507990479871418410962547)
                      ·
                        rfl

theorem cell23_4884294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_4884294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884294 prefixEnd_4884294 := by exact prefixLift 4884294
  have htrace : WordTrace (prefixWord ++ tailWord_4884294) baseStart_4884294 baseEnd_4884294 := by
    simpa [prefixWord, tailWord_4884294, baseEnd_4884294] using wordTrace_append hprefix tailTrace_4884294
  have hstable : (prefixWord ++ tailWord_4884294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884294).length < 2 ^ (prefixWord ++ tailWord_4884294).sum := by decide
  have hdescent : baseEnd_4884294 < baseStart_4884294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884334 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 2, 4, 2]
def baseStart_4884334 : Nat := 118140960795 + 4884334 * 2 ^ 59
def prefixEnd_4884334 : Nat := 4983230072969 + 3 ^ 40 * 4884334 * 2
def baseEnd_4884334 : Nat := 2508011019097598254462363

theorem tailTrace_4884334 : CollatzResearch.WordTrace tailWord_4884334 prefixEnd_4884334 2508011019097598254462363 := by
  unfold tailWord_4884334
  simp only [CollatzResearch.WordTrace]
  refine ⟨22268287035862446335002507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118764197524599713786680037 22268287035862446335002507)
  ·
    refine ⟨33402430553793669502503761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22268287035862446335002507 33402430553793669502503761)
    ·
      refine ⟨25051822915345252126877821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33402430553793669502503761 25051822915345252126877821)
      ·
        refine ⟨9394433593254469547579183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25051822915345252126877821 9394433593254469547579183)
        ·
          refine ⟨14091650389881704321368775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9394433593254469547579183 14091650389881704321368775)
          ·
            refine ⟨21137475584822556482053163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14091650389881704321368775 21137475584822556482053163)
            ·
              refine ⟨31706213377233834723079745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21137475584822556482053163 31706213377233834723079745)
              ·
                refine ⟨23779660032925376042309809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31706213377233834723079745 23779660032925376042309809)
                ·
                  refine ⟨17834745024694032031732357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23779660032925376042309809 17834745024694032031732357)
                  ·
                    refine ⟨3344014692130131005949817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17834745024694032031732357 3344014692130131005949817)
                    ·
                      refine ⟨2508011019097598254462363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3344014692130131005949817 2508011019097598254462363)
                      ·
                        rfl

theorem cell23_4884334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_4884334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884334 prefixEnd_4884334 := by exact prefixLift 4884334
  have htrace : WordTrace (prefixWord ++ tailWord_4884334) baseStart_4884334 baseEnd_4884334 := by
    simpa [prefixWord, tailWord_4884334, baseEnd_4884334] using wordTrace_append hprefix tailTrace_4884334
  have hstable : (prefixWord ++ tailWord_4884334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884334).length < 2 ^ (prefixWord ++ tailWord_4884334).sum := by decide
  have hdescent : baseEnd_4884334 < baseStart_4884334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884357 : List Nat := [1, 3, 1, 1, 3, 2, 5, 1, 6]
def baseStart_4884357 : Nat := 118140960795 + 4884357 * 2 ^ 59
def prefixEnd_4884357 : Nat := 4983230072969 + 3 ^ 40 * 4884357 * 2
def baseEnd_4884357 : Nat := 278669203239183518274973

theorem tailTrace_4884357 : CollatzResearch.WordTrace tailWord_4884357 prefixEnd_4884357 278669203239183518274973 := by
  unfold tailWord_4884357
  simp only [CollatzResearch.WordTrace]
  refine ⟨178147135165816245608107325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118764756777210830405404883 178147135165816245608107325)
  ·
    refine ⟨66805175687181092103040247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178147135165816245608107325 66805175687181092103040247)
    ·
      refine ⟨100207763530771638154560371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66805175687181092103040247 100207763530771638154560371)
      ·
        refine ⟨150311645296157457231840557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100207763530771638154560371 150311645296157457231840557)
        ·
          refine ⟨56366866986059046461940209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150311645296157457231840557 56366866986059046461940209)
          ·
            refine ⟨42275150239544284846455157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56366866986059046461940209 42275150239544284846455157)
            ·
              refine ⟨3963295334957276704355171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42275150239544284846455157 3963295334957276704355171)
              ·
                refine ⟨5944943002435915056532757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3963295334957276704355171 5944943002435915056532757)
                ·
                  refine ⟨278669203239183518274973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5944943002435915056532757 278669203239183518274973)
                  ·
                    rfl

theorem cell23_4884357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 6].length) (baseStart_4884357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884357 prefixEnd_4884357 := by exact prefixLift 4884357
  have htrace : WordTrace (prefixWord ++ tailWord_4884357) baseStart_4884357 baseEnd_4884357 := by
    simpa [prefixWord, tailWord_4884357, baseEnd_4884357] using wordTrace_append hprefix tailTrace_4884357
  have hstable : (prefixWord ++ tailWord_4884357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884357).length < 2 ^ (prefixWord ++ tailWord_4884357).sum := by decide
  have hdescent : baseEnd_4884357 < baseStart_4884357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884377 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 1, 5, 2]
def baseStart_4884377 : Nat := 118140960795 + 4884377 * 2 ^ 59
def prefixEnd_4884377 : Nat := 4983230072969 + 3 ^ 40 * 4884377 * 2
def baseEnd_4884377 : Nat := 2508033098765741586224665

theorem tailTrace_4884377 : CollatzResearch.WordTrace tailWord_4884377 prefixEnd_4884377 2508033098765741586224665 := by
  unfold tailWord_4884377
  simp only [CollatzResearch.WordTrace]
  refine ⟨178147864625743789023835385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118765243083829192682556923 178147864625743789023835385)
  ·
    refine ⟨133610898469307841767876539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178147864625743789023835385 133610898469307841767876539)
    ·
      refine ⟨200416347703961762651814809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133610898469307841767876539 200416347703961762651814809)
      ·
        refine ⟨150312260777971321988861107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200416347703961762651814809 150312260777971321988861107)
        ·
          refine ⟨225468391166956982983291661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150312260777971321988861107 225468391166956982983291661)
          ·
            refine ⟨84550646687608868618734373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225468391166956982983291661 84550646687608868618734373)
            ·
              refine ⟨15853246253926662866012695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84550646687608868618734373 15853246253926662866012695)
              ·
                refine ⟨23779869380889994299019043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15853246253926662866012695 23779869380889994299019043)
                ·
                  refine ⟨35669804071334991448528565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23779869380889994299019043 35669804071334991448528565)
                  ·
                    refine ⟨3344044131687655448299553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35669804071334991448528565 3344044131687655448299553)
                    ·
                      refine ⟨2508033098765741586224665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3344044131687655448299553 2508033098765741586224665)
                      ·
                        rfl

theorem cell23_4884377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 5, 2].length) (baseStart_4884377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884377 prefixEnd_4884377 := by exact prefixLift 4884377
  have htrace : WordTrace (prefixWord ++ tailWord_4884377) baseStart_4884377 baseEnd_4884377 := by
    simpa [prefixWord, tailWord_4884377, baseEnd_4884377] using wordTrace_append hprefix tailTrace_4884377
  have hstable : (prefixWord ++ tailWord_4884377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884377).length < 2 ^ (prefixWord ++ tailWord_4884377).sum := by decide
  have hdescent : baseEnd_4884377 < baseStart_4884377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884401 : List Nat := [1, 2, 2, 4, 2, 3, 1, 1, 3, 1, 3]
def baseStart_4884401 : Nat := 118140960795 + 4884401 * 2 ^ 59
def prefixEnd_4884401 : Nat := 4983230072969 + 3 ^ 40 * 4884401 * 2
def baseEnd_4884401 : Nat := 2508045422301449492324555

theorem tailTrace_4884401 : CollatzResearch.WordTrace tailWord_4884401 prefixEnd_4884401 2508045422301449492324555 := by
  unfold tailWord_4884401
  simp only [CollatzResearch.WordTrace]
  refine ⟨178148739977656841122709057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118765826651771227415139371 178148739977656841122709057)
  ·
    refine ⟨133611554983242630842031793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178148739977656841122709057 133611554983242630842031793)
    ·
      refine ⟨100208666237431973131523845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133611554983242630842031793 100208666237431973131523845)
      ·
        refine ⟨18789124919518494962160721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100208666237431973131523845 18789124919518494962160721)
        ·
          refine ⟨14091843689638871221620541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18789124919518494962160721 14091843689638871221620541)
          ·
            refine ⟨5284441383614576708107703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14091843689638871221620541 5284441383614576708107703)
            ·
              refine ⟨7926662075421865062161555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5284441383614576708107703 7926662075421865062161555)
              ·
                refine ⟨11889993113132797593242333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7926662075421865062161555 11889993113132797593242333)
                ·
                  refine ⟨4458747417424799097465875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11889993113132797593242333 4458747417424799097465875)
                  ·
                    refine ⟨6688121126137198646198813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4458747417424799097465875 6688121126137198646198813)
                    ·
                      refine ⟨2508045422301449492324555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6688121126137198646198813 2508045422301449492324555)
                      ·
                        rfl

theorem cell23_4884401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_4884401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884401 prefixEnd_4884401 := by exact prefixLift 4884401
  have htrace : WordTrace (prefixWord ++ tailWord_4884401) baseStart_4884401 baseEnd_4884401 := by
    simpa [prefixWord, tailWord_4884401, baseEnd_4884401] using wordTrace_append hprefix tailTrace_4884401
  have hstable : (prefixWord ++ tailWord_4884401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884401).length < 2 ^ (prefixWord ++ tailWord_4884401).sum := by decide
  have hdescent : baseEnd_4884401 < baseStart_4884401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884410 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5]
def baseStart_4884410 : Nat := 118140960795 + 4884410 * 2 ^ 59
def prefixEnd_4884410 : Nat := 4983230072969 + 3 ^ 40 * 4884410 * 2
def baseEnd_4884410 : Nat := 2508050043627339957112013

theorem tailTrace_4884410 : CollatzResearch.WordTrace tailWord_4884410 prefixEnd_4884410 2508050043627339957112013 := by
  unfold tailWord_4884410
  simp only [CollatzResearch.WordTrace]
  refine ⟨44537267058656058914946671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118766045489749490439857789 44537267058656058914946671)
  ·
    refine ⟨66805900587984088372420007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44537267058656058914946671 66805900587984088372420007)
    ·
      refine ⟨100208850881976132558630011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66805900587984088372420007 100208850881976132558630011)
      ·
        refine ⟨150313276322964198837945017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100208850881976132558630011 150313276322964198837945017)
        ·
          refine ⟨112734957242223149128458763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150313276322964198837945017 112734957242223149128458763)
          ·
            refine ⟨169102435863334723692688145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112734957242223149128458763 169102435863334723692688145)
            ·
              refine ⟨126826826897501042769516109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169102435863334723692688145 126826826897501042769516109)
              ·
                refine ⟨47560060086562891038568541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126826826897501042769516109 47560060086562891038568541)
                ·
                  refine ⟨17835022532461084139463203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47560060086562891038568541 17835022532461084139463203)
                  ·
                    refine ⟨26752533798691626209194805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17835022532461084139463203 26752533798691626209194805)
                    ·
                      refine ⟨2508050043627339957112013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26752533798691626209194805 2508050043627339957112013)
                      ·
                        rfl

theorem cell23_4884410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_4884410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884410 prefixEnd_4884410 := by exact prefixLift 4884410
  have htrace : WordTrace (prefixWord ++ tailWord_4884410) baseStart_4884410 baseEnd_4884410 := by
    simpa [prefixWord, tailWord_4884410, baseEnd_4884410] using wordTrace_append hprefix tailTrace_4884410
  have hstable : (prefixWord ++ tailWord_4884410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884410).length < 2 ^ (prefixWord ++ tailWord_4884410).sum := by decide
  have hdescent : baseEnd_4884410 < baseStart_4884410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884424 : List Nat := [2, 1, 3, 1, 4, 1, 3, 2, 1, 1, 4]
def baseStart_4884424 : Nat := 118140960795 + 4884424 * 2 ^ 59
def prefixEnd_4884424 : Nat := 4983230072969 + 3 ^ 40 * 4884424 * 2
def baseEnd_4884424 : Nat := 2508057232356502902336949

theorem tailTrace_4884424 : CollatzResearch.WordTrace tailWord_4884424 prefixEnd_4884424 2508057232356502902336949 := by
  unfold tailWord_4884424
  simp only [CollatzResearch.WordTrace]
  refine ⟨89074789428286758025398163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118766385904382344033864217 89074789428286758025398163)
  ·
    refine ⟨133612184142430137038097245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89074789428286758025398163 133612184142430137038097245)
    ·
      refine ⟨50104569053411301389286467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133612184142430137038097245 50104569053411301389286467)
      ·
        refine ⟨75156853580116952083929701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50104569053411301389286467 75156853580116952083929701)
        ·
          refine ⟨14091910046271928515736819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75156853580116952083929701 14091910046271928515736819)
          ·
            refine ⟨21137865069407892773605229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14091910046271928515736819 21137865069407892773605229)
            ·
              refine ⟨7926699401027959790101961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21137865069407892773605229 7926699401027959790101961)
              ·
                refine ⟨5945024550770969842576471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7926699401027959790101961 5945024550770969842576471)
                ·
                  refine ⟨8917536826156454763864707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5945024550770969842576471 8917536826156454763864707)
                  ·
                    refine ⟨13376305239234682145797061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8917536826156454763864707 13376305239234682145797061)
                    ·
                      refine ⟨2508057232356502902336949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13376305239234682145797061 2508057232356502902336949)
                      ·
                        rfl

theorem cell23_4884424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_4884424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884424 prefixEnd_4884424 := by exact prefixLift 4884424
  have htrace : WordTrace (prefixWord ++ tailWord_4884424) baseStart_4884424 baseEnd_4884424 := by
    simpa [prefixWord, tailWord_4884424, baseEnd_4884424] using wordTrace_append hprefix tailTrace_4884424
  have hstable : (prefixWord ++ tailWord_4884424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884424).length < 2 ^ (prefixWord ++ tailWord_4884424).sum := by decide
  have hdescent : baseEnd_4884424 < baseStart_4884424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884427 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 3]
def baseStart_4884427 : Nat := 118140960795 + 4884427 * 2 ^ 59
def prefixEnd_4884427 : Nat := 4983230072969 + 3 ^ 40 * 4884427 * 2
def baseEnd_4884427 : Nat := 2508058772798466390599435

theorem tailTrace_4884427 : CollatzResearch.WordTrace tailWord_4884427 prefixEnd_4884427 2508058772798466390599435 := by
  unfold tailWord_4884427
  simp only [CollatzResearch.WordTrace]
  refine ⟨178149688275562647563155535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118766458850375098375437023 178149688275562647563155535)
  ·
    refine ⟨267224532413343971344733303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178149688275562647563155535 267224532413343971344733303)
    ·
      refine ⟨400836798620015957017099955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267224532413343971344733303 400836798620015957017099955)
      ·
        refine ⟨601255197930023935525649933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400836798620015957017099955 601255197930023935525649933)
        ·
          refine ⟨225470699223758975822118725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 601255197930023935525649933 225470699223758975822118725)
          ·
            refine ⟨42275756104454807966647261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 225470699223758975822118725 42275756104454807966647261)
            ·
              refine ⟨15853408539170552987492723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42275756104454807966647261 15853408539170552987492723)
              ·
                refine ⟨23780112808755829481239085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15853408539170552987492723 23780112808755829481239085)
                ·
                  refine ⟨8917542303283436055464657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23780112808755829481239085 8917542303283436055464657)
                  ·
                    refine ⟨6688156727462577041598493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8917542303283436055464657 6688156727462577041598493)
                    ·
                      refine ⟨2508058772798466390599435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6688156727462577041598493 2508058772798466390599435)
                      ·
                        rfl

theorem cell23_4884427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 3].length) (baseStart_4884427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884427 prefixEnd_4884427 := by exact prefixLift 4884427
  have htrace : WordTrace (prefixWord ++ tailWord_4884427) baseStart_4884427 baseEnd_4884427 := by
    simpa [prefixWord, tailWord_4884427, baseEnd_4884427] using wordTrace_append hprefix tailTrace_4884427
  have hstable : (prefixWord ++ tailWord_4884427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884427).length < 2 ^ (prefixWord ++ tailWord_4884427).sum := by decide
  have hdescent : baseEnd_4884427 < baseStart_4884427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884430 : List Nat := [4, 1, 1, 1, 2, 2, 1, 11]
def baseStart_4884430 : Nat := 118140960795 + 4884430 * 2 ^ 59
def prefixEnd_4884430 : Nat := 4983230072969 + 3 ^ 40 * 4884430 * 2
def baseEnd_4884430 : Nat := 92891122712608514031923

theorem tailTrace_4884430 : CollatzResearch.WordTrace tailWord_4884430 prefixEnd_4884430 92891122712608514031923 := by
  unfold tailWord_4884430
  simp only [CollatzResearch.WordTrace]
  refine ⟨22268724711818972384439343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118766531796367852717009829 22268724711818972384439343)
  ·
    refine ⟨33403087067728458576659015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22268724711818972384439343 33403087067728458576659015)
    ·
      refine ⟨50104630601592687864988523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33403087067728458576659015 50104630601592687864988523)
      ·
        refine ⟨75156945902389031797482785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50104630601592687864988523 75156945902389031797482785)
        ·
          refine ⟨56367709426791773848112089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75156945902389031797482785 56367709426791773848112089)
          ·
            refine ⟨42275782070093830386084067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56367709426791773848112089 42275782070093830386084067)
            ·
              refine ⟨63413673105140745579126101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42275782070093830386084067 63413673105140745579126101)
              ·
                refine ⟨92891122712608514031923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 63413673105140745579126101 92891122712608514031923)
                ·
                  rfl

theorem cell23_4884430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 11].length) (baseStart_4884430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884430 prefixEnd_4884430 := by exact prefixLift 4884430
  have htrace : WordTrace (prefixWord ++ tailWord_4884430) baseStart_4884430 baseEnd_4884430 := by
    simpa [prefixWord, tailWord_4884430, baseEnd_4884430] using wordTrace_append hprefix tailTrace_4884430
  have hstable : (prefixWord ++ tailWord_4884430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884430).length < 2 ^ (prefixWord ++ tailWord_4884430).sum := by decide
  have hdescent : baseEnd_4884430 < baseStart_4884430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884434 : List Nat := [3, 2, 2, 3, 2, 1, 1, 2, 1, 6]
def baseStart_4884434 : Nat := 118140960795 + 4884434 * 2 ^ 59
def prefixEnd_4884434 : Nat := 4983230072969 + 3 ^ 40 * 4884434 * 2
def baseEnd_4884434 : Nat := 836020789054349287737301

theorem tailTrace_4884434 : CollatzResearch.WordTrace tailWord_4884434 prefixEnd_4884434 836020789054349287737301 := by
  unfold tailWord_4884434
  simp only [CollatzResearch.WordTrace]
  refine ⟨44537485896634321939665089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118766629057691525172440237 44537485896634321939665089)
  ·
    refine ⟨33403114422475741454748817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44537485896634321939665089 33403114422475741454748817)
    ·
      refine ⟨25052335816856806091061613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33403114422475741454748817 25052335816856806091061613)
      ·
        refine ⟨9394625931321302284148105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25052335816856806091061613 9394625931321302284148105)
        ·
          refine ⟨7045969448490976713111079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9394625931321302284148105 7045969448490976713111079)
          ·
            refine ⟨10568954172736465069666619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7045969448490976713111079 10568954172736465069666619)
            ·
              refine ⟨15853431259104697604499929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10568954172736465069666619 15853431259104697604499929)
              ·
                refine ⟨11890073444328523203374947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15853431259104697604499929 11890073444328523203374947)
                ·
                  refine ⟨17835110166492784805062421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11890073444328523203374947 17835110166492784805062421)
                  ·
                    refine ⟨836020789054349287737301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17835110166492784805062421 836020789054349287737301)
                    ·
                      rfl

theorem cell23_4884434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_4884434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884434 prefixEnd_4884434 := by exact prefixLift 4884434
  have htrace : WordTrace (prefixWord ++ tailWord_4884434) baseStart_4884434 baseEnd_4884434 := by
    simpa [prefixWord, tailWord_4884434, baseEnd_4884434] using wordTrace_append hprefix tailTrace_4884434
  have hstable : (prefixWord ++ tailWord_4884434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884434).length < 2 ^ (prefixWord ++ tailWord_4884434).sum := by decide
  have hdescent : baseEnd_4884434 < baseStart_4884434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884437 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 3, 2, 4]
def baseStart_4884437 : Nat := 118140960795 + 4884437 * 2 ^ 59
def prefixEnd_4884437 : Nat := 4983230072969 + 3 ^ 40 * 4884437 * 2
def baseEnd_4884437 : Nat := 2508063907605011351474389

theorem tailTrace_4884437 : CollatzResearch.WordTrace tailWord_4884437 prefixEnd_4884437 2508063907605011351474389 := by
  unfold tailWord_4884437
  simp only [CollatzResearch.WordTrace]
  refine ⟨178150053005526419271019565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118766702003684279514013043 178150053005526419271019565)
  ·
    refine ⟨66806269877072407226632337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178150053005526419271019565 66806269877072407226632337)
    ·
      refine ⟨50104702407804305419974253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66806269877072407226632337 50104702407804305419974253)
      ·
        refine ⟨18789263402926614532490345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50104702407804305419974253 18789263402926614532490345)
        ·
          refine ⟨14091947552194960899367759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18789263402926614532490345 14091947552194960899367759)
          ·
            refine ⟨21137921328292441349051639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14091947552194960899367759 21137921328292441349051639)
            ·
              refine ⟨31706881992438662023577459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21137921328292441349051639 31706881992438662023577459)
              ·
                refine ⟨47560322988657993035366189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31706881992438662023577459 47560322988657993035366189)
                ·
                  refine ⟨17835121120746747388262321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47560322988657993035366189 17835121120746747388262321)
                  ·
                    refine ⟨13376340840560060541196741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17835121120746747388262321 13376340840560060541196741)
                    ·
                      refine ⟨2508063907605011351474389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13376340840560060541196741 2508063907605011351474389)
                      ·
                        rfl

theorem cell23_4884437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_4884437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884437 prefixEnd_4884437 := by exact prefixLift 4884437
  have htrace : WordTrace (prefixWord ++ tailWord_4884437) baseStart_4884437 baseEnd_4884437 := by
    simpa [prefixWord, tailWord_4884437, baseEnd_4884437] using wordTrace_append hprefix tailTrace_4884437
  have hstable : (prefixWord ++ tailWord_4884437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884437).length < 2 ^ (prefixWord ++ tailWord_4884437).sum := by decide
  have hdescent : baseEnd_4884437 < baseStart_4884437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884438 : List Nat := [5, 2, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_4884438 : Nat := 118140960795 + 4884438 * 2 ^ 59
def prefixEnd_4884438 : Nat := 4983230072969 + 3 ^ 40 * 4884438 * 2
def baseEnd_4884438 : Nat := 836021473695221949187295

theorem tailTrace_4884438 : CollatzResearch.WordTrace tailWord_4884438 prefixEnd_4884438 836021473695221949187295 := by
  unfold tailWord_4884438
  simp only [CollatzResearch.WordTrace]
  refine ⟨11134380592407674777612873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118766726319015197627870645 11134380592407674777612873)
  ·
    refine ⟨8350785444305756083209655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11134380592407674777612873 8350785444305756083209655)
    ·
      refine ⟨12526178166458634124814483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8350785444305756083209655 12526178166458634124814483)
      ·
        refine ⟨18789267249687951187221725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12526178166458634124814483 18789267249687951187221725)
        ·
          refine ⟨7045975218632981695208147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18789267249687951187221725 7045975218632981695208147)
          ·
            refine ⟨10568962827949472542812221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7045975218632981695208147 10568962827949472542812221)
            ·
              refine ⟨3963361060481052203554583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10568962827949472542812221 3963361060481052203554583)
              ·
                refine ⟨5945041590721578305331875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3963361060481052203554583 5945041590721578305331875)
                ·
                  refine ⟨8917562386082367457997813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5945041590721578305331875 8917562386082367457997813)
                  ·
                    refine ⟨836021473695221949187295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8917562386082367457997813 836021473695221949187295)
                    ·
                      rfl

theorem cell23_4884438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_4884438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884438 prefixEnd_4884438 := by exact prefixLift 4884438
  have htrace : WordTrace (prefixWord ++ tailWord_4884438) baseStart_4884438 baseEnd_4884438 := by
    simpa [prefixWord, tailWord_4884438, baseEnd_4884438] using wordTrace_append hprefix tailTrace_4884438
  have hstable : (prefixWord ++ tailWord_4884438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884438).length < 2 ^ (prefixWord ++ tailWord_4884438).sum := by decide
  have hdescent : baseEnd_4884438 < baseStart_4884438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884441 : List Nat := [1, 2, 1, 2, 6, 1, 3, 1, 1, 1, 4]
def baseStart_4884441 : Nat := 118140960795 + 4884441 * 2 ^ 59
def prefixEnd_4884441 : Nat := 4983230072969 + 3 ^ 40 * 4884441 * 2
def baseEnd_4884441 : Nat := 2508065961527629335824371

theorem tailTrace_4884441 : CollatzResearch.WordTrace tailWord_4884441 prefixEnd_4884441 2508065961527629335824371 := by
  unfold tailWord_4884441
  simp only [CollatzResearch.WordTrace]
  refine ⟨178150198897511927954165177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118766799265007951969443451 178150198897511927954165177)
  ·
    refine ⟨133612649173133945965623883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178150198897511927954165177 133612649173133945965623883)
    ·
      refine ⟨200418973759700918948435825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133612649173133945965623883 200418973759700918948435825)
      ·
        refine ⟨150314230319775689211326869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200418973759700918948435825 150314230319775689211326869)
        ·
          refine ⟨7045979546239485431780947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 150314230319775689211326869 7045979546239485431780947)
          ·
            refine ⟨10568969319359228147671421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7045979546239485431780947 10568969319359228147671421)
            ·
              refine ⟨3963363494759710555376783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10568969319359228147671421 3963363494759710555376783)
              ·
                refine ⟨5945045242139565833065175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3963363494759710555376783 5945045242139565833065175)
                ·
                  refine ⟨8917567863209348749597763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5945045242139565833065175 8917567863209348749597763)
                  ·
                    refine ⟨13376351794814023124396645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8917567863209348749597763 13376351794814023124396645)
                    ·
                      refine ⟨2508065961527629335824371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13376351794814023124396645 2508065961527629335824371)
                      ·
                        rfl

theorem cell23_4884441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 1, 1, 4].length) (baseStart_4884441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884441 prefixEnd_4884441 := by exact prefixLift 4884441
  have htrace : WordTrace (prefixWord ++ tailWord_4884441) baseStart_4884441 baseEnd_4884441 := by
    simpa [prefixWord, tailWord_4884441, baseEnd_4884441] using wordTrace_append hprefix tailTrace_4884441
  have hstable : (prefixWord ++ tailWord_4884441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884441).length < 2 ^ (prefixWord ++ tailWord_4884441).sum := by decide
  have hdescent : baseEnd_4884441 < baseStart_4884441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884458 : List Nat := [3, 1, 3, 1, 2, 1, 3, 4, 1, 2, 2]
def baseStart_4884458 : Nat := 118140960795 + 4884458 * 2 ^ 59
def prefixEnd_4884458 : Nat := 4983230072969 + 3 ^ 40 * 4884458 * 2
def baseEnd_4884458 : Nat := 2508074690698755769311793

theorem tailTrace_4884458 : CollatzResearch.WordTrace tailWord_4884458 prefixEnd_4884458 2508074690698755769311793 := by
  unfold tailWord_4884458
  simp only [CollatzResearch.WordTrace]
  refine ⟨44537704734612584964383507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118767212625633559905022685 44537704734612584964383507)
  ·
    refine ⟨66806557101918877446575261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44537704734612584964383507 66806557101918877446575261)
    ·
      refine ⟨25052458913219579042465723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66806557101918877446575261 25052458913219579042465723)
      ·
        refine ⟨37578688369829368563698585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25052458913219579042465723 37578688369829368563698585)
        ·
          refine ⟨28184016277372026422773939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37578688369829368563698585 28184016277372026422773939)
          ·
            refine ⟨42276024416058039634160909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28184016277372026422773939 42276024416058039634160909)
            ·
              refine ⟨15853509156021764862810341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42276024416058039634160909 15853509156021764862810341)
              ·
                refine ⟨2972532966754080911776939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15853509156021764862810341 2972532966754080911776939)
                ·
                  refine ⟨4458799450131121367665409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2972532966754080911776939 4458799450131121367665409)
                  ·
                    refine ⟨3344099587598341025749057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4458799450131121367665409 3344099587598341025749057)
                    ·
                      refine ⟨2508074690698755769311793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3344099587598341025749057 2508074690698755769311793)
                      ·
                        rfl

theorem cell23_4884458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_4884458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884458 prefixEnd_4884458 := by exact prefixLift 4884458
  have htrace : WordTrace (prefixWord ++ tailWord_4884458) baseStart_4884458 baseEnd_4884458 := by
    simpa [prefixWord, tailWord_4884458, baseEnd_4884458] using wordTrace_append hprefix tailTrace_4884458
  have hstable : (prefixWord ++ tailWord_4884458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884458).length < 2 ^ (prefixWord ++ tailWord_4884458).sum := by decide
  have hdescent : baseEnd_4884458 < baseStart_4884458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884508 : List Nat := [2, 2, 3, 1, 3, 3, 1, 2, 2, 1, 3]
def baseStart_4884508 : Nat := 118140960795 + 4884508 * 2 ^ 59
def prefixEnd_4884508 : Nat := 4983230072969 + 3 ^ 40 * 4884508 * 2
def baseEnd_4884508 : Nat := 2508100364731480573686563

theorem tailTrace_4884508 : CollatzResearch.WordTrace tailWord_4884508 prefixEnd_4884508 2508100364731480573686563 := by
  unfold tailWord_4884508
  simp only [CollatzResearch.WordTrace]
  refine ⟨89076321294134599198427089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118768428392179465597902785 89076321294134599198427089)
  ·
    refine ⟨66807240970600949398820317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89076321294134599198427089 66807240970600949398820317)
    ·
      refine ⟨25052715363975356024557619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66807240970600949398820317 25052715363975356024557619)
      ·
        refine ⟨37579073045963034036836429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25052715363975356024557619 37579073045963034036836429)
        ·
          refine ⟨14092152392236137763813661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37579073045963034036836429 14092152392236137763813661)
          ·
            refine ⟨5284557147088551661430123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14092152392236137763813661 5284557147088551661430123)
            ·
              refine ⟨7926835720632827492145185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5284557147088551661430123 7926835720632827492145185)
              ·
                refine ⟨5945126790474620619108889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7926835720632827492145185 5945126790474620619108889)
                ·
                  refine ⟨4458845092855965464331667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5945126790474620619108889 4458845092855965464331667)
                  ·
                    refine ⟨6688267639283948196497501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4458845092855965464331667 6688267639283948196497501)
                    ·
                      refine ⟨2508100364731480573686563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6688267639283948196497501 2508100364731480573686563)
                      ·
                        rfl

theorem cell23_4884508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_4884508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884508 prefixEnd_4884508 := by exact prefixLift 4884508
  have htrace : WordTrace (prefixWord ++ tailWord_4884508) baseStart_4884508 baseEnd_4884508 := by
    simpa [prefixWord, tailWord_4884508, baseEnd_4884508] using wordTrace_append hprefix tailTrace_4884508
  have hstable : (prefixWord ++ tailWord_4884508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884508).length < 2 ^ (prefixWord ++ tailWord_4884508).sum := by decide
  have hdescent : baseEnd_4884508 < baseStart_4884508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884531 : List Nat := [1, 1, 1, 2, 4, 1, 2, 5, 2, 2, 2]
def baseStart_4884531 : Nat := 118140960795 + 4884531 * 2 ^ 59
def prefixEnd_4884531 : Nat := 4983230072969 + 3 ^ 40 * 4884531 * 2
def baseEnd_4884531 : Nat := 2508112174786533983698957

theorem tailTrace_4884531 : CollatzResearch.WordTrace tailWord_4884531 prefixEnd_4884531 2508112174786533983698957 := by
  unfold tailWord_4884531
  simp only [CollatzResearch.WordTrace]
  refine ⟨178153481467185873324941447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118768987644790582216627631 178153481467185873324941447)
  ·
    refine ⟨267230222200778809987412171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178153481467185873324941447 267230222200778809987412171)
    ·
      refine ⟨400845333301168214981118257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267230222200778809987412171 400845333301168214981118257)
      ·
        refine ⟨300633999975876161235838693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400845333301168214981118257 300633999975876161235838693)
        ·
          refine ⟨56368874995476780231719755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 300633999975876161235838693 56368874995476780231719755)
          ·
            refine ⟨84553312493215170347579633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56368874995476780231719755 84553312493215170347579633)
            ·
              refine ⟨63414984369911377760684725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84553312493215170347579633 63414984369911377760684725)
              ·
                refine ⟨5945154784679191665064193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63414984369911377760684725 5945154784679191665064193)
                ·
                  refine ⟨4458866088509393748798145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5945154784679191665064193 4458866088509393748798145)
                  ·
                    refine ⟨3344149566382045311598609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4458866088509393748798145 3344149566382045311598609)
                    ·
                      refine ⟨2508112174786533983698957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3344149566382045311598609 2508112174786533983698957)
                      ·
                        rfl

theorem cell23_4884531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 2, 2].length) (baseStart_4884531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884531 prefixEnd_4884531 := by exact prefixLift 4884531
  have htrace : WordTrace (prefixWord ++ tailWord_4884531) baseStart_4884531 baseEnd_4884531 := by
    simpa [prefixWord, tailWord_4884531, baseEnd_4884531] using wordTrace_append hprefix tailTrace_4884531
  have hstable : (prefixWord ++ tailWord_4884531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884531).length < 2 ^ (prefixWord ++ tailWord_4884531).sum := by decide
  have hdescent : baseEnd_4884531 < baseStart_4884531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884534 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_4884534 : Nat := 118140960795 + 4884534 * 2 ^ 59
def prefixEnd_4884534 : Nat := 4983230072969 + 3 ^ 40 * 4884534 * 2
def baseEnd_4884534 : Nat := 2508113715228497471961443

theorem tailTrace_4884534 : CollatzResearch.WordTrace tailWord_4884534 prefixEnd_4884534 2508113715228497471961443 := by
  unfold tailWord_4884534
  simp only [CollatzResearch.WordTrace]
  refine ⟨11134599430385937802331291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118769060590783336558200437 11134599430385937802331291)
  ·
    refine ⟨16701899145578906703496937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11134599430385937802331291 16701899145578906703496937)
    ·
      refine ⟨12526424359184180027622703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16701899145578906703496937 12526424359184180027622703)
      ·
        refine ⟨18789636538776270041434055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12526424359184180027622703 18789636538776270041434055)
        ·
          refine ⟨28184454808164405062151083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18789636538776270041434055 28184454808164405062151083)
          ·
            refine ⟨42276682212246607593226625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28184454808164405062151083 42276682212246607593226625)
            ·
              refine ⟨31707511659184955694919969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42276682212246607593226625 31707511659184955694919969)
              ·
                refine ⟨23780633744388716771189977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31707511659184955694919969 23780633744388716771189977)
                ·
                  refine ⟨17835475308291537578392483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23780633744388716771189977 17835475308291537578392483)
                  ·
                    refine ⟨26753212962437306367588725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17835475308291537578392483 26753212962437306367588725)
                    ·
                      refine ⟨2508113715228497471961443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26753212962437306367588725 2508113715228497471961443)
                      ·
                        rfl

theorem cell23_4884534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_4884534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884534 prefixEnd_4884534 := by exact prefixLift 4884534
  have htrace : WordTrace (prefixWord ++ tailWord_4884534) baseStart_4884534 baseEnd_4884534 := by
    simpa [prefixWord, tailWord_4884534, baseEnd_4884534] using wordTrace_append hprefix tailTrace_4884534
  have hstable : (prefixWord ++ tailWord_4884534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884534).length < 2 ^ (prefixWord ++ tailWord_4884534).sum := by decide
  have hdescent : baseEnd_4884534 < baseStart_4884534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884547 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 3]
def baseStart_4884547 : Nat := 118140960795 + 4884547 * 2 ^ 59
def prefixEnd_4884547 : Nat := 4983230072969 + 3 ^ 40 * 4884547 * 2
def baseEnd_4884547 : Nat := 2508120390477005921098883

theorem tailTrace_4884547 : CollatzResearch.WordTrace tailWord_4884547 prefixEnd_4884547 2508120390477005921098883 := by
  unfold tailWord_4884547
  simp only [CollatzResearch.WordTrace]
  refine ⟨178154065035127908057523895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118769376690085272038349263 178154065035127908057523895)
  ·
    refine ⟨267231097552691862086285843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178154065035127908057523895 267231097552691862086285843)
    ·
      refine ⟨400846646329037793129428765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267231097552691862086285843 400846646329037793129428765)
      ·
        refine ⟨150317492373389172423535787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 400846646329037793129428765 150317492373389172423535787)
        ·
          refine ⟨225476238560083758635303681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150317492373389172423535787 225476238560083758635303681)
          ·
            refine ⟨169107178920062818976477761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225476238560083758635303681 169107178920062818976477761)
            ·
              refine ⟨126830384190047114232358321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169107178920062818976477761 126830384190047114232358321)
              ·
                refine ⟨95122788142535335674268741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126830384190047114232358321 95122788142535335674268741)
                ·
                  refine ⟨17835522776725375438925389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95122788142535335674268741 17835522776725375438925389)
                  ·
                    refine ⟨6688321041272015789597021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17835522776725375438925389 6688321041272015789597021)
                    ·
                      refine ⟨2508120390477005921098883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6688321041272015789597021 2508120390477005921098883)
                      ·
                        rfl

theorem cell23_4884547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 3].length) (baseStart_4884547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884547 prefixEnd_4884547 := by exact prefixLift 4884547
  have htrace : WordTrace (prefixWord ++ tailWord_4884547) baseStart_4884547 baseEnd_4884547 := by
    simpa [prefixWord, tailWord_4884547, baseEnd_4884547] using wordTrace_append hprefix tailTrace_4884547
  have hstable : (prefixWord ++ tailWord_4884547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884547).length < 2 ^ (prefixWord ++ tailWord_4884547).sum := by decide
  have hdescent : baseEnd_4884547 < baseStart_4884547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884567 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 4, 5]
def baseStart_4884567 : Nat := 118140960795 + 4884567 * 2 ^ 59
def prefixEnd_4884567 : Nat := 4983230072969 + 3 ^ 40 * 4884567 * 2
def baseEnd_4884567 : Nat := 836043553363365280949597

theorem tailTrace_4884567 : CollatzResearch.WordTrace tailWord_4884567 prefixEnd_4884567 836043553363365280949597 := by
  unfold tailWord_4884567
  simp only [CollatzResearch.WordTrace]
  refine ⟨178154794495055451473251955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118769862996703634315501303 178154794495055451473251955)
  ·
    refine ⟨267232191742583177209877933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178154794495055451473251955 267232191742583177209877933)
    ·
      refine ⟨100212071903468691453704225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267232191742583177209877933 100212071903468691453704225)
      ·
        refine ⟨75159053927601518590278169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100212071903468691453704225 75159053927601518590278169)
        ·
          refine ⟨56369290445701138942708627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75159053927601518590278169 56369290445701138942708627)
          ·
            refine ⟨84553935668551708414062941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56369290445701138942708627 84553935668551708414062941)
            ·
              refine ⟨31707725875706890655273603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84553935668551708414062941 31707725875706890655273603)
              ·
                refine ⟨47561588813560335982910405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31707725875706890655273603 47561588813560335982910405)
                ·
                  refine ⟨8917797902542562996795701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47561588813560335982910405 8917797902542562996795701)
                  ·
                    refine ⟨836043553363365280949597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8917797902542562996795701 836043553363365280949597)
                    ·
                      rfl

theorem cell23_4884567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_4884567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884567 prefixEnd_4884567 := by exact prefixLift 4884567
  have htrace : WordTrace (prefixWord ++ tailWord_4884567) baseStart_4884567 baseEnd_4884567 := by
    simpa [prefixWord, tailWord_4884567, baseEnd_4884567] using wordTrace_append hprefix tailTrace_4884567
  have hstable : (prefixWord ++ tailWord_4884567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884567).length < 2 ^ (prefixWord ++ tailWord_4884567).sum := by decide
  have hdescent : baseEnd_4884567 < baseStart_4884567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884604 : List Nat := [2, 2, 2, 1, 1, 4, 1, 3, 2, 1, 4]
def baseStart_4884604 : Nat := 118140960795 + 4884604 * 2 ^ 59
def prefixEnd_4884604 : Nat := 4983230072969 + 3 ^ 40 * 4884604 * 2
def baseEnd_4884604 : Nat := 2508149658874312198086121

theorem tailTrace_4884604 : CollatzResearch.WordTrace tailWord_4884604 prefixEnd_4884604 2508149658874312198086121 := by
  unfold tailWord_4884604
  simp only [CollatzResearch.WordTrace]
  refine ⟨89078071997960703396174433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118770762663947604528232577 89078071997960703396174433)
  ·
    refine ⟨66808553998470527547130825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89078071997960703396174433 66808553998470527547130825)
    ·
      refine ⟨50106415498852895660348119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66808553998470527547130825 50106415498852895660348119)
      ·
        refine ⟨75159623248279343490522179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50106415498852895660348119 75159623248279343490522179)
        ·
          refine ⟨112739434872419015235783269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75159623248279343490522179 112739434872419015235783269)
          ·
            refine ⟨21138644038578565356709363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112739434872419015235783269 21138644038578565356709363)
            ·
              refine ⟨31707966057867848035064045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21138644038578565356709363 31707966057867848035064045)
              ·
                refine ⟨11890487271700443013149017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31707966057867848035064045 11890487271700443013149017)
                ·
                  refine ⟨8917865453775332259861763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11890487271700443013149017 8917865453775332259861763)
                  ·
                    refine ⟨13376798180662998389792645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8917865453775332259861763 13376798180662998389792645)
                    ·
                      refine ⟨2508149658874312198086121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13376798180662998389792645 2508149658874312198086121)
                      ·
                        rfl

theorem cell23_4884604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_4884604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884604 prefixEnd_4884604 := by exact prefixLift 4884604
  have htrace : WordTrace (prefixWord ++ tailWord_4884604) baseStart_4884604 baseEnd_4884604 := by
    simpa [prefixWord, tailWord_4884604, baseEnd_4884604] using wordTrace_append hprefix tailTrace_4884604
  have hstable : (prefixWord ++ tailWord_4884604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884604).length < 2 ^ (prefixWord ++ tailWord_4884604).sum := by decide
  have hdescent : baseEnd_4884604 < baseStart_4884604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884617 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 2, 1, 6]
def baseStart_4884617 : Nat := 118140960795 + 4884617 * 2 ^ 59
def prefixEnd_4884617 : Nat := 4983230072969 + 3 ^ 40 * 4884617 * 2
def baseEnd_4884617 : Nat := 2508156334122820647223561

theorem tailTrace_4884617 : CollatzResearch.WordTrace tailWord_4884617 prefixEnd_4884617 2508156334122820647223561 := by
  unfold tailWord_4884617
  simp only [CollatzResearch.WordTrace]
  refine ⟨178156618144874310012572105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118771078763249540008381403 178156618144874310012572105)
  ·
    refine ⟨133617463608655732509429079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178156618144874310012572105 133617463608655732509429079)
    ·
      refine ⟨200426195412983598764143619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133617463608655732509429079 200426195412983598764143619)
      ·
        refine ⟨300639293119475398146215429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200426195412983598764143619 300639293119475398146215429)
        ·
          refine ⟨56369867459901637152415393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 300639293119475398146215429 56369867459901637152415393)
          ·
            refine ⟨42277400594926227864311545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56369867459901637152415393 42277400594926227864311545)
            ·
              refine ⟨31708050446194670898233659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42277400594926227864311545 31708050446194670898233659)
              ·
                refine ⟨47562075669292006347350489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31708050446194670898233659 47562075669292006347350489)
                ·
                  refine ⟨35671556751969004760512867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47562075669292006347350489 35671556751969004760512867)
                  ·
                    refine ⟨53507335127953507140769301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35671556751969004760512867 53507335127953507140769301)
                    ·
                      refine ⟨2508156334122820647223561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53507335127953507140769301 2508156334122820647223561)
                      ·
                        rfl

theorem cell23_4884617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_4884617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884617 prefixEnd_4884617 := by exact prefixLift 4884617
  have htrace : WordTrace (prefixWord ++ tailWord_4884617) baseStart_4884617 baseEnd_4884617 := by
    simpa [prefixWord, tailWord_4884617, baseEnd_4884617] using wordTrace_append hprefix tailTrace_4884617
  have hstable : (prefixWord ++ tailWord_4884617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884617).length < 2 ^ (prefixWord ++ tailWord_4884617).sum := by decide
  have hdescent : baseEnd_4884617 < baseStart_4884617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884624 : List Nat := [2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 3]
def baseStart_4884624 : Nat := 118140960795 + 4884624 * 2 ^ 59
def prefixEnd_4884624 : Nat := 4983230072969 + 3 ^ 40 * 4884624 * 2
def baseEnd_4884624 : Nat := 2508159928487402119836029

theorem tailTrace_4884624 : CollatzResearch.WordTrace tailWord_4884624 prefixEnd_4884624 2508159928487402119836029 := by
  unfold tailWord_4884624
  simp only [CollatzResearch.WordTrace]
  refine ⟨89078436727924475104038463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118771248970565966805384617 89078436727924475104038463)
  ·
    refine ⟨133617655091886712656057695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89078436727924475104038463 133617655091886712656057695)
    ·
      refine ⟨200426482637830068984086543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133617655091886712656057695 200426482637830068984086543)
      ·
        refine ⟨300639723956745103476129815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200426482637830068984086543 300639723956745103476129815)
        ·
          refine ⟨450959585935117655214194723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300639723956745103476129815 450959585935117655214194723)
          ·
            refine ⟨676439378902676482821292085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450959585935117655214194723 676439378902676482821292085)
            ·
              refine ⟨63416191772125920264496133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 676439378902676482821292085 63416191772125920264496133)
              ·
                refine ⟨11890535957273610049593025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63416191772125920264496133 11890535957273610049593025)
                ·
                  refine ⟨8917901967955207537194769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11890535957273610049593025 8917901967955207537194769)
                  ·
                    refine ⟨6688426475966405652896077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8917901967955207537194769 6688426475966405652896077)
                    ·
                      refine ⟨2508159928487402119836029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6688426475966405652896077 2508159928487402119836029)
                      ·
                        rfl

theorem cell23_4884624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 3].length) (baseStart_4884624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884624 prefixEnd_4884624 := by exact prefixLift 4884624
  have htrace : WordTrace (prefixWord ++ tailWord_4884624) baseStart_4884624 baseEnd_4884624 := by
    simpa [prefixWord, tailWord_4884624, baseEnd_4884624] using wordTrace_append hprefix tailTrace_4884624
  have hstable : (prefixWord ++ tailWord_4884624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884624).length < 2 ^ (prefixWord ++ tailWord_4884624).sum := by decide
  have hdescent : baseEnd_4884624 < baseStart_4884624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884714 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_4884714 : Nat := 118140960795 + 4884714 * 2 ^ 59
def prefixEnd_4884714 : Nat := 4983230072969 + 3 ^ 40 * 4884714 * 2
def baseEnd_4884714 : Nat := 2508206141746306767710615

theorem tailTrace_4884714 : CollatzResearch.WordTrace tailWord_4884714 prefixEnd_4884714 2508206141746306767710615 := by
  unfold tailWord_4884714
  simp only [CollatzResearch.WordTrace]
  refine ⟨44540039006380723894713299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118773437350348597052568797 44540039006380723894713299)
  ·
    refine ⟨66810058509571085842069949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44540039006380723894713299 66810058509571085842069949)
    ·
      refine ⟨25053771941089157190776231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66810058509571085842069949 25053771941089157190776231)
      ·
        refine ⟨37580657911633735786164347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25053771941089157190776231 37580657911633735786164347)
        ·
          refine ⟨56370986867450603679246521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37580657911633735786164347 56370986867450603679246521)
          ·
            refine ⟨42278240150587952759434891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56370986867450603679246521 42278240150587952759434891)
            ·
              refine ⟨63417360225881929139152337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42278240150587952759434891 63417360225881929139152337)
              ·
                refine ⟨47563020169411446854364253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63417360225881929139152337 47563020169411446854364253)
                ·
                  refine ⟨17836132563529292570386595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47563020169411446854364253 17836132563529292570386595)
                  ·
                    refine ⟨26754198845293938855579893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17836132563529292570386595 26754198845293938855579893)
                    ·
                      refine ⟨2508206141746306767710615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26754198845293938855579893 2508206141746306767710615)
                      ·
                        rfl

theorem cell23_4884714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_4884714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884714 prefixEnd_4884714 := by exact prefixLift 4884714
  have htrace : WordTrace (prefixWord ++ tailWord_4884714) baseStart_4884714 baseEnd_4884714 := by
    simpa [prefixWord, tailWord_4884714, baseEnd_4884714] using wordTrace_append hprefix tailTrace_4884714
  have hstable : (prefixWord ++ tailWord_4884714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884714).length < 2 ^ (prefixWord ++ tailWord_4884714).sum := by decide
  have hdescent : baseEnd_4884714 < baseStart_4884714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884722 : List Nat := [3, 2, 1, 3, 2, 3, 1, 3, 1, 1, 3]
def baseStart_4884722 : Nat := 118140960795 + 4884722 * 2 ^ 59
def prefixEnd_4884722 : Nat := 4983230072969 + 3 ^ 40 * 4884722 * 2
def baseEnd_4884722 : Nat := 2508210249591542736410579

theorem tailTrace_4884722 : CollatzResearch.WordTrace tailWord_4884722 prefixEnd_4884722 2508210249591542736410579 := by
  unfold tailWord_4884722
  simp only [CollatzResearch.WordTrace]
  refine ⟨44540111952373478236286105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118773631872995941963429613 44540111952373478236286105)
  ·
    refine ⟨33405083964280108677214579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44540111952373478236286105 33405083964280108677214579)
    ·
      refine ⟨50107625946420163015821869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33405083964280108677214579 50107625946420163015821869)
      ·
        refine ⟨18790359729907561130933201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50107625946420163015821869 18790359729907561130933201)
        ·
          refine ⟨14092769797430670848199901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18790359729907561130933201 14092769797430670848199901)
          ·
            refine ⟨5284788674036501568074963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14092769797430670848199901 5284788674036501568074963)
            ·
              refine ⟨7927183011054752352112445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5284788674036501568074963 7927183011054752352112445)
              ·
                refine ⟨2972693629145532132042167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7927183011054752352112445 2972693629145532132042167)
                ·
                  refine ⟨4459040443718298198063251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2972693629145532132042167 4459040443718298198063251)
                  ·
                    refine ⟨6688560665577447297094877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4459040443718298198063251 6688560665577447297094877)
                    ·
                      refine ⟨2508210249591542736410579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6688560665577447297094877 2508210249591542736410579)
                      ·
                        rfl

theorem cell23_4884722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_4884722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884722 prefixEnd_4884722 := by exact prefixLift 4884722
  have htrace : WordTrace (prefixWord ++ tailWord_4884722) baseStart_4884722 baseEnd_4884722 := by
    simpa [prefixWord, tailWord_4884722, baseEnd_4884722] using wordTrace_append hprefix tailTrace_4884722
  have hstable : (prefixWord ++ tailWord_4884722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884722).length < 2 ^ (prefixWord ++ tailWord_4884722).sum := by decide
  have hdescent : baseEnd_4884722 < baseStart_4884722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884738 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_4884738 : Nat := 118140960795 + 4884738 * 2 ^ 59
def prefixEnd_4884738 : Nat := 4983230072969 + 3 ^ 40 * 4884738 * 2
def baseEnd_4884738 : Nat := 836072821760671557936835

theorem tailTrace_4884738 : CollatzResearch.WordTrace tailWord_4884738 prefixEnd_4884738 836072821760671557936835 := by
  unfold tailWord_4884738
  simp only [CollatzResearch.WordTrace]
  refine ⟨44540257844358986919431717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118774020918290631785151245 44540257844358986919431717)
  ·
    refine ⟨8351298345817310047393447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44540257844358986919431717 8351298345817310047393447)
    ·
      refine ⟨12526947518725965071090171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8351298345817310047393447 12526947518725965071090171)
      ·
        refine ⟨18790421278088947606635257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12526947518725965071090171 18790421278088947606635257)
        ·
          refine ⟨14092815958566710704976443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18790421278088947606635257 14092815958566710704976443)
          ·
            refine ⟨21139223937850066057464665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14092815958566710704976443 21139223937850066057464665)
            ·
              refine ⟨15854417953387549543098499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21139223937850066057464665 15854417953387549543098499)
              ·
                refine ⟨23781626930081324314647749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15854417953387549543098499 23781626930081324314647749)
                ·
                  refine ⟨4459055049390248308996453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23781626930081324314647749 4459055049390248308996453)
                  ·
                    refine ⟨836072821760671557936835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4459055049390248308996453 836072821760671557936835)
                    ·
                      rfl

theorem cell23_4884738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_4884738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884738 prefixEnd_4884738 := by exact prefixLift 4884738
  have htrace : WordTrace (prefixWord ++ tailWord_4884738) baseStart_4884738 baseEnd_4884738 := by
    simpa [prefixWord, tailWord_4884738, baseEnd_4884738] using wordTrace_append hprefix tailTrace_4884738
  have hstable : (prefixWord ++ tailWord_4884738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884738).length < 2 ^ (prefixWord ++ tailWord_4884738).sum := by decide
  have hdescent : baseEnd_4884738 < baseStart_4884738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884745 : List Nat := [1, 2, 1, 1, 3, 6, 1, 1, 3, 2, 2]
def baseStart_4884745 : Nat := 118140960795 + 4884745 * 2 ^ 59
def prefixEnd_4884745 : Nat := 4983230072969 + 3 ^ 40 * 4884745 * 2
def baseEnd_4884745 : Nat := 2508222059646596146422973

theorem tailTrace_4884745 : CollatzResearch.WordTrace tailWord_4884745 prefixEnd_4884745 2508222059646596146422973 := by
  unfold tailWord_4884745
  simp only [CollatzResearch.WordTrace]
  refine ⟨178161286688410587873231689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118774191125607058582154459 178161286688410587873231689)
  ·
    refine ⟨133620965016307940904923767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178161286688410587873231689 133620965016307940904923767)
    ·
      refine ⟨200431447524461911357385651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133620965016307940904923767 200431447524461911357385651)
      ·
        refine ⟨300647171286692867036078477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200431447524461911357385651 300647171286692867036078477)
        ·
          refine ⟨112742689232509825138529429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 300647171286692867036078477 112742689232509825138529429)
          ·
            refine ⟨5284813557773898053368567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 112742689232509825138529429 5284813557773898053368567)
            ·
              refine ⟨7927220336660847080052851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5284813557773898053368567 7927220336660847080052851)
              ·
                refine ⟨11890830504991270620079277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7927220336660847080052851 11890830504991270620079277)
                ·
                  refine ⟨4459061439371726482529729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11890830504991270620079277 4459061439371726482529729)
                  ·
                    refine ⟨3344296079528794861897297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4459061439371726482529729 3344296079528794861897297)
                    ·
                      refine ⟨2508222059646596146422973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3344296079528794861897297 2508222059646596146422973)
                      ·
                        rfl

theorem cell23_4884745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 2, 2].length) (baseStart_4884745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884745 prefixEnd_4884745 := by exact prefixLift 4884745
  have htrace : WordTrace (prefixWord ++ tailWord_4884745) baseStart_4884745 baseEnd_4884745 := by
    simpa [prefixWord, tailWord_4884745, baseEnd_4884745] using wordTrace_append hprefix tailTrace_4884745
  have hstable : (prefixWord ++ tailWord_4884745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884745).length < 2 ^ (prefixWord ++ tailWord_4884745).sum := by decide
  have hdescent : baseEnd_4884745 < baseStart_4884745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884782 : List Nat := [4, 1, 3, 3, 2, 1, 1, 1, 1, 1, 5]
def baseStart_4884782 : Nat := 118140960795 + 4884782 * 2 ^ 59
def prefixEnd_4884782 : Nat := 4983230072969 + 3 ^ 40 * 4884782 * 2
def baseEnd_4884782 : Nat := 2508241058430812501660303

theorem tailTrace_4884782 : CollatzResearch.WordTrace tailWord_4884782 prefixEnd_4884782 2508241058430812501660303 := by
  unfold tailWord_4884782
  simp only [CollatzResearch.WordTrace]
  refine ⟨22270329523659567899041075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118775090792851028794885733 22270329523659567899041075)
  ·
    refine ⟨33405494285489351848561613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22270329523659567899041075 33405494285489351848561613)
    ·
      refine ⟨12527060357058506943210605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33405494285489351848561613 12527060357058506943210605)
      ·
        refine ⟨4697647633896940103703977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12527060357058506943210605 4697647633896940103703977)
        ·
          refine ⟨3523235725422705077777983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4697647633896940103703977 3523235725422705077777983)
          ·
            refine ⟨5284853588134057616666975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3523235725422705077777983 5284853588134057616666975)
            ·
              refine ⟨7927280382201086425000463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5284853588134057616666975 7927280382201086425000463)
              ·
                refine ⟨11890920573301629637500695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7927280382201086425000463 11890920573301629637500695)
                ·
                  refine ⟨17836380859952444456251043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11890920573301629637500695 17836380859952444456251043)
                  ·
                    refine ⟨26754571289928666684376565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17836380859952444456251043 26754571289928666684376565)
                    ·
                      refine ⟨2508241058430812501660303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26754571289928666684376565 2508241058430812501660303)
                      ·
                        rfl

theorem cell23_4884782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_4884782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884782 prefixEnd_4884782 := by exact prefixLift 4884782
  have htrace : WordTrace (prefixWord ++ tailWord_4884782) baseStart_4884782 baseEnd_4884782 := by
    simpa [prefixWord, tailWord_4884782, baseEnd_4884782] using wordTrace_append hprefix tailTrace_4884782
  have hstable : (prefixWord ++ tailWord_4884782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884782).length < 2 ^ (prefixWord ++ tailWord_4884782).sum := by decide
  have hdescent : baseEnd_4884782 < baseStart_4884782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884818 : List Nat := [3, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2]
def baseStart_4884818 : Nat := 118140960795 + 4884818 * 2 ^ 59
def prefixEnd_4884818 : Nat := 4983230072969 + 3 ^ 40 * 4884818 * 2
def baseEnd_4884818 : Nat := 2508259543734374360810137

theorem tailTrace_4884818 : CollatzResearch.WordTrace tailWord_4884818 prefixEnd_4884818 2508259543734374360810137 := by
  unfold tailWord_4884818
  simp only [CollatzResearch.WordTrace]
  refine ⟨44540987304286530335159777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118775966144764080893759405 44540987304286530335159777)
  ·
    refine ⟨33405740478214897751369833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44540987304286530335159777 33405740478214897751369833)
    ·
      refine ⟨25054305358661173313527375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33405740478214897751369833 25054305358661173313527375)
      ·
        refine ⟨37581458037991759970291063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25054305358661173313527375 37581458037991759970291063)
        ·
          refine ⟨56372187056987639955436595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37581458037991759970291063 56372187056987639955436595)
          ·
            refine ⟨84558280585481459933154893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56372187056987639955436595 84558280585481459933154893)
            ·
              refine ⟨31709355219555547474933085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84558280585481459933154893 31709355219555547474933085)
              ·
                refine ⟨11891008207333330303099907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31709355219555547474933085 11891008207333330303099907)
                ·
                  refine ⟨17836512310999995454649861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11891008207333330303099907 17836512310999995454649861)
                  ·
                    refine ⟨3344346058312499147746849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17836512310999995454649861 3344346058312499147746849)
                    ·
                      refine ⟨2508259543734374360810137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3344346058312499147746849 2508259543734374360810137)
                      ·
                        rfl

theorem cell23_4884818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_4884818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884818 prefixEnd_4884818 := by exact prefixLift 4884818
  have htrace : WordTrace (prefixWord ++ tailWord_4884818) baseStart_4884818 baseEnd_4884818 := by
    simpa [prefixWord, tailWord_4884818, baseEnd_4884818] using wordTrace_append hprefix tailTrace_4884818
  have hstable : (prefixWord ++ tailWord_4884818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884818).length < 2 ^ (prefixWord ++ tailWord_4884818).sum := by decide
  have hdescent : baseEnd_4884818 < baseStart_4884818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884830 : List Nat := [4, 4, 2, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_4884830 : Nat := 118140960795 + 4884830 * 2 ^ 59
def prefixEnd_4884830 : Nat := 4983230072969 + 3 ^ 40 * 4884830 * 2
def baseEnd_4884830 : Nat := 2508265705502228313860083

theorem tailTrace_4884830 : CollatzResearch.WordTrace tailWord_4884830 prefixEnd_4884830 2508265705502228313860083 := by
  unfold tailWord_4884830
  simp only [CollatzResearch.WordTrace]
  refine ⟨22270548361637830923759493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118776257928735098260050629 22270548361637830923759493)
  ·
    refine ⟨4175727817807093298204905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22270548361637830923759493 4175727817807093298204905)
    ·
      refine ⟨3131795863355319973653679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4175727817807093298204905 3131795863355319973653679)
      ·
        refine ⟨4697693795032979960480519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3131795863355319973653679 4697693795032979960480519)
        ·
          refine ⟨7046540692549469940720779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4697693795032979960480519 7046540692549469940720779)
          ·
            refine ⟨10569811038824204911081169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7046540692549469940720779 10569811038824204911081169)
            ·
              refine ⟨7927358279118153683310877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10569811038824204911081169 7927358279118153683310877)
              ·
                refine ⟨2972759354669307631241579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7927358279118153683310877 2972759354669307631241579)
                ·
                  refine ⟨4459139032003961446862369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2972759354669307631241579 4459139032003961446862369)
                  ·
                    refine ⟨3344354274002971085146777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4459139032003961446862369 3344354274002971085146777)
                    ·
                      refine ⟨2508265705502228313860083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3344354274002971085146777 2508265705502228313860083)
                      ·
                        rfl

theorem cell23_4884830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_4884830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884830 prefixEnd_4884830 := by exact prefixLift 4884830
  have htrace : WordTrace (prefixWord ++ tailWord_4884830) baseStart_4884830 baseEnd_4884830 := by
    simpa [prefixWord, tailWord_4884830, baseEnd_4884830] using wordTrace_append hprefix tailTrace_4884830
  have hstable : (prefixWord ++ tailWord_4884830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884830).length < 2 ^ (prefixWord ++ tailWord_4884830).sum := by decide
  have hdescent : baseEnd_4884830 < baseStart_4884830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884965 : List Nat := [1, 3, 1, 5, 2, 1, 2, 2, 6]
def baseStart_4884965 : Nat := 118140960795 + 4884965 * 2 ^ 59
def prefixEnd_4884965 : Nat := 4983230072969 + 3 ^ 40 * 4884965 * 2
def baseEnd_4884965 : Nat := 278703891710065031741329

theorem tailTrace_4884965 : CollatzResearch.WordTrace tailWord_4884965 prefixEnd_4884965 278703891710065031741329 := by
  unfold tailWord_4884965
  simp only [CollatzResearch.WordTrace]
  refine ⟨178169310747613565446240349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118779540498409043630826899 178169310747613565446240349)
  ·
    refine ⟨66813491530355087042340131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178169310747613565446240349 66813491530355087042340131)
    ·
      refine ⟨100220237295532630563510197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66813491530355087042340131 100220237295532630563510197)
      ·
        refine ⟨9395647246456184115329081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100220237295532630563510197 9395647246456184115329081)
        ·
          refine ⟨7046735434842138086496811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9395647246456184115329081 7046735434842138086496811)
          ·
            refine ⟨10570103152263207129745217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7046735434842138086496811 10570103152263207129745217)
            ·
              refine ⟨7927577364197405347308913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10570103152263207129745217 7927577364197405347308913)
              ·
                refine ⟨5945683023148054010481685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7927577364197405347308913 5945683023148054010481685)
                ·
                  refine ⟨278703891710065031741329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5945683023148054010481685 278703891710065031741329)
                  ·
                    rfl

theorem cell23_4884965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 6].length) (baseStart_4884965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4884965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4884965 prefixEnd_4884965 := by exact prefixLift 4884965
  have htrace : WordTrace (prefixWord ++ tailWord_4884965) baseStart_4884965 baseEnd_4884965 := by
    simpa [prefixWord, tailWord_4884965, baseEnd_4884965] using wordTrace_append hprefix tailTrace_4884965
  have hstable : (prefixWord ++ tailWord_4884965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884965).length < 2 ^ (prefixWord ++ tailWord_4884965).sum := by decide
  have hdescent : baseEnd_4884965 < baseStart_4884965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885001 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 5, 1, 5]
def baseStart_4885001 : Nat := 118140960795 + 4885001 * 2 ^ 59
def prefixEnd_4885001 : Nat := 4983230072969 + 3 ^ 40 * 4885001 * 2
def baseEnd_4885001 : Nat := 2508353510694147144821795

theorem tailTrace_4885001 : CollatzResearch.WordTrace tailWord_4885001 prefixEnd_4885001 2508353510694147144821795 := by
  unfold tailWord_4885001
  simp only [CollatzResearch.WordTrace]
  refine ⟨178170623775483143594550857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118780415850322095729700571 178170623775483143594550857)
  ·
    refine ⟨133627967831612357695913143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178170623775483143594550857 133627967831612357695913143)
    ·
      refine ⟨200441951747418536543869715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133627967831612357695913143 200441951747418536543869715)
      ·
        refine ⟨300662927621127804815804573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200441951747418536543869715 300662927621127804815804573)
        ·
          refine ⟨112748597857922926805926715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 300662927621127804815804573 112748597857922926805926715)
          ·
            refine ⟨169122896786884390208890073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112748597857922926805926715 169122896786884390208890073)
            ·
              refine ⟨126842172590163292656667555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169122896786884390208890073 126842172590163292656667555)
              ·
                refine ⟨190263258885244938985001333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126842172590163292656667555 190263258885244938985001333)
                ·
                  refine ⟨17837180520491713029843875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 190263258885244938985001333 17837180520491713029843875)
                  ·
                    refine ⟨26755770780737569544765813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17837180520491713029843875 26755770780737569544765813)
                    ·
                      refine ⟨2508353510694147144821795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26755770780737569544765813 2508353510694147144821795)
                      ·
                        rfl

theorem cell23_4885001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 1, 5].length) (baseStart_4885001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885001 prefixEnd_4885001 := by exact prefixLift 4885001
  have htrace : WordTrace (prefixWord ++ tailWord_4885001) baseStart_4885001 baseEnd_4885001 := by
    simpa [prefixWord, tailWord_4885001, baseEnd_4885001] using wordTrace_append hprefix tailTrace_4885001
  have hstable : (prefixWord ++ tailWord_4885001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885001).length < 2 ^ (prefixWord ++ tailWord_4885001).sum := by decide
  have hdescent : baseEnd_4885001 < baseStart_4885001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885012 : List Nat := [2, 4, 3, 1, 1, 2, 1, 3, 1, 5]
def baseStart_4885012 : Nat := 118140960795 + 4885012 * 2 ^ 59
def prefixEnd_4885012 : Nat := 4983230072969 + 3 ^ 40 * 4885012 * 2
def baseEnd_4885012 : Nat := 836119719660448867261415

theorem tailTrace_4885012 : CollatzResearch.WordTrace tailWord_4885012 prefixEnd_4885012 836119719660448867261415 := by
  unfold tailWord_4885012
  simp only [CollatzResearch.WordTrace]
  refine ⟨89085512489221646236600645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118780683318962194982134193 89085512489221646236600645)
  ·
    refine ⟨16703533591729058669362621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89085512489221646236600645 16703533591729058669362621)
    ·
      refine ⟨6263825096898397001010983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16703533591729058669362621 6263825096898397001010983)
      ·
        refine ⟨9395737645347595501516475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6263825096898397001010983 9395737645347595501516475)
        ·
          refine ⟨14093606468021393252274713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9395737645347595501516475 14093606468021393252274713)
          ·
            refine ⟨10570204851016044939206035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14093606468021393252274713 10570204851016044939206035)
            ·
              refine ⟨15855307276524067408809053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10570204851016044939206035 15855307276524067408809053)
              ·
                refine ⟨5945740228696525278303395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15855307276524067408809053 5945740228696525278303395)
                ·
                  refine ⟨8918610343044787917455093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5945740228696525278303395 8918610343044787917455093)
                  ·
                    refine ⟨836119719660448867261415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8918610343044787917455093 836119719660448867261415)
                    ·
                      rfl

theorem cell23_4885012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_4885012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885012 prefixEnd_4885012 := by exact prefixLift 4885012
  have htrace : WordTrace (prefixWord ++ tailWord_4885012) baseStart_4885012 baseEnd_4885012 := by
    simpa [prefixWord, tailWord_4885012, baseEnd_4885012] using wordTrace_append hprefix tailTrace_4885012
  have hstable : (prefixWord ++ tailWord_4885012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885012).length < 2 ^ (prefixWord ++ tailWord_4885012).sum := by decide
  have hdescent : baseEnd_4885012 < baseStart_4885012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885052 : List Nat := [2, 2, 2, 2, 3, 2, 2, 2, 1, 2, 3]
def baseStart_4885052 : Nat := 118140960795 + 4885052 * 2 ^ 59
def prefixEnd_4885052 : Nat := 4983230072969 + 3 ^ 40 * 4885052 * 2
def baseEnd_4885052 : Nat := 2508379698207526445284061

theorem tailTrace_4885052 : CollatzResearch.WordTrace tailWord_4885052 prefixEnd_4885052 2508379698207526445284061 := by
  unfold tailWord_4885052
  simp only [CollatzResearch.WordTrace]
  refine ⟨89086241949149189652328705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118781655932198919536438273 89086241949149189652328705)
  ·
    refine ⟨66814681461861892239246529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89086241949149189652328705 66814681461861892239246529)
    ·
      refine ⟨50111011096396419179434897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66814681461861892239246529 50111011096396419179434897)
      ·
        refine ⟨37583258322297314384576173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50111011096396419179434897 37583258322297314384576173)
        ·
          refine ⟨14093721870861492894216065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37583258322297314384576173 14093721870861492894216065)
          ·
            refine ⟨10570291403146119670662049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14093721870861492894216065 10570291403146119670662049)
            ·
              refine ⟨7927718552359589752996537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10570291403146119670662049 7927718552359589752996537)
              ·
                refine ⟨5945788914269692314747403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7927718552359589752996537 5945788914269692314747403)
                ·
                  refine ⟨8918683371404538472121105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5945788914269692314747403 8918683371404538472121105)
                  ·
                    refine ⟨6689012528553403854090829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8918683371404538472121105 6689012528553403854090829)
                    ·
                      refine ⟨2508379698207526445284061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6689012528553403854090829 2508379698207526445284061)
                      ·
                        rfl

theorem cell23_4885052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_4885052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885052 prefixEnd_4885052 := by exact prefixLift 4885052
  have htrace : WordTrace (prefixWord ++ tailWord_4885052) baseStart_4885052 baseEnd_4885052 := by
    simpa [prefixWord, tailWord_4885052, baseEnd_4885052] using wordTrace_append hprefix tailTrace_4885052
  have hstable : (prefixWord ++ tailWord_4885052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885052).length < 2 ^ (prefixWord ++ tailWord_4885052).sum := by decide
  have hdescent : baseEnd_4885052 < baseStart_4885052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885060 : List Nat := [2, 3, 5, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_4885060 : Nat := 118140960795 + 4885060 * 2 ^ 59
def prefixEnd_4885060 : Nat := 4983230072969 + 3 ^ 40 * 4885060 * 2
def baseEnd_4885060 : Nat := 2508383806052762413984025

theorem tailTrace_4885060 : CollatzResearch.WordTrace tailWord_4885060 prefixEnd_4885060 2508383806052762413984025 := by
  unfold tailWord_4885060
  simp only [CollatzResearch.WordTrace]
  refine ⟨89086387841134698335474317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118781850454846264447299089 89086387841134698335474317)
  ·
    refine ⟨33407395440425511875802869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89086387841134698335474317 33407395440425511875802869)
    ·
      refine ⟨3131943322539891738356519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33407395440425511875802869 3131943322539891738356519)
      ·
        refine ⟨4697914983809837607534779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3131943322539891738356519 4697914983809837607534779)
        ·
          refine ⟨7046872475714756411302169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4697914983809837607534779 7046872475714756411302169)
          ·
            refine ⟨5285154356786067308476627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7046872475714756411302169 5285154356786067308476627)
            ·
              refine ⟨7927731535179100962714941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5285154356786067308476627 7927731535179100962714941)
              ·
                refine ⟨2972899325692162861018103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7927731535179100962714941 2972899325692162861018103)
                ·
                  refine ⟨4459348988538244291527155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2972899325692162861018103 4459348988538244291527155)
                  ·
                    refine ⟨6689023482807366437290733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4459348988538244291527155 6689023482807366437290733)
                    ·
                      refine ⟨2508383806052762413984025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6689023482807366437290733 2508383806052762413984025)
                      ·
                        rfl

theorem cell23_4885060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_4885060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885060 prefixEnd_4885060 := by exact prefixLift 4885060
  have htrace : WordTrace (prefixWord ++ tailWord_4885060) baseStart_4885060 baseEnd_4885060 := by
    simpa [prefixWord, tailWord_4885060, baseEnd_4885060] using wordTrace_append hprefix tailTrace_4885060
  have hstable : (prefixWord ++ tailWord_4885060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885060).length < 2 ^ (prefixWord ++ tailWord_4885060).sum := by decide
  have hdescent : baseEnd_4885060 < baseStart_4885060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885066 : List Nat := [3, 1, 2, 1, 1, 6, 1, 3, 1, 2, 2]
def baseStart_4885066 : Nat := 118140960795 + 4885066 * 2 ^ 59
def prefixEnd_4885066 : Nat := 4983230072969 + 3 ^ 40 * 4885066 * 2
def baseEnd_4885066 : Nat := 2508386886936689390508997

theorem tailTrace_4885066 : CollatzResearch.WordTrace tailWord_4885066 prefixEnd_4885066 2508386886936689390508997 := by
  unfold tailWord_4885066
  simp only [CollatzResearch.WordTrace]
  refine ⟨44543248630061914923916763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118781996346831773130444701 44543248630061914923916763)
  ·
    refine ⟨66814872945092872385875145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44543248630061914923916763 66814872945092872385875145)
    ·
      refine ⟨50111154708819654289406359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66814872945092872385875145 50111154708819654289406359)
      ·
        refine ⟨75166732063229481434109539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50111154708819654289406359 75166732063229481434109539)
        ·
          refine ⟨112750098094844222151164309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75166732063229481434109539 112750098094844222151164309)
          ·
            refine ⟨5285160848195822913335827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 112750098094844222151164309 5285160848195822913335827)
            ·
              refine ⟨7927741272293734370003741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5285160848195822913335827 7927741272293734370003741)
              ·
                refine ⟨2972902977110150388751403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7927741272293734370003741 2972902977110150388751403)
                ·
                  refine ⟨4459354465665225583127105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2972902977110150388751403 4459354465665225583127105)
                  ·
                    refine ⟨3344515849248919187345329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4459354465665225583127105 3344515849248919187345329)
                    ·
                      refine ⟨2508386886936689390508997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3344515849248919187345329 2508386886936689390508997)
                      ·
                        rfl

theorem cell23_4885066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 1, 2, 2].length) (baseStart_4885066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885066 prefixEnd_4885066 := by exact prefixLift 4885066
  have htrace : WordTrace (prefixWord ++ tailWord_4885066) baseStart_4885066 baseEnd_4885066 := by
    simpa [prefixWord, tailWord_4885066, baseEnd_4885066] using wordTrace_append hprefix tailTrace_4885066
  have hstable : (prefixWord ++ tailWord_4885066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885066).length < 2 ^ (prefixWord ++ tailWord_4885066).sum := by decide
  have hdescent : baseEnd_4885066 < baseStart_4885066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885098 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 1, 8]
def baseStart_4885098 : Nat := 118140960795 + 4885098 * 2 ^ 59
def prefixEnd_4885098 : Nat := 4983230072969 + 3 ^ 40 * 4885098 * 2
def baseEnd_4885098 : Nat := 836134439439211088436283

theorem tailTrace_4885098 : CollatzResearch.WordTrace tailWord_4885098 prefixEnd_4885098 836134439439211088436283 := by
  unfold tailWord_4885098
  simp only [CollatzResearch.WordTrace]
  refine ⟨44543540414032932290207987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118782774437421152773887965 44543540414032932290207987)
  ·
    refine ⟨66815310621049398435311981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44543540414032932290207987 66815310621049398435311981)
    ·
      refine ⟨25055741482893524413241993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66815310621049398435311981 25055741482893524413241993)
      ·
        refine ⟨18791806112170143309931495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25055741482893524413241993 18791806112170143309931495)
        ·
          refine ⟨28187709168255214964897243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18791806112170143309931495 28187709168255214964897243)
          ·
            refine ⟨42281563752382822447345865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28187709168255214964897243 42281563752382822447345865)
            ·
              refine ⟨31711172814287116835509399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42281563752382822447345865 31711172814287116835509399)
              ·
                refine ⟨47566759221430675253264099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31711172814287116835509399 47566759221430675253264099)
                ·
                  refine ⟨71350138832146012879896149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47566759221430675253264099 71350138832146012879896149)
                  ·
                    refine ⟨836134439439211088436283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71350138832146012879896149 836134439439211088436283)
                    ·
                      rfl

theorem cell23_4885098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_4885098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885098 prefixEnd_4885098 := by exact prefixLift 4885098
  have htrace : WordTrace (prefixWord ++ tailWord_4885098) baseStart_4885098 baseEnd_4885098 := by
    simpa [prefixWord, tailWord_4885098, baseEnd_4885098] using wordTrace_append hprefix tailTrace_4885098
  have hstable : (prefixWord ++ tailWord_4885098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885098).length < 2 ^ (prefixWord ++ tailWord_4885098).sum := by decide
  have hdescent : baseEnd_4885098 < baseStart_4885098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885109 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 3, 3, 2]
def baseStart_4885109 : Nat := 118140960795 + 4885109 * 2 ^ 59
def prefixEnd_4885109 : Nat := 4983230072969 + 3 ^ 40 * 4885109 * 2
def baseEnd_4885109 : Nat := 2508408966604832722271299

theorem tailTrace_4885109 : CollatzResearch.WordTrace tailWord_4885109 prefixEnd_4885109 2508408966604832722271299 := by
  unfold tailWord_4885109
  simp only [CollatzResearch.WordTrace]
  refine ⟨178174562859091878039482381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118783041906061252026321587 178174562859091878039482381)
  ·
    refine ⟨66815461072159454264805893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178174562859091878039482381 66815461072159454264805893)
    ·
      refine ⟨12527898951029897674651105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66815461072159454264805893 12527898951029897674651105)
      ·
        refine ⟨9395924213272423255988329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12527898951029897674651105 9395924213272423255988329)
        ·
          refine ⟨7046943159954317441991247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9395924213272423255988329 7046943159954317441991247)
          ·
            refine ⟨10570414739931476162986871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7046943159954317441991247 10570414739931476162986871)
            ·
              refine ⟨15855622109897214244480307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10570414739931476162986871 15855622109897214244480307)
              ·
                refine ⟨23783433164845821366720461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15855622109897214244480307 23783433164845821366720461)
                ·
                  refine ⟨8918787436817183012520173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23783433164845821366720461 8918787436817183012520173)
                  ·
                    refine ⟨3344545288806443629695065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8918787436817183012520173 3344545288806443629695065)
                    ·
                      refine ⟨2508408966604832722271299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3344545288806443629695065 2508408966604832722271299)
                      ·
                        rfl

theorem cell23_4885109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_4885109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885109 prefixEnd_4885109 := by exact prefixLift 4885109
  have htrace : WordTrace (prefixWord ++ tailWord_4885109) baseStart_4885109 baseEnd_4885109 := by
    simpa [prefixWord, tailWord_4885109, baseEnd_4885109] using wordTrace_append hprefix tailTrace_4885109
  have hstable : (prefixWord ++ tailWord_4885109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885109).length < 2 ^ (prefixWord ++ tailWord_4885109).sum := by decide
  have hdescent : baseEnd_4885109 < baseStart_4885109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885145 : List Nat := [1, 2, 1, 2, 1, 2, 5, 4, 5]
def baseStart_4885145 : Nat := 118140960795 + 4885145 * 2 ^ 59
def prefixEnd_4885145 : Nat := 4983230072969 + 3 ^ 40 * 4885145 * 2
def baseEnd_4885145 : Nat := 278714161323154953491237

theorem tailTrace_4885145 : CollatzResearch.WordTrace tailWord_4885145 prefixEnd_4885145 278714161323154953491237 := by
  unfold tailWord_4885145
  simp only [CollatzResearch.WordTrace]
  refine ⟨178175875886961456187792889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118783917257974304125195259 178175875886961456187792889)
  ·
    refine ⟨133631906915221092140844667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178175875886961456187792889 133631906915221092140844667)
    ·
      refine ⟨200447860372831638211267001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133631906915221092140844667 200447860372831638211267001)
      ·
        refine ⟨150335895279623728658450251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200447860372831638211267001 150335895279623728658450251)
        ·
          refine ⟨225503842919435592987675377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150335895279623728658450251 225503842919435592987675377)
          ·
            refine ⟨169127882189576694740756533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225503842919435592987675377 169127882189576694740756533)
            ·
              refine ⟨15855738955272815131945925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 169127882189576694740756533 15855738955272815131945925)
              ·
                refine ⟨2972951054113652837239861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15855738955272815131945925 2972951054113652837239861)
                ·
                  refine ⟨278714161323154953491237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2972951054113652837239861 278714161323154953491237)
                  ·
                    rfl

theorem cell23_4885145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 5].length) (baseStart_4885145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885145 prefixEnd_4885145 := by exact prefixLift 4885145
  have htrace : WordTrace (prefixWord ++ tailWord_4885145) baseStart_4885145 baseEnd_4885145 := by
    simpa [prefixWord, tailWord_4885145, baseEnd_4885145] using wordTrace_append hprefix tailTrace_4885145
  have hstable : (prefixWord ++ tailWord_4885145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885145).length < 2 ^ (prefixWord ++ tailWord_4885145).sum := by decide
  have hdescent : baseEnd_4885145 < baseStart_4885145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885175 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 1, 7]
def baseStart_4885175 : Nat := 118140960795 + 4885175 * 2 ^ 59
def prefixEnd_4885175 : Nat := 4983230072969 + 3 ^ 40 * 4885175 * 2
def baseEnd_4885175 : Nat := 836147618776009821348665

theorem tailTrace_4885175 : CollatzResearch.WordTrace tailWord_4885175 prefixEnd_4885175 836147618776009821348665 := by
  unfold tailWord_4885175
  simp only [CollatzResearch.WordTrace]
  refine ⟨178176970076852771311384979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118784646717901847540923319 178176970076852771311384979)
  ·
    refine ⟨267265455115279156967077469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178176970076852771311384979 267265455115279156967077469)
    ·
      refine ⟨100224545668229683862654051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267265455115279156967077469 100224545668229683862654051)
      ·
        refine ⟨150336818502344525793981077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100224545668229683862654051 150336818502344525793981077)
        ·
          refine ⟨7047038367297399646592863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 150336818502344525793981077 7047038367297399646592863)
          ·
            refine ⟨10570557550946099469889295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7047038367297399646592863 10570557550946099469889295)
            ·
              refine ⟨15855836326419149204833943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10570557550946099469889295 15855836326419149204833943)
              ·
                refine ⟨23783754489628723807250915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15855836326419149204833943 23783754489628723807250915)
                ·
                  refine ⟨35675631734443085710876373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23783754489628723807250915 35675631734443085710876373)
                  ·
                    refine ⟨836147618776009821348665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35675631734443085710876373 836147618776009821348665)
                    ·
                      rfl

theorem cell23_4885175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 7].length) (baseStart_4885175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885175 prefixEnd_4885175 := by exact prefixLift 4885175
  have htrace : WordTrace (prefixWord ++ tailWord_4885175) baseStart_4885175 baseEnd_4885175 := by
    simpa [prefixWord, tailWord_4885175, baseEnd_4885175] using wordTrace_append hprefix tailTrace_4885175
  have hstable : (prefixWord ++ tailWord_4885175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885175).length < 2 ^ (prefixWord ++ tailWord_4885175).sum := by decide
  have hdescent : baseEnd_4885175 < baseStart_4885175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885212 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_4885212 : Nat := 118140960795 + 4885212 * 2 ^ 59
def prefixEnd_4885212 : Nat := 4983230072969 + 3 ^ 40 * 4885212 * 2
def baseEnd_4885212 : Nat := 2508461855112245819283325

theorem tailTrace_4885212 : CollatzResearch.WordTrace tailWord_4885212 prefixEnd_4885212 2508461855112245819283325 := by
  unfold tailWord_4885212
  simp only [CollatzResearch.WordTrace]
  refine ⟨89089159788859363315240945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118785546385145817753654593 89089159788859363315240945)
  ·
    refine ⟨66816869841644522486430709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89089159788859363315240945 66816869841644522486430709)
    ·
      refine ⟨6264081547654173983102879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66816869841644522486430709 6264081547654173983102879)
      ·
        refine ⟨9396122321481260974654319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6264081547654173983102879 9396122321481260974654319)
        ·
          refine ⟨14094183482221891461981479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9396122321481260974654319 14094183482221891461981479)
          ·
            refine ⟨21141275223332837192972219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14094183482221891461981479 21141275223332837192972219)
            ·
              refine ⟨31711912834999255789458329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21141275223332837192972219 31711912834999255789458329)
              ·
                refine ⟨23783934626249441842093747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31711912834999255789458329 23783934626249441842093747)
                ·
                  refine ⟨35675901939374162763140621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23783934626249441842093747 35675901939374162763140621)
                  ·
                    refine ⟨13378463227265311036177733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35675901939374162763140621 13378463227265311036177733)
                    ·
                      refine ⟨2508461855112245819283325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13378463227265311036177733 2508461855112245819283325)
                      ·
                        rfl

theorem cell23_4885212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_4885212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885212 prefixEnd_4885212 := by exact prefixLift 4885212
  have htrace : WordTrace (prefixWord ++ tailWord_4885212) baseStart_4885212 baseEnd_4885212 := by
    simpa [prefixWord, tailWord_4885212, baseEnd_4885212] using wordTrace_append hprefix tailTrace_4885212
  have hstable : (prefixWord ++ tailWord_4885212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885212).length < 2 ^ (prefixWord ++ tailWord_4885212).sum := by decide
  have hdescent : baseEnd_4885212 < baseStart_4885212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885215 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 3]
def baseStart_4885215 : Nat := 118140960795 + 4885215 * 2 ^ 59
def prefixEnd_4885215 : Nat := 4983230072969 + 3 ^ 40 * 4885215 * 2
def baseEnd_4885215 : Nat := 2508463395554209307545811

theorem tailTrace_4885215 : CollatzResearch.WordTrace tailWord_4885215 prefixEnd_4885215 2508463395554209307545811 := by
  unfold tailWord_4885215
  simp only [CollatzResearch.WordTrace]
  refine ⟨178178428996707858142841099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118785619331138572095227399 178178428996707858142841099)
  ·
    refine ⟨267267643495061787214261649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178178428996707858142841099 267267643495061787214261649)
    ·
      refine ⟨200450732621296340410696237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267267643495061787214261649 200450732621296340410696237)
      ·
        refine ⟨75169024732986127654011089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200450732621296340410696237 75169024732986127654011089)
        ·
          refine ⟨56376768549739595740508317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75169024732986127654011089 56376768549739595740508317)
          ·
            refine ⟨21141288206152348402690619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56376768549739595740508317 21141288206152348402690619)
            ·
              refine ⟨31711932309228522604035929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21141288206152348402690619 31711932309228522604035929)
              ·
                refine ⟨23783949231921391953026947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31711932309228522604035929 23783949231921391953026947)
                ·
                  refine ⟨35675923847882087929540421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23783949231921391953026947 35675923847882087929540421)
                  ·
                    refine ⟨6689235721477891486788829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35675923847882087929540421 6689235721477891486788829)
                    ·
                      refine ⟨2508463395554209307545811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6689235721477891486788829 2508463395554209307545811)
                      ·
                        rfl

theorem cell23_4885215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_4885215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885215 prefixEnd_4885215 := by exact prefixLift 4885215
  have htrace : WordTrace (prefixWord ++ tailWord_4885215) baseStart_4885215 baseEnd_4885215 := by
    simpa [prefixWord, tailWord_4885215, baseEnd_4885215] using wordTrace_append hprefix tailTrace_4885215
  have hstable : (prefixWord ++ tailWord_4885215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885215).length < 2 ^ (prefixWord ++ tailWord_4885215).sum := by decide
  have hdescent : baseEnd_4885215 < baseStart_4885215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885256 : List Nat := [2, 1, 3, 2, 2, 3, 3, 2, 1, 4]
def baseStart_4885256 : Nat := 118140960795 + 4885256 * 2 ^ 59
def prefixEnd_4885256 : Nat := 4983230072969 + 3 ^ 40 * 4885256 * 2
def baseEnd_4885256 : Nat := 836161482753681215711041

theorem tailTrace_4885256 : CollatzResearch.WordTrace tailWord_4885256 prefixEnd_4885256 836161482753681215711041 := by
  unfold tailWord_4885256
  simp only [CollatzResearch.WordTrace]
  refine ⟨89089962194779661072541811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118786616259706214763389081 89089962194779661072541811)
  ·
    refine ⟨133634943292169491608812717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89089962194779661072541811 133634943292169491608812717)
    ·
      refine ⟨50113103734563559353304769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133634943292169491608812717 50113103734563559353304769)
      ·
        refine ⟨37584827800922669514978577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50113103734563559353304769 37584827800922669514978577)
        ·
          refine ⟨28188620850692002136233933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37584827800922669514978577 28188620850692002136233933)
          ·
            refine ⟨10570732819009500801087725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28188620850692002136233933 10570732819009500801087725)
            ·
              refine ⟨3964024807128562800407897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10570732819009500801087725 3964024807128562800407897)
              ·
                refine ⟨2973018605346422100305923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3964024807128562800407897 2973018605346422100305923)
                ·
                  refine ⟨4459527908019633150458885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2973018605346422100305923 4459527908019633150458885)
                  ·
                    refine ⟨836161482753681215711041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4459527908019633150458885 836161482753681215711041)
                    ·
                      rfl

theorem cell23_4885256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_4885256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885256 prefixEnd_4885256 := by exact prefixLift 4885256
  have htrace : WordTrace (prefixWord ++ tailWord_4885256) baseStart_4885256 baseEnd_4885256 := by
    simpa [prefixWord, tailWord_4885256, baseEnd_4885256] using wordTrace_append hprefix tailTrace_4885256
  have hstable : (prefixWord ++ tailWord_4885256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885256).length < 2 ^ (prefixWord ++ tailWord_4885256).sum := by decide
  have hdescent : baseEnd_4885256 < baseStart_4885256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885272 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 6, 3, 2]
def baseStart_4885272 : Nat := 118140960795 + 4885272 * 2 ^ 59
def prefixEnd_4885272 : Nat := 4983230072969 + 3 ^ 40 * 4885272 * 2
def baseEnd_4885272 : Nat := 2508492663951515584533049

theorem tailTrace_4885272 : CollatzResearch.WordTrace tailWord_4885272 prefixEnd_4885272 2508492663951515584533049 := by
  unfold tailWord_4885272
  simp only [CollatzResearch.WordTrace]
  refine ⟨89090253978750678438833035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118787005305000904585110713 89090253978750678438833035)
  ·
    refine ⟨133635380968126017658249553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89090253978750678438833035 133635380968126017658249553)
    ·
      refine ⟨100226535726094513243687165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133635380968126017658249553 100226535726094513243687165)
      ·
        refine ⟨37584950897285442466382687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100226535726094513243687165 37584950897285442466382687)
        ·
          refine ⟨56377426345928163699574031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37584950897285442466382687 56377426345928163699574031)
          ·
            refine ⟨84566139518892245549361047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56377426345928163699574031 84566139518892245549361047)
            ·
              refine ⟨126849209278338368324041571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84566139518892245549361047 126849209278338368324041571)
              ·
                refine ⟨190273813917507552486062357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126849209278338368324041571 190273813917507552486062357)
                ·
                  refine ⟨8919085027383166522784173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 190273813917507552486062357 8919085027383166522784173)
                  ·
                    refine ⟨3344656885268687446044065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8919085027383166522784173 3344656885268687446044065)
                    ·
                      refine ⟨2508492663951515584533049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3344656885268687446044065 2508492663951515584533049)
                      ·
                        rfl

theorem cell23_4885272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_4885272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885272 prefixEnd_4885272 := by exact prefixLift 4885272
  have htrace : WordTrace (prefixWord ++ tailWord_4885272) baseStart_4885272 baseEnd_4885272 := by
    simpa [prefixWord, tailWord_4885272, baseEnd_4885272] using wordTrace_append hprefix tailTrace_4885272
  have hstable : (prefixWord ++ tailWord_4885272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885272).length < 2 ^ (prefixWord ++ tailWord_4885272).sum := by decide
  have hdescent : baseEnd_4885272 < baseStart_4885272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885282 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 3, 5]
def baseStart_4885282 : Nat := 118140960795 + 4885282 * 2 ^ 59
def prefixEnd_4885282 : Nat := 4983230072969 + 3 ^ 40 * 4885282 * 2
def baseEnd_4885282 : Nat := 836165932919353515136001

theorem tailTrace_4885282 : CollatzResearch.WordTrace tailWord_4885282 prefixEnd_4885282 836165932919353515136001 := by
  unfold tailWord_4885282
  simp only [CollatzResearch.WordTrace]
  refine ⟨44545218171866282146382525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118787248458310085723686733 44545218171866282146382525)
  ·
    refine ⟨16704456814449855804893447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44545218171866282146382525 16704456814449855804893447)
    ·
      refine ⟨25056685221674783707340171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16704456814449855804893447 25056685221674783707340171)
      ·
        refine ⟨37585027832512175561010257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25056685221674783707340171 37585027832512175561010257)
        ·
          refine ⟨28188770874384131670757693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37585027832512175561010257 28188770874384131670757693)
          ·
            refine ⟨10570789077894049376534135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28188770874384131670757693 10570789077894049376534135)
            ·
              refine ⟨15856183616841074064801203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10570789077894049376534135 15856183616841074064801203)
              ·
                refine ⟨23784275425261611097201805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15856183616841074064801203 23784275425261611097201805)
                ·
                  refine ⟨8919103284473104161450677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23784275425261611097201805 8919103284473104161450677)
                  ·
                    refine ⟨836165932919353515136001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8919103284473104161450677 836165932919353515136001)
                    ·
                      rfl

theorem cell23_4885282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_4885282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885282 prefixEnd_4885282 := by exact prefixLift 4885282
  have htrace : WordTrace (prefixWord ++ tailWord_4885282) baseStart_4885282 baseEnd_4885282 := by
    simpa [prefixWord, tailWord_4885282, baseEnd_4885282] using wordTrace_append hprefix tailTrace_4885282
  have hstable : (prefixWord ++ tailWord_4885282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885282).length < 2 ^ (prefixWord ++ tailWord_4885282).sum := by decide
  have hdescent : baseEnd_4885282 < baseStart_4885282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885299 : List Nat := [1, 1, 1, 2, 6, 2, 3, 1, 1, 5]
def baseStart_4885299 : Nat := 118140960795 + 4885299 * 2 ^ 59
def prefixEnd_4885299 : Nat := 4983230072969 + 3 ^ 40 * 4885299 * 2
def baseEnd_4885299 : Nat := 836168842643062326298475

theorem tailTrace_4885299 : CollatzResearch.WordTrace tailWord_4885299 prefixEnd_4885299 836168842643062326298475 := by
  unfold tailWord_4885299
  simp only [CollatzResearch.WordTrace]
  refine ⟨178181492728403540488898951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118787661818935693659265967 178181492728403540488898951)
  ·
    refine ⟨267272239092605310733348427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178181492728403540488898951 267272239092605310733348427)
    ·
      refine ⟨400908358638907966100022641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267272239092605310733348427 400908358638907966100022641)
      ·
        refine ⟨300681268979180974575016981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400908358638907966100022641 300681268979180974575016981)
        ·
          refine ⟨14094434483399108183203921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 300681268979180974575016981 14094434483399108183203921)
          ·
            refine ⟨10570825862549331137402941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14094434483399108183203921 10570825862549331137402941)
            ·
              refine ⟨3964059698455999176526103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10570825862549331137402941 3964059698455999176526103)
              ·
                refine ⟨5946089547683998764789155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3964059698455999176526103 5946089547683998764789155)
                ·
                  refine ⟨8919134321525998147183733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5946089547683998764789155 8919134321525998147183733)
                  ·
                    refine ⟨836168842643062326298475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8919134321525998147183733 836168842643062326298475)
                    ·
                      rfl

theorem cell23_4885299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 1, 5].length) (baseStart_4885299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885299 prefixEnd_4885299 := by exact prefixLift 4885299
  have htrace : WordTrace (prefixWord ++ tailWord_4885299) baseStart_4885299 baseEnd_4885299 := by
    simpa [prefixWord, tailWord_4885299, baseEnd_4885299] using wordTrace_append hprefix tailTrace_4885299
  have hstable : (prefixWord ++ tailWord_4885299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885299).length < 2 ^ (prefixWord ++ tailWord_4885299).sum := by decide
  have hdescent : baseEnd_4885299 < baseStart_4885299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885315 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 4]
def baseStart_4885315 : Nat := 118140960795 + 4885315 * 2 ^ 59
def prefixEnd_4885315 : Nat := 4983230072969 + 3 ^ 40 * 4885315 * 2
def baseEnd_4885315 : Nat := 2508514743619658916295351

theorem tailTrace_4885315 : CollatzResearch.WordTrace tailWord_4885315 prefixEnd_4885315 2508514743619658916295351 := by
  unfold tailWord_4885315
  simp only [CollatzResearch.WordTrace]
  refine ⟨178182076296345575221481399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118788050864230383480987599 178182076296345575221481399)
  ·
    refine ⟨267273114444518362832222099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178182076296345575221481399 267273114444518362832222099)
    ·
      refine ⟨400909671666777544248333149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267273114444518362832222099 400909671666777544248333149)
      ·
        refine ⟨150341126875041579093124931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 400909671666777544248333149 150341126875041579093124931)
        ·
          refine ⟨225511690312562368639687397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150341126875041579093124931 225511690312562368639687397)
          ·
            refine ⟨42283441933605444119941387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 225511690312562368639687397 42283441933605444119941387)
            ·
              refine ⟨63425162900408166179912081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42283441933605444119941387 63425162900408166179912081)
              ·
                refine ⟨47568872175306124634934061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63425162900408166179912081 47568872175306124634934061)
                ·
                  refine ⟨17838327065739796738100273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47568872175306124634934061 17838327065739796738100273)
                  ·
                    refine ⟨13378745299304847553575205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17838327065739796738100273 13378745299304847553575205)
                    ·
                      refine ⟨2508514743619658916295351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13378745299304847553575205 2508514743619658916295351)
                      ·
                        rfl

theorem cell23_4885315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_4885315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885315 prefixEnd_4885315 := by exact prefixLift 4885315
  have htrace : WordTrace (prefixWord ++ tailWord_4885315) baseStart_4885315 baseEnd_4885315 := by
    simpa [prefixWord, tailWord_4885315, baseEnd_4885315] using wordTrace_append hprefix tailTrace_4885315
  have hstable : (prefixWord ++ tailWord_4885315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885315).length < 2 ^ (prefixWord ++ tailWord_4885315).sum := by decide
  have hdescent : baseEnd_4885315 < baseStart_4885315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885319 : List Nat := [1, 1, 4, 1, 2, 1, 1, 5, 3, 2, 2]
def baseStart_4885319 : Nat := 118140960795 + 4885319 * 2 ^ 59
def prefixEnd_4885319 : Nat := 4983230072969 + 3 ^ 40 * 4885319 * 2
def baseEnd_4885319 : Nat := 2508516797542276900645333

theorem tailTrace_4885319 : CollatzResearch.WordTrace tailWord_4885319 prefixEnd_4885319 2508516797542276900645333 := by
  unfold tailWord_4885319
  simp only [CollatzResearch.WordTrace]
  refine ⟨178182222188331083904627011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118788148125554055936418007 178182222188331083904627011)
  ·
    refine ⟨267273333282496625856940517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178182222188331083904627011 267273333282496625856940517)
    ·
      refine ⟨50113749990468117348176347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 267273333282496625856940517 50113749990468117348176347)
      ·
        refine ⟨75170624985702176022264521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50113749990468117348176347 75170624985702176022264521)
        ·
          refine ⟨56377968739276632016698391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75170624985702176022264521 56377968739276632016698391)
          ·
            refine ⟨84566953108914948025047587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56377968739276632016698391 84566953108914948025047587)
            ·
              refine ⟨126850429663372422037571381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84566953108914948025047587 126850429663372422037571381)
              ·
                refine ⟨11892227780941164566022317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126850429663372422037571381 11892227780941164566022317)
                ·
                  refine ⟨4459585417852936712258369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11892227780941164566022317 4459585417852936712258369)
                  ·
                    refine ⟨3344689063389702534193777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4459585417852936712258369 3344689063389702534193777)
                    ·
                      refine ⟨2508516797542276900645333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3344689063389702534193777 2508516797542276900645333)
                      ·
                        rfl

theorem cell23_4885319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_4885319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885319 prefixEnd_4885319 := by exact prefixLift 4885319
  have htrace : WordTrace (prefixWord ++ tailWord_4885319) baseStart_4885319 baseEnd_4885319 := by
    simpa [prefixWord, tailWord_4885319, baseEnd_4885319] using wordTrace_append hprefix tailTrace_4885319
  have hstable : (prefixWord ++ tailWord_4885319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885319).length < 2 ^ (prefixWord ++ tailWord_4885319).sum := by decide
  have hdescent : baseEnd_4885319 < baseStart_4885319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885369 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 4, 1, 3]
def baseStart_4885369 : Nat := 118140960795 + 4885369 * 2 ^ 59
def prefixEnd_4885369 : Nat := 4983230072969 + 3 ^ 40 * 4885369 * 2
def baseEnd_4885369 : Nat := 2508542471575001705020103

theorem tailTrace_4885369 : CollatzResearch.WordTrace tailWord_4885369 prefixEnd_4885369 2508542471575001705020103 := by
  unfold tailWord_4885369
  simp only [CollatzResearch.WordTrace]
  refine ⟨178184045838149942443947161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118789363892099961629298107 178184045838149942443947161)
  ·
    refine ⟨133638034378612456832960371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178184045838149942443947161 133638034378612456832960371)
    ·
      refine ⟨200457051567918685249440557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133638034378612456832960371 200457051567918685249440557)
      ·
        refine ⟨75171394337969506968540209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200457051567918685249440557 75171394337969506968540209)
        ·
          refine ⟨56378545753477130226405157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75171394337969506968540209 56378545753477130226405157)
          ·
            refine ⟨10570977328776961917450967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56378545753477130226405157 10570977328776961917450967)
            ·
              refine ⟨15856465993165442876176451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10570977328776961917450967 15856465993165442876176451)
              ·
                refine ⟨23784698989748164314264677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15856465993165442876176451 23784698989748164314264677)
                ·
                  refine ⟨4459631060577780808924627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23784698989748164314264677 4459631060577780808924627)
                  ·
                    refine ⟨6689446590866671213386941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4459631060577780808924627 6689446590866671213386941)
                    ·
                      refine ⟨2508542471575001705020103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6689446590866671213386941 2508542471575001705020103)
                      ·
                        rfl

theorem cell23_4885369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_4885369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885369 prefixEnd_4885369 := by exact prefixLift 4885369
  have htrace : WordTrace (prefixWord ++ tailWord_4885369) baseStart_4885369 baseEnd_4885369 := by
    simpa [prefixWord, tailWord_4885369, baseEnd_4885369] using wordTrace_append hprefix tailTrace_4885369
  have hstable : (prefixWord ++ tailWord_4885369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885369).length < 2 ^ (prefixWord ++ tailWord_4885369).sum := by decide
  have hdescent : baseEnd_4885369 < baseStart_4885369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885375 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 4]
def baseStart_4885375 : Nat := 118140960795 + 4885375 * 2 ^ 59
def prefixEnd_4885375 : Nat := 4983230072969 + 3 ^ 40 * 4885375 * 2
def baseEnd_4885375 : Nat := 2508545552458928681545075

theorem tailTrace_4885375 : CollatzResearch.WordTrace tailWord_4885375 prefixEnd_4885375 2508545552458928681545075 := by
  unfold tailWord_4885375
  simp only [CollatzResearch.WordTrace]
  refine ⟨178184264676128205468665579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118789509784085470312443719 178184264676128205468665579)
  ·
    refine ⟨267276397014192308202998369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178184264676128205468665579 267276397014192308202998369)
    ·
      refine ⟨200457297760644231152248777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267276397014192308202998369 200457297760644231152248777)
      ·
        refine ⟨150342973320483173364186583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200457297760644231152248777 150342973320483173364186583)
        ·
          refine ⟨225514459980724760046279875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150342973320483173364186583 225514459980724760046279875)
          ·
            refine ⟨338271689971087140069419813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225514459980724760046279875 338271689971087140069419813)
            ·
              refine ⟨63425941869578838763016215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 338271689971087140069419813 63425941869578838763016215)
              ·
                refine ⟨95138912804368258144524323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63425941869578838763016215 95138912804368258144524323)
                ·
                  refine ⟨142708369206552387216786485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95138912804368258144524323 142708369206552387216786485)
                  ·
                    refine ⟨13378909613114286301573733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 142708369206552387216786485 13378909613114286301573733)
                    ·
                      refine ⟨2508545552458928681545075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13378909613114286301573733 2508545552458928681545075)
                      ·
                        rfl

theorem cell23_4885375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_4885375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885375 prefixEnd_4885375 := by exact prefixLift 4885375
  have htrace : WordTrace (prefixWord ++ tailWord_4885375) baseStart_4885375 baseEnd_4885375 := by
    simpa [prefixWord, tailWord_4885375, baseEnd_4885375] using wordTrace_append hprefix tailTrace_4885375
  have hstable : (prefixWord ++ tailWord_4885375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885375).length < 2 ^ (prefixWord ++ tailWord_4885375).sum := by decide
  have hdescent : baseEnd_4885375 < baseStart_4885375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885386 : List Nat := [3, 1, 2, 4, 1, 3, 1, 1, 1, 3, 3]
def baseStart_4885386 : Nat := 118140960795 + 4885386 * 2 ^ 59
def prefixEnd_4885386 : Nat := 4983230072969 + 3 ^ 40 * 4885386 * 2
def baseEnd_4885386 : Nat := 2508551200746128138507525

theorem tailTrace_4885386 : CollatzResearch.WordTrace tailWord_4885386 prefixEnd_4885386 2508551200746128138507525 := by
  unfold tailWord_4885386
  simp only [CollatzResearch.WordTrace]
  refine ⟨44546166469772088586829003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118789777252725569564877341 44546166469772088586829003)
  ·
    refine ⟨66819249704658132880243505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44546166469772088586829003 66819249704658132880243505)
    ·
      refine ⟨50114437278493599660182629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66819249704658132880243505 50114437278493599660182629)
      ·
        refine ⟨9396456989717549936284243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50114437278493599660182629 9396456989717549936284243)
        ·
          refine ⟨14094685484576324904426365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9396456989717549936284243 14094685484576324904426365)
          ·
            refine ⟨5285507056716121839159887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14094685484576324904426365 5285507056716121839159887)
            ·
              refine ⟨7928260585074182758739831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5285507056716121839159887 7928260585074182758739831)
              ·
                refine ⟨11892390877611274138109747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7928260585074182758739831 11892390877611274138109747)
                ·
                  refine ⟨17838586316416911207164621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11892390877611274138109747 17838586316416911207164621)
                  ·
                    refine ⟨6689469868656341702686733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17838586316416911207164621 6689469868656341702686733)
                    ·
                      refine ⟨2508551200746128138507525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6689469868656341702686733 2508551200746128138507525)
                      ·
                        rfl

theorem cell23_4885386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_4885386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885386 prefixEnd_4885386 := by exact prefixLift 4885386
  have htrace : WordTrace (prefixWord ++ tailWord_4885386) baseStart_4885386 baseEnd_4885386 := by
    simpa [prefixWord, tailWord_4885386, baseEnd_4885386] using wordTrace_append hprefix tailTrace_4885386
  have hstable : (prefixWord ++ tailWord_4885386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885386).length < 2 ^ (prefixWord ++ tailWord_4885386).sum := by decide
  have hdescent : baseEnd_4885386 < baseStart_4885386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885412 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 2, 1, 5]
def baseStart_4885412 : Nat := 118140960795 + 4885412 * 2 ^ 59
def prefixEnd_4885412 : Nat := 4983230072969 + 3 ^ 40 * 4885412 * 2
def baseEnd_4885412 : Nat := 2508564551243145036782405

theorem tailTrace_4885412 : CollatzResearch.WordTrace tailWord_4885412 prefixEnd_4885412 2508564551243145036782405 := by
  unfold tailWord_4885412
  simp only [CollatzResearch.WordTrace]
  refine ⟨89092807088497080393881245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118790409451329440525174993 89092807088497080393881245)
  ·
    refine ⟨33409802658186405147705467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89092807088497080393881245 33409802658186405147705467)
    ·
      refine ⟨50114703987279607721558201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33409802658186405147705467 50114703987279607721558201)
      ·
        refine ⟨37586027990459705791168651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50114703987279607721558201 37586027990459705791168651)
        ·
          refine ⟨56379041985689558686752977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37586027990459705791168651 56379041985689558686752977)
          ·
            refine ⟨42284281489267169015064733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56379041985689558686752977 42284281489267169015064733)
            ·
              refine ⟨15856605558475188380649275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42284281489267169015064733 15856605558475188380649275)
              ·
                refine ⟨23784908337712782570973913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15856605558475188380649275 23784908337712782570973913)
                ·
                  refine ⟨17838681253284586928230435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23784908337712782570973913 17838681253284586928230435)
                  ·
                    refine ⟨26758021879926880392345653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17838681253284586928230435 26758021879926880392345653)
                    ·
                      refine ⟨2508564551243145036782405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26758021879926880392345653 2508564551243145036782405)
                      ·
                        rfl

theorem cell23_4885412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_4885412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885412 prefixEnd_4885412 := by exact prefixLift 4885412
  have htrace : WordTrace (prefixWord ++ tailWord_4885412) baseStart_4885412 baseEnd_4885412 := by
    simpa [prefixWord, tailWord_4885412, baseEnd_4885412] using wordTrace_append hprefix tailTrace_4885412
  have hstable : (prefixWord ++ tailWord_4885412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885412).length < 2 ^ (prefixWord ++ tailWord_4885412).sum := by decide
  have hdescent : baseEnd_4885412 < baseStart_4885412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885432 : List Nat := [2, 1, 2, 1, 2, 4, 3, 1, 7]
def baseStart_4885432 : Nat := 118140960795 + 4885432 * 2 ^ 59
def prefixEnd_4885432 : Nat := 4983230072969 + 3 ^ 40 * 4885432 * 2
def baseEnd_4885432 : Nat := 278730535650692773170257

theorem tailTrace_4885432 : CollatzResearch.WordTrace tailWord_4885432 prefixEnd_4885432 278730535650692773170257 := by
  unfold tailWord_4885432
  simp only [CollatzResearch.WordTrace]
  refine ⟨89093171818460852101745275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118790895757947802802327033 89093171818460852101745275)
  ·
    refine ⟨133639757727691278152617913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89093171818460852101745275 133639757727691278152617913)
    ·
      refine ⟨100229818295768458614463435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133639757727691278152617913 100229818295768458614463435)
      ·
        refine ⟨150344727443652687921695153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100229818295768458614463435 150344727443652687921695153)
        ·
          refine ⟨112758545582739515941271365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150344727443652687921695153 112758545582739515941271365)
          ·
            refine ⟨21142227296763659238988381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112758545582739515941271365 21142227296763659238988381)
            ·
              refine ⟨7928335236286372214620643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21142227296763659238988381 7928335236286372214620643)
              ·
                refine ⟨11892502854429558321930965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7928335236286372214620643 11892502854429558321930965)
                ·
                  refine ⟨278730535650692773170257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11892502854429558321930965 278730535650692773170257)
                  ·
                    rfl

theorem cell23_4885432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 7].length) (baseStart_4885432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885432 prefixEnd_4885432 := by exact prefixLift 4885432
  have htrace : WordTrace (prefixWord ++ tailWord_4885432) baseStart_4885432 baseEnd_4885432 := by
    simpa [prefixWord, tailWord_4885432, baseEnd_4885432] using wordTrace_append hprefix tailTrace_4885432
  have hstable : (prefixWord ++ tailWord_4885432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885432).length < 2 ^ (prefixWord ++ tailWord_4885432).sum := by decide
  have hdescent : baseEnd_4885432 < baseStart_4885432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885479 : List Nat := [1, 1, 5, 2, 2, 1, 2, 2, 2, 5]
def baseStart_4885479 : Nat := 118140960795 + 4885479 * 2 ^ 59
def prefixEnd_4885479 : Nat := 4983230072969 + 3 ^ 40 * 4885479 * 2
def baseEnd_4885479 : Nat := 836199651482332091548199

theorem tailTrace_4885479 : CollatzResearch.WordTrace tailWord_4885479 prefixEnd_4885479 836199651482332091548199 := by
  unfold tailWord_4885479
  simp only [CollatzResearch.WordTrace]
  refine ⟨178188057867751431230451491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118792038578500954153634327 178188057867751431230451491)
  ·
    refine ⟨267282086801627146845677237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178188057867751431230451491 267282086801627146845677237)
    ·
      refine ⟨25057695637652545016782241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 267282086801627146845677237 25057695637652545016782241)
      ·
        refine ⟨18793271728239408762586681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25057695637652545016782241 18793271728239408762586681)
        ·
          refine ⟨14094953796179556571940011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18793271728239408762586681 14094953796179556571940011)
          ·
            refine ⟨21142430694269334857910017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14094953796179556571940011 21142430694269334857910017)
            ·
              refine ⟨15856823020702001143432513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21142430694269334857910017 15856823020702001143432513)
              ·
                refine ⟨11892617265526500857574385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15856823020702001143432513 11892617265526500857574385)
                ·
                  refine ⟨8919462949144875643180789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11892617265526500857574385 8919462949144875643180789)
                  ·
                    refine ⟨836199651482332091548199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8919462949144875643180789 836199651482332091548199)
                    ·
                      rfl

theorem cell23_4885479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_4885479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885479 prefixEnd_4885479 := by exact prefixLift 4885479
  have htrace : WordTrace (prefixWord ++ tailWord_4885479) baseStart_4885479 baseEnd_4885479 := by
    simpa [prefixWord, tailWord_4885479, baseEnd_4885479] using wordTrace_append hprefix tailTrace_4885479
  have hstable : (prefixWord ++ tailWord_4885479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885479).length < 2 ^ (prefixWord ++ tailWord_4885479).sum := by decide
  have hdescent : baseEnd_4885479 < baseStart_4885479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885493 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_4885493 : Nat := 118140960795 + 4885493 * 2 ^ 59
def prefixEnd_4885493 : Nat := 4983230072969 + 3 ^ 40 * 4885493 * 2
def baseEnd_4885493 : Nat := 2508606143176159219869533

theorem tailTrace_4885493 : CollatzResearch.WordTrace tailWord_4885493 prefixEnd_4885493 2508606143176159219869533 := by
  unfold tailWord_4885493
  simp only [CollatzResearch.WordTrace]
  refine ⟨178188568489700711621461133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118792378993133807747640755 178188568489700711621461133)
  ·
    refine ⟨66820713183637766858047925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178188568489700711621461133 66820713183637766858047925)
    ·
      refine ⟨6264441860966040642941993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66820713183637766858047925 6264441860966040642941993)
      ·
        refine ⟨4698331395724530482206495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6264441860966040642941993 4698331395724530482206495)
        ·
          refine ⟨7047497093586795723309743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4698331395724530482206495 7047497093586795723309743)
          ·
            refine ⟨10571245640380193584964615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7047497093586795723309743 10571245640380193584964615)
            ·
              refine ⟨15856868460570290377446923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10571245640380193584964615 15856868460570290377446923)
              ·
                refine ⟨23785302690855435566170385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15856868460570290377446923 23785302690855435566170385)
                ·
                  refine ⟨17838977018141576674627789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23785302690855435566170385 17838977018141576674627789)
                  ·
                    refine ⟨6689616381803091252985421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17838977018141576674627789 6689616381803091252985421)
                    ·
                      refine ⟨2508606143176159219869533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6689616381803091252985421 2508606143176159219869533)
                      ·
                        rfl

theorem cell23_4885493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_4885493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885493 prefixEnd_4885493 := by exact prefixLift 4885493
  have htrace : WordTrace (prefixWord ++ tailWord_4885493) baseStart_4885493 baseEnd_4885493 := by
    simpa [prefixWord, tailWord_4885493, baseEnd_4885493] using wordTrace_append hprefix tailTrace_4885493
  have hstable : (prefixWord ++ tailWord_4885493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885493).length < 2 ^ (prefixWord ++ tailWord_4885493).sum := by decide
  have hdescent : baseEnd_4885493 < baseStart_4885493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885509 : List Nat := [1, 3, 1, 1, 2, 3, 3, 2, 3, 4]
def baseStart_4885509 : Nat := 118140960795 + 4885509 * 2 ^ 59
def prefixEnd_4885509 : Nat := 4983230072969 + 3 ^ 40 * 4885509 * 2
def baseEnd_4885509 : Nat := 836204786288877052423153

theorem tailTrace_4885509 : CollatzResearch.WordTrace tailWord_4885509 prefixEnd_4885509 836204786288877052423153 := by
  unfold tailWord_4885509
  simp only [CollatzResearch.WordTrace]
  refine ⟨178189152057642746354043581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118792768038428497569362387 178189152057642746354043581)
  ·
    refine ⟨66820932021616029882766343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178189152057642746354043581 66820932021616029882766343)
    ·
      refine ⟨100231398032424044824149515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66820932021616029882766343 100231398032424044824149515)
      ·
        refine ⟨150347097048636067236224273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100231398032424044824149515 150347097048636067236224273)
        ·
          refine ⟨112760322786477050427168205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150347097048636067236224273 112760322786477050427168205)
          ·
            refine ⟨42285121044928893910188077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112760322786477050427168205 42285121044928893910188077)
            ·
              refine ⟨15856920391848335216320529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42285121044928893910188077 15856920391848335216320529)
              ·
                refine ⟨11892690293886251412240397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15856920391848335216320529 11892690293886251412240397)
                ·
                  refine ⟨4459758860207344279590149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11892690293886251412240397 4459758860207344279590149)
                  ·
                    refine ⟨836204786288877052423153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4459758860207344279590149 836204786288877052423153)
                    ·
                      rfl

theorem cell23_4885509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 4].length) (baseStart_4885509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885509 prefixEnd_4885509 := by exact prefixLift 4885509
  have htrace : WordTrace (prefixWord ++ tailWord_4885509) baseStart_4885509 baseEnd_4885509 := by
    simpa [prefixWord, tailWord_4885509, baseEnd_4885509] using wordTrace_append hprefix tailTrace_4885509
  have hstable : (prefixWord ++ tailWord_4885509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885509).length < 2 ^ (prefixWord ++ tailWord_4885509).sum := by decide
  have hdescent : baseEnd_4885509 < baseStart_4885509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885516 : List Nat := [2, 2, 1, 2, 3, 4, 1, 1, 2, 1, 4]
def baseStart_4885516 : Nat := 118140960795 + 4885516 * 2 ^ 59
def prefixEnd_4885516 : Nat := 4983230072969 + 3 ^ 40 * 4885516 * 2
def baseEnd_4885516 : Nat := 2508617953231212629881927

theorem tailTrace_4885516 : CollatzResearch.WordTrace tailWord_4885516 prefixEnd_4885516 2508617953231212629881927 := by
  unfold tailWord_4885516
  simp only [CollatzResearch.WordTrace]
  refine ⟨89094703684308693274774201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118792938245744924366365601 89094703684308693274774201)
  ·
    refine ⟨66821027763231519956080651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89094703684308693274774201 66821027763231519956080651)
    ·
      refine ⟨100231541644847279934120977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66821027763231519956080651 100231541644847279934120977)
      ·
        refine ⟨75173656233635459950590733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100231541644847279934120977 75173656233635459950590733)
        ·
          refine ⟨28190121087613297481471525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75173656233635459950590733 28190121087613297481471525)
          ·
            refine ⟨5285647703927493277775911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28190121087613297481471525 5285647703927493277775911)
            ·
              refine ⟨7928471555891239916663867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5285647703927493277775911 7928471555891239916663867)
              ·
                refine ⟨11892707333836859874995801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7928471555891239916663867 11892707333836859874995801)
                ·
                  refine ⟨8919530500377644906246851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11892707333836859874995801 8919530500377644906246851)
                  ·
                    refine ⟨13379295750566467359370277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8919530500377644906246851 13379295750566467359370277)
                    ·
                      refine ⟨2508617953231212629881927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13379295750566467359370277 2508617953231212629881927)
                      ·
                        rfl

theorem cell23_4885516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_4885516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885516 prefixEnd_4885516 := by exact prefixLift 4885516
  have htrace : WordTrace (prefixWord ++ tailWord_4885516) baseStart_4885516 baseEnd_4885516 := by
    simpa [prefixWord, tailWord_4885516, baseEnd_4885516] using wordTrace_append hprefix tailTrace_4885516
  have hstable : (prefixWord ++ tailWord_4885516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885516).length < 2 ^ (prefixWord ++ tailWord_4885516).sum := by decide
  have hdescent : baseEnd_4885516 < baseStart_4885516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885539 : List Nat := [1, 1, 1, 4, 3, 2, 3, 2, 6]
def baseStart_4885539 : Nat := 118140960795 + 4885539 * 2 ^ 59
def prefixEnd_4885539 : Nat := 4983230072969 + 3 ^ 40 * 4885539 * 2
def baseEnd_4885539 : Nat := 278736640365140671099369

theorem tailTrace_4885539 : CollatzResearch.WordTrace tailWord_4885539 prefixEnd_4885539 278736640365140671099369 := by
  unfold tailWord_4885539
  simp only [CollatzResearch.WordTrace]
  refine ⟨178190246247534061477635671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118793497498356040985090447 178190246247534061477635671)
  ·
    refine ⟨267285369371301092216453507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178190246247534061477635671 267285369371301092216453507)
    ·
      refine ⟨400928054056951638324680261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267285369371301092216453507 400928054056951638324680261)
      ·
        refine ⟨75174010135678432185877549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 400928054056951638324680261 75174010135678432185877549)
        ·
          refine ⟨28190253800879412069704081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75174010135678432185877549 28190253800879412069704081)
          ·
            refine ⟨21142690350659559052278061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28190253800879412069704081 21142690350659559052278061)
            ·
              refine ⟨7928508881497334644604273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21142690350659559052278061 7928508881497334644604273)
              ·
                refine ⟨5946381661123000983453205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7928508881497334644604273 5946381661123000983453205)
                ·
                  refine ⟨278736640365140671099369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5946381661123000983453205 278736640365140671099369)
                  ·
                    rfl

theorem cell23_4885539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 6].length) (baseStart_4885539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885539 prefixEnd_4885539 := by exact prefixLift 4885539
  have htrace : WordTrace (prefixWord ++ tailWord_4885539) baseStart_4885539 baseEnd_4885539 := by
    simpa [prefixWord, tailWord_4885539, baseEnd_4885539] using wordTrace_append hprefix tailTrace_4885539
  have hstable : (prefixWord ++ tailWord_4885539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885539).length < 2 ^ (prefixWord ++ tailWord_4885539).sum := by decide
  have hdescent : baseEnd_4885539 < baseStart_4885539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885543 : List Nat := [1, 1, 7, 1, 1, 2, 2, 1, 3, 4]
def baseStart_4885543 : Nat := 118140960795 + 4885543 * 2 ^ 59
def prefixEnd_4885543 : Nat := 4983230072969 + 3 ^ 40 * 4885543 * 2
def baseEnd_4885543 : Nat := 836210605736294674748101

theorem tailTrace_4885543 : CollatzResearch.WordTrace tailWord_4885543 prefixEnd_4885543 836210605736294674748101 := by
  unfold tailWord_4885543
  simp only [CollatzResearch.WordTrace]
  refine ⟨178190392139519570160781283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118793594759679713440520855 178190392139519570160781283)
  ·
    refine ⟨267285588209279355241171925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178190392139519570160781283 267285588209279355241171925)
    ·
      refine ⟨6264505973654984888464967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 267285588209279355241171925 6264505973654984888464967)
      ·
        refine ⟨9396758960482477332697451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6264505973654984888464967 9396758960482477332697451)
        ·
          refine ⟨14095138440723715999046177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9396758960482477332697451 14095138440723715999046177)
          ·
            refine ⟨10571353830542786999284633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14095138440723715999046177 10571353830542786999284633)
            ·
              refine ⟨7928515372907090249463475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10571353830542786999284633 7928515372907090249463475)
              ·
                refine ⟨11892773059360635374195213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7928515372907090249463475 11892773059360635374195213)
                ·
                  refine ⟨4459789897260238265323205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11892773059360635374195213 4459789897260238265323205)
                  ·
                    refine ⟨836210605736294674748101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4459789897260238265323205 836210605736294674748101)
                    ·
                      rfl

theorem cell23_4885543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_4885543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885543 prefixEnd_4885543 := by exact prefixLift 4885543
  have htrace : WordTrace (prefixWord ++ tailWord_4885543) baseStart_4885543 baseEnd_4885543 := by
    simpa [prefixWord, tailWord_4885543, baseEnd_4885543] using wordTrace_append hprefix tailTrace_4885543
  have hstable : (prefixWord ++ tailWord_4885543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885543).length < 2 ^ (prefixWord ++ tailWord_4885543).sum := by decide
  have hdescent : baseEnd_4885543 < baseStart_4885543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885562 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7]
def baseStart_4885562 : Nat := 118140960795 + 4885562 * 2 ^ 59
def prefixEnd_4885562 : Nat := 4983230072969 + 3 ^ 40 * 4885562 * 2
def baseEnd_4885562 : Nat := 2508641573341319449906715

theorem tailTrace_4885562 : CollatzResearch.WordTrace tailWord_4885562 prefixEnd_4885562 2508641573341319449906715 := by
  unfold tailWord_4885562
  simp only [CollatzResearch.WordTrace]
  refine ⟨44547771281612684101430735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118794056750967157603815293 44547771281612684101430735)
  ·
    refine ⟨66821656922419026152146103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44547771281612684101430735 66821656922419026152146103)
    ·
      refine ⟨100232485383628539228219155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66821656922419026152146103 100232485383628539228219155)
      ·
        refine ⟨150348728075442808842328733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100232485383628539228219155 150348728075442808842328733)
        ·
          refine ⟨56380773028291053315873275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150348728075442808842328733 56380773028291053315873275)
          ·
            refine ⟨84571159542436579973809913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56380773028291053315873275 84571159542436579973809913)
            ·
              refine ⟨63428369656827434980357435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84571159542436579973809913 63428369656827434980357435)
              ·
                refine ⟨95142554485241152470536153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63428369656827434980357435 95142554485241152470536153)
                ·
                  refine ⟨71356915863930864352902115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95142554485241152470536153 71356915863930864352902115)
                  ·
                    refine ⟨107035373795896296529353173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71356915863930864352902115 107035373795896296529353173)
                    ·
                      refine ⟨2508641573341319449906715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107035373795896296529353173 2508641573341319449906715)
                      ·
                        rfl

theorem cell23_4885562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_4885562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885562 prefixEnd_4885562 := by exact prefixLift 4885562
  have htrace : WordTrace (prefixWord ++ tailWord_4885562) baseStart_4885562 baseEnd_4885562 := by
    simpa [prefixWord, tailWord_4885562, baseEnd_4885562] using wordTrace_append hprefix tailTrace_4885562
  have hstable : (prefixWord ++ tailWord_4885562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885562).length < 2 ^ (prefixWord ++ tailWord_4885562).sum := by decide
  have hdescent : baseEnd_4885562 < baseStart_4885562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885576 : List Nat := [2, 1, 3, 1, 1, 1, 4, 3, 2, 3, 2]
def baseStart_4885576 : Nat := 118140960795 + 4885576 * 2 ^ 59
def prefixEnd_4885576 : Nat := 4983230072969 + 3 ^ 40 * 4885576 * 2
def baseEnd_4885576 : Nat := 2508648762070482395131651

theorem tailTrace_4885576 : CollatzResearch.WordTrace tailWord_4885576 prefixEnd_4885576 2508648762070482395131651 := by
  unfold tailWord_4885576
  simp only [CollatzResearch.WordTrace]
  refine ⟨89095797874200008398366291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118794397165600011197821721 89095797874200008398366291)
  ·
    refine ⟨133643696811300012597549437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89095797874200008398366291 133643696811300012597549437)
    ·
      refine ⟨50116386304237504724081039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133643696811300012597549437 50116386304237504724081039)
      ·
        refine ⟨75174579456356257086121559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50116386304237504724081039 75174579456356257086121559)
        ·
          refine ⟨112761869184534385629182339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75174579456356257086121559 112761869184534385629182339)
          ·
            refine ⟨169142803776801578443773509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112761869184534385629182339 169142803776801578443773509)
            ·
              refine ⟨31714275708150295958207533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169142803776801578443773509 31714275708150295958207533)
              ·
                refine ⟨11892853390556360984327825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31714275708150295958207533 11892853390556360984327825)
                ·
                  refine ⟨8919640042917270738245869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11892853390556360984327825 8919640042917270738245869)
                  ·
                    refine ⟨3344865016093976526842201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8919640042917270738245869 3344865016093976526842201)
                    ·
                      refine ⟨2508648762070482395131651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3344865016093976526842201 2508648762070482395131651)
                      ·
                        rfl

theorem cell23_4885576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 2, 3, 2].length) (baseStart_4885576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885576 prefixEnd_4885576 := by exact prefixLift 4885576
  have htrace : WordTrace (prefixWord ++ tailWord_4885576) baseStart_4885576 baseEnd_4885576 := by
    simpa [prefixWord, tailWord_4885576, baseEnd_4885576] using wordTrace_append hprefix tailTrace_4885576
  have hstable : (prefixWord ++ tailWord_4885576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885576).length < 2 ^ (prefixWord ++ tailWord_4885576).sum := by decide
  have hdescent : baseEnd_4885576 < baseStart_4885576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885586 : List Nat := [3, 2, 2, 1, 3, 1, 2, 3, 1, 5]
def baseStart_4885586 : Nat := 118140960795 + 4885586 * 2 ^ 59
def prefixEnd_4885586 : Nat := 4983230072969 + 3 ^ 40 * 4885586 * 2
def baseEnd_4885586 : Nat := 836217965625675785335535

theorem tailTrace_4885586 : CollatzResearch.WordTrace tailWord_4885586 prefixEnd_4885586 836217965625675785335535 := by
  unfold tailWord_4885586
  simp only [CollatzResearch.WordTrace]
  refine ⟨44547990119590947126149153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118794640318909192336397741 44547990119590947126149153)
  ·
    refine ⟨33410992589693210344611865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44547990119590947126149153 33410992589693210344611865)
    ·
      refine ⟨25058244442269907758458899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33410992589693210344611865 25058244442269907758458899)
      ·
        refine ⟨37587366663404861637688349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25058244442269907758458899 37587366663404861637688349)
        ·
          refine ⟨14095262498776823114133131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37587366663404861637688349 14095262498776823114133131)
          ·
            refine ⟨21142893748165234671199697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14095262498776823114133131 21142893748165234671199697)
            ·
              refine ⟨15857170311123926003399773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21142893748165234671199697 15857170311123926003399773)
              ·
                refine ⟨5946438866671472251274915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15857170311123926003399773 5946438866671472251274915)
                ·
                  refine ⟨8919658300007208376912373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5946438866671472251274915 8919658300007208376912373)
                  ·
                    refine ⟨836217965625675785335535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8919658300007208376912373 836217965625675785335535)
                    ·
                      rfl

theorem cell23_4885586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_4885586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885586 prefixEnd_4885586 := by exact prefixLift 4885586
  have htrace : WordTrace (prefixWord ++ tailWord_4885586) baseStart_4885586 baseEnd_4885586 := by
    simpa [prefixWord, tailWord_4885586, baseEnd_4885586] using wordTrace_append hprefix tailTrace_4885586
  have hstable : (prefixWord ++ tailWord_4885586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885586).length < 2 ^ (prefixWord ++ tailWord_4885586).sum := by decide
  have hdescent : baseEnd_4885586 < baseStart_4885586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885599 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 4, 4]
def baseStart_4885599 : Nat := 118140960795 + 4885599 * 2 ^ 59
def prefixEnd_4885599 : Nat := 4983230072969 + 3 ^ 40 * 4885599 * 2
def baseEnd_4885599 : Nat := 836220190708511935048015

theorem tailTrace_4885599 : CollatzResearch.WordTrace tailWord_4885599 prefixEnd_4885599 836220190708511935048015 := by
  unfold tailWord_4885599
  simp only [CollatzResearch.WordTrace]
  refine ⟨178192434627316691724819851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118794956418211127816546567 178192434627316691724819851)
  ·
    refine ⟨267288651940975037587229777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178192434627316691724819851 267288651940975037587229777)
    ·
      refine ⟨200466488955731278190422333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267288651940975037587229777 200466488955731278190422333)
      ·
        refine ⟨75174933358399229321408375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200466488955731278190422333 75174933358399229321408375)
        ·
          refine ⟨112762400037598843982112563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75174933358399229321408375 112762400037598843982112563)
          ·
            refine ⟨169143600056398265973168845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112762400037598843982112563 169143600056398265973168845)
            ·
              refine ⟨63428850021149349739938317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169143600056398265973168845 63428850021149349739938317)
              ·
                refine ⟨23785818757931006152476869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63428850021149349739938317 23785818757931006152476869)
                ·
                  refine ⟨4459841017112063653589413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23785818757931006152476869 4459841017112063653589413)
                  ·
                    refine ⟨836220190708511935048015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4459841017112063653589413 836220190708511935048015)
                    ·
                      rfl

theorem cell23_4885599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 4].length) (baseStart_4885599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885599 prefixEnd_4885599 := by exact prefixLift 4885599
  have htrace : WordTrace (prefixWord ++ tailWord_4885599) baseStart_4885599 baseEnd_4885599 := by
    simpa [prefixWord, tailWord_4885599, baseEnd_4885599] using wordTrace_append hprefix tailTrace_4885599
  have hstable : (prefixWord ++ tailWord_4885599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885599).length < 2 ^ (prefixWord ++ tailWord_4885599).sum := by decide
  have hdescent : baseEnd_4885599 < baseStart_4885599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885600 : List Nat := [2, 1, 1, 3, 2, 2, 5, 2, 1, 1, 3]
def baseStart_4885600 : Nat := 118140960795 + 4885600 * 2 ^ 59
def prefixEnd_4885600 : Nat := 4983230072969 + 3 ^ 40 * 4885600 * 2
def baseEnd_4885600 : Nat := 2508661085606190301231541

theorem tailTrace_4885600 : CollatzResearch.WordTrace tailWord_4885600 prefixEnd_4885600 2508661085606190301231541 := by
  unfold tailWord_4885600
  simp only [CollatzResearch.WordTrace]
  refine ⟨89096235550156534447803127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118794980733542045930404169 89096235550156534447803127)
  ·
    refine ⟨133644353325234801671704691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89096235550156534447803127 133644353325234801671704691)
    ·
      refine ⟨200466529987852202507557037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133644353325234801671704691 200466529987852202507557037)
      ·
        refine ⟨75174948745444575940333889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200466529987852202507557037 75174948745444575940333889)
        ·
          refine ⟨56381211559083431955250417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75174948745444575940333889 56381211559083431955250417)
          ·
            refine ⟨42285908669312573966437813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56381211559083431955250417 42285908669312573966437813)
            ·
              refine ⟨3964303937748053809353545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42285908669312573966437813 3964303937748053809353545)
              ·
                refine ⟨2973227953311040357015159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3964303937748053809353545 2973227953311040357015159)
                ·
                  refine ⟨4459841929966560535522739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2973227953311040357015159 4459841929966560535522739)
                  ·
                    refine ⟨6689762894949840803284109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4459841929966560535522739 6689762894949840803284109)
                    ·
                      refine ⟨2508661085606190301231541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6689762894949840803284109 2508661085606190301231541)
                      ·
                        rfl

theorem cell23_4885600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 1, 1, 3].length) (baseStart_4885600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885600 prefixEnd_4885600 := by exact prefixLift 4885600
  have htrace : WordTrace (prefixWord ++ tailWord_4885600) baseStart_4885600 baseEnd_4885600 := by
    simpa [prefixWord, tailWord_4885600, baseEnd_4885600] using wordTrace_append hprefix tailTrace_4885600
  have hstable : (prefixWord ++ tailWord_4885600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885600).length < 2 ^ (prefixWord ++ tailWord_4885600).sum := by decide
  have hdescent : baseEnd_4885600 < baseStart_4885600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885609 : List Nat := [1, 2, 1, 1, 1, 6, 2, 2, 1, 1, 5]
def baseStart_4885609 : Nat := 118140960795 + 4885609 * 2 ^ 59
def prefixEnd_4885609 : Nat := 4983230072969 + 3 ^ 40 * 4885609 * 2
def baseEnd_4885609 : Nat := 2508665706932080766018999

theorem tailTrace_4885609 : CollatzResearch.WordTrace tailWord_4885609 prefixEnd_4885609 2508665706932080766018999 := by
  unfold tailWord_4885609
  simp only [CollatzResearch.WordTrace]
  refine ⟨178192799357280463432683881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118795199571520308955122587 178192799357280463432683881)
  ·
    refine ⟨133644599517960347574512911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178192799357280463432683881 133644599517960347574512911)
    ·
      refine ⟨200466899276940521361769367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133644599517960347574512911 200466899276940521361769367)
      ·
        refine ⟨300700348915410782042654051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200466899276940521361769367 300700348915410782042654051)
        ·
          refine ⟨451050523373116173063981077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300700348915410782042654051 451050523373116173063981077)
          ·
            refine ⟨21142993283114820612374113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 451050523373116173063981077 21142993283114820612374113)
            ·
              refine ⟨15857244962336115459280585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21142993283114820612374113 15857244962336115459280585)
              ·
                refine ⟨11892933721752086594460439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15857244962336115459280585 11892933721752086594460439)
                ·
                  refine ⟨17839400582628129891690659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11892933721752086594460439 17839400582628129891690659)
                  ·
                    refine ⟨26759100873942194837535989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17839400582628129891690659 26759100873942194837535989)
                    ·
                      refine ⟨2508665706932080766018999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26759100873942194837535989 2508665706932080766018999)
                      ·
                        rfl

theorem cell23_4885609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 1, 5].length) (baseStart_4885609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885609 prefixEnd_4885609 := by exact prefixLift 4885609
  have htrace : WordTrace (prefixWord ++ tailWord_4885609) baseStart_4885609 baseEnd_4885609 := by
    simpa [prefixWord, tailWord_4885609, baseEnd_4885609] using wordTrace_append hprefix tailTrace_4885609
  have hstable : (prefixWord ++ tailWord_4885609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885609).length < 2 ^ (prefixWord ++ tailWord_4885609).sum := by decide
  have hdescent : baseEnd_4885609 < baseStart_4885609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885616 : List Nat := [2, 1, 1, 1, 5, 1, 3, 3, 2, 4]
def baseStart_4885616 : Nat := 118140960795 + 4885616 * 2 ^ 59
def prefixEnd_4885616 : Nat := 4983230072969 + 3 ^ 40 * 4885616 * 2
def baseEnd_4885616 : Nat := 836223100432220746210489

theorem tailTrace_4885616 : CollatzResearch.WordTrace tailWord_4885616 prefixEnd_4885616 836223100432220746210489 := by
  unfold tailWord_4885616
  simp only [CollatzResearch.WordTrace]
  refine ⟨89096527334127551814094351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118795369778836735752125801 89096527334127551814094351)
  ·
    refine ⟨133644791001191327721141527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89096527334127551814094351 133644791001191327721141527)
    ·
      refine ⟨200467186501786991581712291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133644791001191327721141527 200467186501786991581712291)
      ·
        refine ⟨300700779752680487372568437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200467186501786991581712291 300700779752680487372568437)
        ·
          refine ⟨28190698101813795691178291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 300700779752680487372568437 28190698101813795691178291)
          ·
            refine ⟨42286047152720693536767437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28190698101813795691178291 42286047152720693536767437)
            ·
              refine ⟨15857267682270260076287789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42286047152720693536767437 15857267682270260076287789)
              ·
                refine ⟨5946475380851347528607921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15857267682270260076287789 5946475380851347528607921)
                ·
                  refine ⟨4459856535638510646455941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5946475380851347528607921 4459856535638510646455941)
                  ·
                    refine ⟨836223100432220746210489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4459856535638510646455941 836223100432220746210489)
                    ·
                      rfl

theorem cell23_4885616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 2, 4].length) (baseStart_4885616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885616 prefixEnd_4885616 := by exact prefixLift 4885616
  have htrace : WordTrace (prefixWord ++ tailWord_4885616) baseStart_4885616 baseEnd_4885616 := by
    simpa [prefixWord, tailWord_4885616, baseEnd_4885616] using wordTrace_append hprefix tailTrace_4885616
  have hstable : (prefixWord ++ tailWord_4885616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885616).length < 2 ^ (prefixWord ++ tailWord_4885616).sum := by decide
  have hdescent : baseEnd_4885616 < baseStart_4885616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885636 : List Nat := [2, 3, 2, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_4885636 : Nat := 118140960795 + 4885636 * 2 ^ 59
def prefixEnd_4885636 : Nat := 4983230072969 + 3 ^ 40 * 4885636 * 2
def baseEnd_4885636 : Nat := 2508679570909752160381375

theorem tailTrace_4885636 : CollatzResearch.WordTrace tailWord_4885636 prefixEnd_4885636 2508679570909752160381375 := by
  unfold tailWord_4885636
  simp only [CollatzResearch.WordTrace]
  refine ⟨89096892064091323521958381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118795856085455098029277841 89096892064091323521958381)
  ·
    refine ⟨33411334524034246320734393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89096892064091323521958381 33411334524034246320734393)
    ·
      refine ⟨25058500893025684740550795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33411334524034246320734393 25058500893025684740550795)
      ·
        refine ⟨37587751339538527110826193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25058500893025684740550795 37587751339538527110826193)
        ·
          refine ⟨28190813504653895333119645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37587751339538527110826193 28190813504653895333119645)
          ·
            refine ⟨10571555064245210749919867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28190813504653895333119645 10571555064245210749919867)
            ·
              refine ⟨15857332596367816124879801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10571555064245210749919867 15857332596367816124879801)
              ·
                refine ⟨11892999447275862093659851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15857332596367816124879801 11892999447275862093659851)
                ·
                  refine ⟨17839499170913793140489777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11892999447275862093659851 17839499170913793140489777)
                  ·
                    refine ⟨13379624378185344855367333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17839499170913793140489777 13379624378185344855367333)
                    ·
                      refine ⟨2508679570909752160381375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13379624378185344855367333 2508679570909752160381375)
                      ·
                        rfl

theorem cell23_4885636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_4885636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885636 prefixEnd_4885636 := by exact prefixLift 4885636
  have htrace : WordTrace (prefixWord ++ tailWord_4885636) baseStart_4885636 baseEnd_4885636 := by
    simpa [prefixWord, tailWord_4885636, baseEnd_4885636] using wordTrace_append hprefix tailTrace_4885636
  have hstable : (prefixWord ++ tailWord_4885636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885636).length < 2 ^ (prefixWord ++ tailWord_4885636).sum := by decide
  have hdescent : baseEnd_4885636 < baseStart_4885636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885640 : List Nat := [2, 1, 3, 4, 2, 1, 3, 1, 1, 1, 4]
def baseStart_4885640 : Nat := 118140960795 + 4885640 * 2 ^ 59
def prefixEnd_4885640 : Nat := 4983230072969 + 3 ^ 40 * 4885640 * 2
def baseEnd_4885640 : Nat := 2508681624832370144731357

theorem tailTrace_4885640 : CollatzResearch.WordTrace tailWord_4885640 prefixEnd_4885640 2508681624832370144731357 := by
  unfold tailWord_4885640
  simp only [CollatzResearch.WordTrace]
  refine ⟨89096965010084077863531187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118795953346778770484708249 89096965010084077863531187)
  ·
    refine ⟨133645447515126116795296781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89096965010084077863531187 133645447515126116795296781)
    ·
      refine ⟨50117042818172293798236293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133645447515126116795296781 50117042818172293798236293)
      ·
        refine ⟨9396945528407305087169305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50117042818172293798236293 9396945528407305087169305)
        ·
          refine ⟨7047709146305478815376979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9396945528407305087169305 7047709146305478815376979)
          ·
            refine ⟨10571563719458218223065469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7047709146305478815376979 10571563719458218223065469)
            ·
              refine ⟨3964336394796831833649551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10571563719458218223065469 3964336394796831833649551)
              ·
                refine ⟨5946504592195247750474327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3964336394796831833649551 5946504592195247750474327)
                ·
                  refine ⟨8919756888292871625711491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5946504592195247750474327 8919756888292871625711491)
                  ·
                    refine ⟨13379635332439307438567237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8919756888292871625711491 13379635332439307438567237)
                    ·
                      refine ⟨2508681624832370144731357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13379635332439307438567237 2508681624832370144731357)
                      ·
                        rfl

theorem cell23_4885640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_4885640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885640 prefixEnd_4885640 := by exact prefixLift 4885640
  have htrace : WordTrace (prefixWord ++ tailWord_4885640) baseStart_4885640 baseEnd_4885640 := by
    simpa [prefixWord, tailWord_4885640, baseEnd_4885640] using wordTrace_append hprefix tailTrace_4885640
  have hstable : (prefixWord ++ tailWord_4885640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885640).length < 2 ^ (prefixWord ++ tailWord_4885640).sum := by decide
  have hdescent : baseEnd_4885640 < baseStart_4885640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885663 : List Nat := [1, 1, 2, 6, 3, 1, 1, 8]
def baseStart_4885663 : Nat := 118140960795 + 4885663 * 2 ^ 59
def prefixEnd_4885663 : Nat := 4983230072969 + 3 ^ 40 * 4885663 * 2
def baseEnd_4885663 : Nat := 92914571662497168694213

theorem tailTrace_4885663 : CollatzResearch.WordTrace tailWord_4885663 prefixEnd_4885663 92914571662497168694213 := by
  unfold tailWord_4885663
  simp only [CollatzResearch.WordTrace]
  refine ⟨178194768899084830655149643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118796512599389887103433095 178194768899084830655149643)
  ·
    refine ⟨267292153348627245982724465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178194768899084830655149643 267292153348627245982724465)
    ·
      refine ⟨200469115011470434487043349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267292153348627245982724465 200469115011470434487043349)
      ·
        refine ⟨9396989766162676616580157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 200469115011470434487043349 9396989766162676616580157)
        ·
          refine ⟨3523871162311003731217559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9396989766162676616580157 3523871162311003731217559)
          ·
            refine ⟨5285806743466505596826339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3523871162311003731217559 5285806743466505596826339)
            ·
              refine ⟨7928710115199758395239509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5285806743466505596826339 7928710115199758395239509)
              ·
                refine ⟨92914571662497168694213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7928710115199758395239509 92914571662497168694213)
                ·
                  rfl

theorem cell23_4885663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 8].length) (baseStart_4885663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885663 prefixEnd_4885663 := by exact prefixLift 4885663
  have htrace : WordTrace (prefixWord ++ tailWord_4885663) baseStart_4885663 baseEnd_4885663 := by
    simpa [prefixWord, tailWord_4885663, baseEnd_4885663] using wordTrace_append hprefix tailTrace_4885663
  have hstable : (prefixWord ++ tailWord_4885663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885663).length < 2 ^ (prefixWord ++ tailWord_4885663).sum := by decide
  have hdescent : baseEnd_4885663 < baseStart_4885663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885699 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 3]
def baseStart_4885699 : Nat := 118140960795 + 4885699 * 2 ^ 59
def prefixEnd_4885699 : Nat := 4983230072969 + 3 ^ 40 * 4885699 * 2
def baseEnd_4885699 : Nat := 2508711920190985413893585

theorem tailTrace_4885699 : CollatzResearch.WordTrace tailWord_4885699 prefixEnd_4885699 2508711920190985413893585 := by
  unfold tailWord_4885699
  simp only [CollatzResearch.WordTrace]
  refine ⟨178196081926954408803460151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118797387951302939202306767 178196081926954408803460151)
  ·
    refine ⟨267294122890431613205190227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178196081926954408803460151 267294122890431613205190227)
    ·
      refine ⟨400941184335647419807785341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267294122890431613205190227 400941184335647419807785341)
      ·
        refine ⟨150352944125867782427919503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 400941184335647419807785341 150352944125867782427919503)
        ·
          refine ⟨225529416188801673641879255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150352944125867782427919503 225529416188801673641879255)
          ·
            refine ⟨338294124283202510462818883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225529416188801673641879255 338294124283202510462818883)
            ·
              refine ⟨507441186424803765694228325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338294124283202510462818883 507441186424803765694228325)
              ·
                refine ⟨95145222454650706067667811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 507441186424803765694228325 95145222454650706067667811)
                ·
                  refine ⟨142717833681976059101501717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95145222454650706067667811 142717833681976059101501717)
                  ·
                    refine ⟨6689898453842627770382893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 142717833681976059101501717 6689898453842627770382893)
                    ·
                      refine ⟨2508711920190985413893585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6689898453842627770382893 2508711920190985413893585)
                      ·
                        rfl

theorem cell23_4885699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 3].length) (baseStart_4885699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885699 prefixEnd_4885699 := by exact prefixLift 4885699
  have htrace : WordTrace (prefixWord ++ tailWord_4885699) baseStart_4885699 baseEnd_4885699 := by
    simpa [prefixWord, tailWord_4885699, baseEnd_4885699] using wordTrace_append hprefix tailTrace_4885699
  have hstable : (prefixWord ++ tailWord_4885699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885699).length < 2 ^ (prefixWord ++ tailWord_4885699).sum := by decide
  have hdescent : baseEnd_4885699 < baseStart_4885699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885719 : List Nat := [1, 1, 3, 2, 1, 2, 3, 3, 7]
def baseStart_4885719 : Nat := 118140960795 + 4885719 * 2 ^ 59
def prefixEnd_4885719 : Nat := 4983230072969 + 3 ^ 40 * 4885719 * 2
def baseEnd_4885719 : Nat := 278746909978230592849277

theorem tailTrace_4885719 : CollatzResearch.WordTrace tailWord_4885719 prefixEnd_4885719 278746909978230592849277 := by
  unfold tailWord_4885719
  simp only [CollatzResearch.WordTrace]
  refine ⟨178196811386881952219188211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118797874257921301479458807 178196811386881952219188211)
  ·
    refine ⟨267295217080322928328782317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178196811386881952219188211 267295217080322928328782317)
    ·
      refine ⟨100235706405121098123293369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267295217080322928328782317 100235706405121098123293369)
      ·
        refine ⟨75176779803840823592470027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100235706405121098123293369 75176779803840823592470027)
        ·
          refine ⟨112765169705761235388705041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75176779803840823592470027 112765169705761235388705041)
          ·
            refine ⟨84573877279320926541528781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112765169705761235388705041 84573877279320926541528781)
            ·
              refine ⟨31715203979745347453073293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84573877279320926541528781 31715203979745347453073293)
              ·
                refine ⟨11893201492404505294902485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31715203979745347453073293 11893201492404505294902485)
                ·
                  refine ⟨278746909978230592849277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11893201492404505294902485 278746909978230592849277)
                  ·
                    rfl

theorem cell23_4885719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 7].length) (baseStart_4885719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885719 prefixEnd_4885719 := by exact prefixLift 4885719
  have htrace : WordTrace (prefixWord ++ tailWord_4885719) baseStart_4885719 baseEnd_4885719 := by
    simpa [prefixWord, tailWord_4885719, baseEnd_4885719] using wordTrace_append hprefix tailTrace_4885719
  have hstable : (prefixWord ++ tailWord_4885719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885719).length < 2 ^ (prefixWord ++ tailWord_4885719).sum := by decide
  have hdescent : baseEnd_4885719 < baseStart_4885719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885823 : List Nat := [1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 3]
def baseStart_4885823 : Nat := 118140960795 + 4885823 * 2 ^ 59
def prefixEnd_4885823 : Nat := 4983230072969 + 3 ^ 40 * 4885823 * 2
def baseEnd_4885823 : Nat := 2508775591792142928743015

theorem tailTrace_4885823 : CollatzResearch.WordTrace tailWord_4885823 prefixEnd_4885823 2508775591792142928743015 := by
  unfold tailWord_4885823
  simp only [CollatzResearch.WordTrace]
  refine ⟨178200604578505177980974123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118800403052336785320649415 178200604578505177980974123)
  ·
    refine ⟨267300906867757766971461185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178200604578505177980974123 267300906867757766971461185)
    ·
      refine ⟨200475680150818325228595889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267300906867757766971461185 200475680150818325228595889)
      ·
        refine ⟨150356760113113743921446917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200475680150818325228595889 150356760113113743921446917)
        ·
          refine ⟨28191892521208826985271297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150356760113113743921446917 28191892521208826985271297)
          ·
            refine ⟨21143919390906620238953473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28191892521208826985271297 21143919390906620238953473)
            ·
              refine ⟨15857939543179965179215105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21143919390906620238953473 15857939543179965179215105)
              ·
                refine ⟨11893454657384973884411329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15857939543179965179215105 11893454657384973884411329)
                ·
                  refine ⟨8920090993038730413308497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11893454657384973884411329 8920090993038730413308497)
                  ·
                    refine ⟨6690068244779047809981373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8920090993038730413308497 6690068244779047809981373)
                    ·
                      refine ⟨2508775591792142928743015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6690068244779047809981373 2508775591792142928743015)
                      ·
                        rfl

theorem cell23_4885823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 3].length) (baseStart_4885823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885823 prefixEnd_4885823 := by exact prefixLift 4885823
  have htrace : WordTrace (prefixWord ++ tailWord_4885823) baseStart_4885823 baseEnd_4885823 := by
    simpa [prefixWord, tailWord_4885823, baseEnd_4885823] using wordTrace_append hprefix tailTrace_4885823
  have hstable : (prefixWord ++ tailWord_4885823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885823).length < 2 ^ (prefixWord ++ tailWord_4885823).sum := by decide
  have hdescent : baseEnd_4885823 < baseStart_4885823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885877 : List Nat := [1, 3, 4, 1, 4, 1, 1, 2, 6]
def baseStart_4885877 : Nat := 118140960795 + 4885877 * 2 ^ 59
def prefixEnd_4885877 : Nat := 4983230072969 + 3 ^ 40 * 4885877 * 2
def baseEnd_4885877 : Nat := 278755924416387301940863

theorem tailTrace_4885877 : CollatzResearch.WordTrace tailWord_4885877 prefixEnd_4885877 278755924416387301940863 := by
  unfold tailWord_4885877
  simp only [CollatzResearch.WordTrace]
  refine ⟨178202574120309545203439885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118801716080206363468959923 178202574120309545203439885)
  ·
    refine ⟨66825965295116079451289957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178202574120309545203439885 66825965295116079451289957)
    ·
      refine ⟨12529868492834264897116867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66825965295116079451289957 12529868492834264897116867)
      ·
        refine ⟨18794802739251397345675301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12529868492834264897116867 18794802739251397345675301)
        ·
          refine ⟨3524025513609637002314119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18794802739251397345675301 3524025513609637002314119)
          ·
            refine ⟨5286038270414455503471179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3524025513609637002314119 5286038270414455503471179)
            ·
              refine ⟨7929057405621683255206769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5286038270414455503471179 7929057405621683255206769)
              ·
                refine ⟨5946793054216262441405077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7929057405621683255206769 5946793054216262441405077)
                ·
                  refine ⟨278755924416387301940863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5946793054216262441405077 278755924416387301940863)
                  ·
                    rfl

theorem cell23_4885877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 6].length) (baseStart_4885877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885877 prefixEnd_4885877 := by exact prefixLift 4885877
  have htrace : WordTrace (prefixWord ++ tailWord_4885877) baseStart_4885877 baseEnd_4885877 := by
    simpa [prefixWord, tailWord_4885877, baseEnd_4885877] using wordTrace_append hprefix tailTrace_4885877
  have hstable : (prefixWord ++ tailWord_4885877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885877).length < 2 ^ (prefixWord ++ tailWord_4885877).sum := by decide
  have hdescent : baseEnd_4885877 < baseStart_4885877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885933 : List Nat := [1, 5, 2, 2, 1, 1, 11]
def baseStart_4885933 : Nat := 118140960795 + 4885933 * 2 ^ 59
def prefixEnd_4885933 : Nat := 4983230072969 + 3 ^ 40 * 4885933 * 2
def baseEnd_4885933 : Nat := 30973235489680709856389

theorem tailTrace_4885933 : CollatzResearch.WordTrace tailWord_4885933 prefixEnd_4885933 30973235489680709856389 := by
  unfold tailWord_4885933
  simp only [CollatzResearch.WordTrace]
  refine ⟨178204616608106666767478453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118803077738737777844985635 178204616608106666767478453)
  ·
    refine ⟨16706682807010000009451105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 178204616608106666767478453 16706682807010000009451105)
    ·
      refine ⟨12530012105257500007088329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16706682807010000009451105 12530012105257500007088329)
      ·
        refine ⟨9397509078943125005316247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12530012105257500007088329 9397509078943125005316247)
        ·
          refine ⟨14096263618414687507974371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9397509078943125005316247 14096263618414687507974371)
          ·
            refine ⟨21144395427622031261961557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14096263618414687507974371 21144395427622031261961557)
            ·
              refine ⟨30973235489680709856389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 21144395427622031261961557 30973235489680709856389)
              ·
                rfl

theorem cell23_4885933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 11].length) (baseStart_4885933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885933 prefixEnd_4885933 := by exact prefixLift 4885933
  have htrace : WordTrace (prefixWord ++ tailWord_4885933) baseStart_4885933 baseEnd_4885933 := by
    simpa [prefixWord, tailWord_4885933, baseEnd_4885933] using wordTrace_append hprefix tailTrace_4885933
  have hstable : (prefixWord ++ tailWord_4885933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885933).length < 2 ^ (prefixWord ++ tailWord_4885933).sum := by decide
  have hdescent : baseEnd_4885933 < baseStart_4885933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4885994 : List Nat := [3, 1, 3, 1, 4, 1, 2, 2, 2, 1, 3]
def baseStart_4885994 : Nat := 118140960795 + 4885994 * 2 ^ 59
def prefixEnd_4885994 : Nat := 4983230072969 + 3 ^ 40 * 4885994 * 2
def baseEnd_4885994 : Nat := 2508863396984061759704729

theorem tailTrace_4885994 : CollatzResearch.WordTrace tailWord_4885994 prefixEnd_4885994 2508863396984061759704729 := by
  unfold tailWord_4885994
  simp only [CollatzResearch.WordTrace]
  refine ⟨44551710365221418546362259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118804560973923782790299357 44551710365221418546362259)
  ·
    refine ⟨66827565547832127819543389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44551710365221418546362259 66827565547832127819543389)
    ·
      refine ⟨25060337080437047932328771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66827565547832127819543389 25060337080437047932328771)
      ·
        refine ⟨37590505620655571898493157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25060337080437047932328771 37590505620655571898493157)
        ·
          refine ⟨7048219803872919730967467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37590505620655571898493157 7048219803872919730967467)
          ·
            refine ⟨10572329705809379596451201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7048219803872919730967467 10572329705809379596451201)
            ·
              refine ⟨7929247279357034697338401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10572329705809379596451201 7929247279357034697338401)
              ·
                refine ⟨5946935459517776023003801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7929247279357034697338401 5946935459517776023003801)
                ·
                  refine ⟨4460201594638332017252851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5946935459517776023003801 4460201594638332017252851)
                  ·
                    refine ⟨6690302391957498025879277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4460201594638332017252851 6690302391957498025879277)
                    ·
                      refine ⟨2508863396984061759704729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6690302391957498025879277 2508863396984061759704729)
                      ·
                        rfl

theorem cell23_4885994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_4885994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4885994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4885994 prefixEnd_4885994 := by exact prefixLift 4885994
  have htrace : WordTrace (prefixWord ++ tailWord_4885994) baseStart_4885994 baseEnd_4885994 := by
    simpa [prefixWord, tailWord_4885994, baseEnd_4885994] using wordTrace_append hprefix tailTrace_4885994
  have hstable : (prefixWord ++ tailWord_4885994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4885994).length < 2 ^ (prefixWord ++ tailWord_4885994).sum := by decide
  have hdescent : baseEnd_4885994 < baseStart_4885994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4885994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886013 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 1, 4, 4]
def baseStart_4886013 : Nat := 118140960795 + 4886013 * 2 ^ 59
def prefixEnd_4886013 : Nat := 4983230072969 + 3 ^ 40 * 4886013 * 2
def baseEnd_4886013 : Nat := 2508873153116497185367141

theorem tailTrace_4886013 : CollatzResearch.WordTrace tailWord_4886013 prefixEnd_4886013 2508873153116497185367141 := by
  unfold tailWord_4886013
  simp only [CollatzResearch.WordTrace]
  refine ⟨178207534447816840430390693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118805022965211226953593795 178207534447816840430390693)
  ·
    refine ⟨33413912708965657580698255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178207534447816840430390693 33413912708965657580698255)
    ·
      refine ⟨50120869063448486371047383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33413912708965657580698255 50120869063448486371047383)
      ·
        refine ⟨75181303595172729556571075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50120869063448486371047383 75181303595172729556571075)
        ·
          refine ⟨112771955392759094334856613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75181303595172729556571075 112771955392759094334856613)
          ·
            refine ⟨21144741636142330187785615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112771955392759094334856613 21144741636142330187785615)
            ·
              refine ⟨31717112454213495281678423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21144741636142330187785615 31717112454213495281678423)
              ·
                refine ⟨47575668681320242922517635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31717112454213495281678423 47575668681320242922517635)
                ·
                  refine ⟨71363503021980364383776453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47575668681320242922517635 71363503021980364383776453)
                  ·
                    refine ⟨13380656816621318321958085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71363503021980364383776453 13380656816621318321958085)
                    ·
                      refine ⟨2508873153116497185367141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13380656816621318321958085 2508873153116497185367141)
                      ·
                        rfl

theorem cell23_4886013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_4886013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886013 prefixEnd_4886013 := by exact prefixLift 4886013
  have htrace : WordTrace (prefixWord ++ tailWord_4886013) baseStart_4886013 baseEnd_4886013 := by
    simpa [prefixWord, tailWord_4886013, baseEnd_4886013] using wordTrace_append hprefix tailTrace_4886013
  have hstable : (prefixWord ++ tailWord_4886013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886013).length < 2 ^ (prefixWord ++ tailWord_4886013).sum := by decide
  have hdescent : baseEnd_4886013 < baseStart_4886013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886023 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 9]
def baseStart_4886023 : Nat := 118140960795 + 4886023 * 2 ^ 59
def prefixEnd_4886023 : Nat := 4983230072969 + 3 ^ 40 * 4886023 * 2
def baseEnd_4886023 : Nat := 278764254213671349582455

theorem tailTrace_4886023 : CollatzResearch.WordTrace tailWord_4886023 prefixEnd_4886023 278764254213671349582455 := by
  unfold tailWord_4886023
  simp only [CollatzResearch.WordTrace]
  refine ⟨178207899177780612138254723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118805266118520408092169815 178207899177780612138254723)
  ·
    refine ⟨267311848766670918207382085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178207899177780612138254723 267311848766670918207382085)
    ·
      refine ⟨50120971643750797163884141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 267311848766670918207382085 50120971643750797163884141)
      ·
        refine ⟨18795364366406548936456553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50120971643750797163884141 18795364366406548936456553)
        ·
          refine ⟨14096523274804911702342415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18795364366406548936456553 14096523274804911702342415)
          ·
            refine ⟨21144784912207367553513623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14096523274804911702342415 21144784912207367553513623)
            ·
              refine ⟨31717177368311051330270435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21144784912207367553513623 31717177368311051330270435)
              ·
                refine ⟨47575766052466576995405653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31717177368311051330270435 47575766052466576995405653)
                ·
                  refine ⟨278764254213671349582455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47575766052466576995405653 278764254213671349582455)
                  ·
                    rfl

theorem cell23_4886023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 9].length) (baseStart_4886023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886023 prefixEnd_4886023 := by exact prefixLift 4886023
  have htrace : WordTrace (prefixWord ++ tailWord_4886023) baseStart_4886023 baseEnd_4886023 := by
    simpa [prefixWord, tailWord_4886023, baseEnd_4886023] using wordTrace_append hprefix tailTrace_4886023
  have hstable : (prefixWord ++ tailWord_4886023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886023).length < 2 ^ (prefixWord ++ tailWord_4886023).sum := by decide
  have hdescent : baseEnd_4886023 < baseStart_4886023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886033 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 3]
def baseStart_4886033 : Nat := 118140960795 + 4886033 * 2 ^ 59
def prefixEnd_4886033 : Nat := 4983230072969 + 3 ^ 40 * 4886033 * 2
def baseEnd_4886033 : Nat := 2508883422729587107117049

theorem tailTrace_4886033 : CollatzResearch.WordTrace tailWord_4886033 prefixEnd_4886033 2508883422729587107117049 := by
  unfold tailWord_4886033
  simp only [CollatzResearch.WordTrace]
  refine ⟨178208263907744383846118753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118805509271829589230745835 178208263907744383846118753)
  ·
    refine ⟨133656197930808287884589065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178208263907744383846118753 133656197930808287884589065)
    ·
      refine ⟨100242148448106215913441799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133656197930808287884589065 100242148448106215913441799)
      ·
        refine ⟨150363222672159323870162699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100242148448106215913441799 150363222672159323870162699)
        ·
          refine ⟨225544834008238985805244049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150363222672159323870162699 225544834008238985805244049)
          ·
            refine ⟨169158625506179239353933037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225544834008238985805244049 169158625506179239353933037)
            ·
              refine ⟨63434484564817214757724889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169158625506179239353933037 63434484564817214757724889)
              ·
                refine ⟨47575863423612911068293667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63434484564817214757724889 47575863423612911068293667)
                ·
                  refine ⟨71363795135419366602440501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47575863423612911068293667 71363795135419366602440501)
                  ·
                    refine ⟨6690355793945565618978797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71363795135419366602440501 6690355793945565618978797)
                    ·
                      refine ⟨2508883422729587107117049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6690355793945565618978797 2508883422729587107117049)
                      ·
                        rfl

theorem cell23_4886033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 3].length) (baseStart_4886033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886033 prefixEnd_4886033 := by exact prefixLift 4886033
  have htrace : WordTrace (prefixWord ++ tailWord_4886033) baseStart_4886033 baseEnd_4886033 := by
    simpa [prefixWord, tailWord_4886033, baseEnd_4886033] using wordTrace_append hprefix tailTrace_4886033
  have hstable : (prefixWord ++ tailWord_4886033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886033).length < 2 ^ (prefixWord ++ tailWord_4886033).sum := by decide
  have hdescent : baseEnd_4886033 < baseStart_4886033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886050 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 2, 3, 3]
def baseStart_4886050 : Nat := 118140960795 + 4886050 * 2 ^ 59
def prefixEnd_4886050 : Nat := 4983230072969 + 3 ^ 40 * 4886050 * 2
def baseEnd_4886050 : Nat := 2508892151900713540604471

theorem tailTrace_4886050 : CollatzResearch.WordTrace tailWord_4886050 prefixEnd_4886050 2508892151900713540604471 := by
  unfold tailWord_4886050
  simp only [CollatzResearch.WordTrace]
  refine ⟨44552220987170698937371901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118805922632455197166325069 44552220987170698937371901)
  ·
    refine ⟨16707082870189012101514463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44552220987170698937371901 16707082870189012101514463)
    ·
      refine ⟨25060624305283518152271695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16707082870189012101514463 25060624305283518152271695)
      ·
        refine ⟨37590936457925277228407543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25060624305283518152271695 37590936457925277228407543)
        ·
          refine ⟨56386404686887915842611315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37590936457925277228407543 56386404686887915842611315)
          ·
            refine ⟨84579607030331873763916973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56386404686887915842611315 84579607030331873763916973)
            ·
              refine ⟨31717352636374452661468865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84579607030331873763916973 31717352636374452661468865)
              ·
                refine ⟨23788014477280839496101649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31717352636374452661468865 23788014477280839496101649)
                ·
                  refine ⟨17841010857960629622076237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23788014477280839496101649 17841010857960629622076237)
                  ·
                    refine ⟨6690379071735236108278589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17841010857960629622076237 6690379071735236108278589)
                    ·
                      refine ⟨2508892151900713540604471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6690379071735236108278589 2508892151900713540604471)
                      ·
                        rfl

theorem cell23_4886050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_4886050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886050 prefixEnd_4886050 := by exact prefixLift 4886050
  have htrace : WordTrace (prefixWord ++ tailWord_4886050) baseStart_4886050 baseEnd_4886050 := by
    simpa [prefixWord, tailWord_4886050, baseEnd_4886050] using wordTrace_append hprefix tailTrace_4886050
  have hstable : (prefixWord ++ tailWord_4886050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886050).length < 2 ^ (prefixWord ++ tailWord_4886050).sum := by decide
  have hdescent : baseEnd_4886050 < baseStart_4886050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886051 : List Nat := [1, 1, 1, 4, 5, 2, 1, 2, 2, 2, 2]
def baseStart_4886051 : Nat := 118140960795 + 4886051 * 2 ^ 59
def prefixEnd_4886051 : Nat := 4983230072969 + 3 ^ 40 * 4886051 * 2
def baseEnd_4886051 : Nat := 2508892665381368036691967

theorem tailTrace_4886051 : CollatzResearch.WordTrace tailWord_4886051 prefixEnd_4886051 2508892665381368036691967 := by
  unfold tailWord_4886051
  simp only [CollatzResearch.WordTrace]
  refine ⟨178208920421679172920274007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118805946947786115280182671 178208920421679172920274007)
  ·
    refine ⟨267313380632518759380411011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178208920421679172920274007 267313380632518759380411011)
    ·
      refine ⟨400970070948778139070616517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267313380632518759380411011 400970070948778139070616517)
      ·
        refine ⟨75181888302895901075740597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 400970070948778139070616517 75181888302895901075740597)
        ·
          refine ⟨7048302028396490725850681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75181888302895901075740597 7048302028396490725850681)
          ·
            refine ⟨5286226521297368044388011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7048302028396490725850681 5286226521297368044388011)
            ·
              refine ⟨7929339781946052066582017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5286226521297368044388011 7929339781946052066582017)
              ·
                refine ⟨5947004836459539049936513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7929339781946052066582017 5947004836459539049936513)
                ·
                  refine ⟨4460253627344654287452385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5947004836459539049936513 4460253627344654287452385)
                  ·
                    refine ⟨3345190220508490715589289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4460253627344654287452385 3345190220508490715589289)
                    ·
                      refine ⟨2508892665381368036691967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3345190220508490715589289 2508892665381368036691967)
                      ·
                        rfl

theorem cell23_4886051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 2, 2].length) (baseStart_4886051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886051 prefixEnd_4886051 := by exact prefixLift 4886051
  have htrace : WordTrace (prefixWord ++ tailWord_4886051) baseStart_4886051 baseEnd_4886051 := by
    simpa [prefixWord, tailWord_4886051, baseEnd_4886051] using wordTrace_append hprefix tailTrace_4886051
  have hstable : (prefixWord ++ tailWord_4886051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886051).length < 2 ^ (prefixWord ++ tailWord_4886051).sum := by decide
  have hdescent : baseEnd_4886051 < baseStart_4886051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886053 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 4, 5]
def baseStart_4886053 : Nat := 118140960795 + 4886053 * 2 ^ 59
def prefixEnd_4886053 : Nat := 4983230072969 + 3 ^ 40 * 4886053 * 2
def baseEnd_4886053 : Nat := 836297897447559009622319

theorem tailTrace_4886053 : CollatzResearch.WordTrace tailWord_4886053 prefixEnd_4886053 836297897447559009622319 := by
  unfold tailWord_4886053
  simp only [CollatzResearch.WordTrace]
  refine ⟨178208993367671927261846813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118805995578447951507897875 178208993367671927261846813)
  ·
    refine ⟨66828372512876972723192555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178208993367671927261846813 66828372512876972723192555)
    ·
      refine ⟨100242558769315459084788833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66828372512876972723192555 100242558769315459084788833)
      ·
        refine ⟨75181919076986594313591625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100242558769315459084788833 75181919076986594313591625)
        ·
          refine ⟨56386439307739945735193719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75181919076986594313591625 56386439307739945735193719)
          ·
            refine ⟨84579658961609918602790579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56386439307739945735193719 84579658961609918602790579)
            ·
              refine ⟨126869488442414877904185869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84579658961609918602790579 126869488442414877904185869)
              ·
                refine ⟨47576058165905579214069701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126869488442414877904185869 47576058165905579214069701)
                ·
                  refine ⟨8920510906107296102638069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47576058165905579214069701 8920510906107296102638069)
                  ·
                    refine ⟨836297897447559009622319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8920510906107296102638069 836297897447559009622319)
                    ·
                      rfl

theorem cell23_4886053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_4886053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886053 prefixEnd_4886053 := by exact prefixLift 4886053
  have htrace : WordTrace (prefixWord ++ tailWord_4886053) baseStart_4886053 baseEnd_4886053 := by
    simpa [prefixWord, tailWord_4886053, baseEnd_4886053] using wordTrace_append hprefix tailTrace_4886053
  have hstable : (prefixWord ++ tailWord_4886053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886053).length < 2 ^ (prefixWord ++ tailWord_4886053).sum := by decide
  have hdescent : baseEnd_4886053 < baseStart_4886053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886090 : List Nat := [3, 1, 2, 1, 1, 3, 2, 3, 2, 1, 4]
def baseStart_4886090 : Nat := 118140960795 + 4886090 * 2 ^ 59
def prefixEnd_4886090 : Nat := 4983230072969 + 3 ^ 40 * 4886090 * 2
def baseEnd_4886090 : Nat := 2508912691126893384104287

theorem tailTrace_4886090 : CollatzResearch.WordTrace tailWord_4886090 prefixEnd_4886090 2508912691126893384104287 := by
  unfold tailWord_4886090
  simp only [CollatzResearch.WordTrace]
  refine ⟨44552585717134470645235931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118806895245691921720629149 44552585717134470645235931)
  ·
    refine ⟨66828878575701705967853897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44552585717134470645235931 66828878575701705967853897)
    ·
      refine ⟨50121658931776279475890423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66828878575701705967853897 50121658931776279475890423)
      ·
        refine ⟨75182488397664419213835635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50121658931776279475890423 75182488397664419213835635)
        ·
          refine ⟨112773732596496628820753453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75182488397664419213835635 112773732596496628820753453)
          ·
            refine ⟨42290149723686235807782545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112773732596496628820753453 42290149723686235807782545)
            ·
              refine ⟨31717612292764676855836909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42290149723686235807782545 31717612292764676855836909)
              ·
                refine ⟨11894104609786753820938841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31717612292764676855836909 11894104609786753820938841)
                ·
                  refine ⟨8920578457340065365704131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11894104609786753820938841 8920578457340065365704131)
                  ·
                    refine ⟨13380867686010098048556197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8920578457340065365704131 13380867686010098048556197)
                    ·
                      refine ⟨2508912691126893384104287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13380867686010098048556197 2508912691126893384104287)
                      ·
                        rfl

theorem cell23_4886090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_4886090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886090 prefixEnd_4886090 := by exact prefixLift 4886090
  have htrace : WordTrace (prefixWord ++ tailWord_4886090) baseStart_4886090 baseEnd_4886090 := by
    simpa [prefixWord, tailWord_4886090, baseEnd_4886090] using wordTrace_append hprefix tailTrace_4886090
  have hstable : (prefixWord ++ tailWord_4886090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886090).length < 2 ^ (prefixWord ++ tailWord_4886090).sum := by decide
  have hdescent : baseEnd_4886090 < baseStart_4886090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886113 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 8]
def baseStart_4886113 : Nat := 118140960795 + 4886113 * 2 ^ 59
def prefixEnd_4886113 : Nat := 4983230072969 + 3 ^ 40 * 4886113 * 2
def baseEnd_4886113 : Nat := 278769389020216310457409

theorem tailTrace_4886113 : CollatzResearch.WordTrace tailWord_4886113 prefixEnd_4886113 278769389020216310457409 := by
  unfold tailWord_4886113
  simp only [CollatzResearch.WordTrace]
  refine ⟨178211181747454557509030993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118807454498303038339353995 178211181747454557509030993)
  ·
    refine ⟨133658386310590918131773245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178211181747454557509030993 133658386310590918131773245)
    ·
      refine ⟨50121894866471594299414967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133658386310590918131773245 50121894866471594299414967)
      ·
        refine ⟨75182842299707391449122451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50121894866471594299414967 75182842299707391449122451)
        ·
          refine ⟨112774263449561087173683677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75182842299707391449122451 112774263449561087173683677)
          ·
            refine ⟨42290348793585407690131379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112774263449561087173683677 42290348793585407690131379)
            ·
              refine ⟨63435523190378111535197069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42290348793585407690131379 63435523190378111535197069)
              ·
                refine ⟨23788321196391791825698901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63435523190378111535197069 23788321196391791825698901)
                ·
                  refine ⟨278769389020216310457409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23788321196391791825698901 278769389020216310457409)
                  ·
                    rfl

theorem cell23_4886113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 8].length) (baseStart_4886113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886113 prefixEnd_4886113 := by exact prefixLift 4886113
  have htrace : WordTrace (prefixWord ++ tailWord_4886113) baseStart_4886113 baseEnd_4886113 := by
    simpa [prefixWord, tailWord_4886113, baseEnd_4886113] using wordTrace_append hprefix tailTrace_4886113
  have hstable : (prefixWord ++ tailWord_4886113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886113).length < 2 ^ (prefixWord ++ tailWord_4886113).sum := by decide
  have hdescent : baseEnd_4886113 < baseStart_4886113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886117 : List Nat := [1, 3, 1, 3, 3, 1, 3, 1, 3, 4]
def baseStart_4886117 : Nat := 118140960795 + 4886117 * 2 ^ 59
def prefixEnd_4886117 : Nat := 4983230072969 + 3 ^ 40 * 4886117 * 2
def baseEnd_4886117 : Nat := 836308851701521592822221

theorem tailTrace_4886117 : CollatzResearch.WordTrace tailWord_4886117 prefixEnd_4886117 836308851701521592822221 := by
  unfold tailWord_4886117
  simp only [CollatzResearch.WordTrace]
  refine ⟨178211327639440066192176605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118807551759626710794784403 178211327639440066192176605)
  ·
    refine ⟨66829247864790024822066227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178211327639440066192176605 66829247864790024822066227)
    ·
      refine ⟨100243871797185037233099341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66829247864790024822066227 100243871797185037233099341)
      ·
        refine ⟨37591451923944388962412253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100243871797185037233099341 37591451923944388962412253)
        ·
          refine ⟨14096794471479145860904595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37591451923944388962412253 14096794471479145860904595)
          ·
            refine ⟨21145191707218718791356893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14096794471479145860904595 21145191707218718791356893)
            ·
              refine ⟨7929446890207019546758835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21145191707218718791356893 7929446890207019546758835)
              ·
                refine ⟨11894170335310529320138253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7929446890207019546758835 11894170335310529320138253)
                ·
                  refine ⟨4460313875741448495051845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11894170335310529320138253 4460313875741448495051845)
                  ·
                    refine ⟨836308851701521592822221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4460313875741448495051845 836308851701521592822221)
                    ·
                      rfl

theorem cell23_4886117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 4].length) (baseStart_4886117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886117 prefixEnd_4886117 := by exact prefixLift 4886117
  have htrace : WordTrace (prefixWord ++ tailWord_4886117) baseStart_4886117 baseEnd_4886117 := by
    simpa [prefixWord, tailWord_4886117, baseEnd_4886117] using wordTrace_append hprefix tailTrace_4886117
  have hstable : (prefixWord ++ tailWord_4886117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886117).length < 2 ^ (prefixWord ++ tailWord_4886117).sum := by decide
  have hdescent : baseEnd_4886117 < baseStart_4886117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886160 : List Nat := [2, 1, 1, 1, 1, 1, 3, 7, 1, 5]
def baseStart_4886160 : Nat := 118140960795 + 4886160 * 2 ^ 59
def prefixEnd_4886160 : Nat := 4983230072969 + 3 ^ 40 * 4886160 * 2
def baseEnd_4886160 : Nat := 836316211590902703409655

theorem tailTrace_4886160 : CollatzResearch.WordTrace tailWord_4886160 prefixEnd_4886160 836316211590902703409655 := by
  unfold tailWord_4886160
  simp only [CollatzResearch.WordTrace]
  refine ⟨89106447989142142267995967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118808597318856189690661289 89106447989142142267995967)
  ·
    refine ⟨133659671983713213401993951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89106447989142142267995967 133659671983713213401993951)
    ·
      refine ⟨200489507975569820102990927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133659671983713213401993951 200489507975569820102990927)
      ·
        refine ⟨300734261963354730154486391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200489507975569820102990927 300734261963354730154486391)
        ·
          refine ⟨451101392945032095231729587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300734261963354730154486391 451101392945032095231729587)
          ·
            refine ⟨676652089417548142847594381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451101392945032095231729587 676652089417548142847594381)
            ·
              refine ⟨253744533531580553567847893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 676652089417548142847594381 253744533531580553567847893)
              ·
                refine ⟨5947137504646419224246435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 253744533531580553567847893 5947137504646419224246435)
                ·
                  refine ⟨8920706256969628836369653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5947137504646419224246435 8920706256969628836369653)
                  ·
                    refine ⟨836316211590902703409655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8920706256969628836369653 836316211590902703409655)
                    ·
                      rfl

theorem cell23_4886160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 1, 5].length) (baseStart_4886160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886160 prefixEnd_4886160 := by exact prefixLift 4886160
  have htrace : WordTrace (prefixWord ++ tailWord_4886160) baseStart_4886160 baseEnd_4886160 := by
    simpa [prefixWord, tailWord_4886160, baseEnd_4886160] using wordTrace_append hprefix tailTrace_4886160
  have hstable : (prefixWord ++ tailWord_4886160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886160).length < 2 ^ (prefixWord ++ tailWord_4886160).sum := by decide
  have hdescent : baseEnd_4886160 < baseStart_4886160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886164 : List Nat := [2, 4, 2, 2, 2, 1, 2, 2, 6]
def baseStart_4886164 : Nat := 118140960795 + 4886164 * 2 ^ 59
def prefixEnd_4886164 : Nat := 4983230072969 + 3 ^ 40 * 4886164 * 2
def baseEnd_4886164 : Nat := 278772298743925121619883

theorem tailTrace_4886164 : CollatzResearch.WordTrace tailWord_4886164 prefixEnd_4886164 278772298743925121619883 := by
  unfold tailWord_4886164
  simp only [CollatzResearch.WordTrace]
  refine ⟨89106520935134896609568773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118808694580179862146091697 89106520935134896609568773)
  ·
    refine ⟨16707472675337793114294145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89106520935134896609568773 16707472675337793114294145)
    ·
      refine ⟨12530604506503344835720609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16707472675337793114294145 12530604506503344835720609)
      ·
        refine ⟨9397953379877508626790457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12530604506503344835720609 9397953379877508626790457)
        ·
          refine ⟨7048465034908131470092843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9397953379877508626790457 7048465034908131470092843)
          ·
            refine ⟨10572697552362197205139265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7048465034908131470092843 10572697552362197205139265)
            ·
              refine ⟨7929523164271647903854449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10572697552362197205139265 7929523164271647903854449)
              ·
                refine ⟨5947142373203735927890837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7929523164271647903854449 5947142373203735927890837)
                ·
                  refine ⟨278772298743925121619883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5947142373203735927890837 278772298743925121619883)
                  ·
                    rfl

theorem cell23_4886164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_4886164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886164 prefixEnd_4886164 := by exact prefixLift 4886164
  have htrace : WordTrace (prefixWord ++ tailWord_4886164) baseStart_4886164 baseEnd_4886164 := by
    simpa [prefixWord, tailWord_4886164, baseEnd_4886164] using wordTrace_append hprefix tailTrace_4886164
  have hstable : (prefixWord ++ tailWord_4886164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886164).length < 2 ^ (prefixWord ++ tailWord_4886164).sum := by decide
  have hdescent : baseEnd_4886164 < baseStart_4886164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886203 : List Nat := [1, 1, 1, 1, 1, 2, 3, 13]
def baseStart_4886203 : Nat := 118140960795 + 4886203 * 2 ^ 59
def prefixEnd_4886203 : Nat := 4983230072969 + 3 ^ 40 * 4886203 * 2
def baseEnd_4886203 : Nat := 92924841275587090444121

theorem tailTrace_4886203 : CollatzResearch.WordTrace tailWord_4886203 prefixEnd_4886203 92924841275587090444121 := by
  unfold tailWord_4886203
  simp only [CollatzResearch.WordTrace]
  refine ⟨178214464317128502879807263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118809642878085668586538175 178214464317128502879807263)
  ·
    refine ⟨267321696475692754319710895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178214464317128502879807263 267321696475692754319710895)
    ·
      refine ⟨400982544713539131479566343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267321696475692754319710895 400982544713539131479566343)
      ·
        refine ⟨601473817070308697219349515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400982544713539131479566343 601473817070308697219349515)
        ·
          refine ⟨902210725605463045829024273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601473817070308697219349515 902210725605463045829024273)
          ·
            refine ⟨676658044204097284371768205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 902210725605463045829024273 676658044204097284371768205)
            ·
              refine ⟨253746766576536481639413077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 676658044204097284371768205 253746766576536481639413077)
              ·
                refine ⟨92924841275587090444121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 253746766576536481639413077 92924841275587090444121)
                ·
                  rfl

theorem cell23_4886203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 13].length) (baseStart_4886203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886203 prefixEnd_4886203 := by exact prefixLift 4886203
  have htrace : WordTrace (prefixWord ++ tailWord_4886203) baseStart_4886203 baseEnd_4886203 := by
    simpa [prefixWord, tailWord_4886203, baseEnd_4886203] using wordTrace_append hprefix tailTrace_4886203
  have hstable : (prefixWord ++ tailWord_4886203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886203).length < 2 ^ (prefixWord ++ tailWord_4886203).sum := by decide
  have hdescent : baseEnd_4886203 < baseStart_4886203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886231 : List Nat := [1, 1, 3, 2, 1, 3, 1, 6, 1, 2, 2]
def baseStart_4886231 : Nat := 118140960795 + 4886231 * 2 ^ 59
def prefixEnd_4886231 : Nat := 4983230072969 + 3 ^ 40 * 4886231 * 2
def baseEnd_4886231 : Nat := 2508985091899177332441139

theorem tailTrace_4886231 : CollatzResearch.WordTrace tailWord_4886231 prefixEnd_4886231 2508985091899177332441139 := by
  unfold tailWord_4886231
  simp only [CollatzResearch.WordTrace]
  refine ⟨178215485561027063661826547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118810323707351375774551031 178215485561027063661826547)
  ·
    refine ⟨267323228341540595492739821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178215485561027063661826547 267323228341540595492739821)
    ·
      refine ⟨100246210628077723309777433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267323228341540595492739821 100246210628077723309777433)
      ·
        refine ⟨75184657971058292482333075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100246210628077723309777433 75184657971058292482333075)
        ·
          refine ⟨112776986956587438723499613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75184657971058292482333075 112776986956587438723499613)
          ·
            refine ⟨42291370108720289521312355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112776986956587438723499613 42291370108720289521312355)
            ·
              refine ⟨63437055163080434281968533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42291370108720289521312355 63437055163080434281968533)
              ·
                refine ⟨2973611960769395356967275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63437055163080434281968533 2973611960769395356967275)
                ·
                  refine ⟨4460417941154093035450913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2973611960769395356967275 4460417941154093035450913)
                  ·
                    refine ⟨3345313455865569776588185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4460417941154093035450913 3345313455865569776588185)
                    ·
                      refine ⟨2508985091899177332441139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3345313455865569776588185 2508985091899177332441139)
                      ·
                        rfl

theorem cell23_4886231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 1, 2, 2].length) (baseStart_4886231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886231 prefixEnd_4886231 := by exact prefixLift 4886231
  have htrace : WordTrace (prefixWord ++ tailWord_4886231) baseStart_4886231 baseEnd_4886231 := by
    simpa [prefixWord, tailWord_4886231, baseEnd_4886231] using wordTrace_append hprefix tailTrace_4886231
  have hstable : (prefixWord ++ tailWord_4886231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886231).length < 2 ^ (prefixWord ++ tailWord_4886231).sum := by decide
  have hdescent : baseEnd_4886231 < baseStart_4886231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886241 : List Nat := [1, 2, 3, 1, 5, 1, 3, 1, 2, 4]
def baseStart_4886241 : Nat := 118140960795 + 4886241 * 2 ^ 59
def prefixEnd_4886241 : Nat := 4983230072969 + 3 ^ 40 * 4886241 * 2
def baseEnd_4886241 : Nat := 836330075568574097772031

theorem tailTrace_4886241 : CollatzResearch.WordTrace tailWord_4886241 prefixEnd_4886241 836330075568574097772031 := by
  unfold tailWord_4886241
  simp only [CollatzResearch.WordTrace]
  refine ⟨178215850290990835369690577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118810566860660556913127051 178215850290990835369690577)
  ·
    refine ⟨133661887718243126527267933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178215850290990835369690577 133661887718243126527267933)
    ·
      refine ⟨50123207894341172447725475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133661887718243126527267933 50123207894341172447725475)
      ·
        refine ⟨75184811841511758671588213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50123207894341172447725475 75184811841511758671588213)
        ·
          refine ⟨7048576110141727375461395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75184811841511758671588213 7048576110141727375461395)
          ·
            refine ⟨10572864165212591063192093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7048576110141727375461395 10572864165212591063192093)
            ·
              refine ⟨3964824061954721648697035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10572864165212591063192093 3964824061954721648697035)
              ·
                refine ⟨5947236092932082473045553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3964824061954721648697035 5947236092932082473045553)
                ·
                  refine ⟨4460427069699061854784165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5947236092932082473045553 4460427069699061854784165)
                  ·
                    refine ⟨836330075568574097772031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4460427069699061854784165 836330075568574097772031)
                    ·
                      rfl

theorem cell23_4886241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_4886241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886241 prefixEnd_4886241 := by exact prefixLift 4886241
  have htrace : WordTrace (prefixWord ++ tailWord_4886241) baseStart_4886241 baseEnd_4886241 := by
    simpa [prefixWord, tailWord_4886241, baseEnd_4886241] using wordTrace_append hprefix tailTrace_4886241
  have hstable : (prefixWord ++ tailWord_4886241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886241).length < 2 ^ (prefixWord ++ tailWord_4886241).sum := by decide
  have hdescent : baseEnd_4886241 < baseStart_4886241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886250 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 2, 7]
def baseStart_4886250 : Nat := 118140960795 + 4886250 * 2 ^ 59
def prefixEnd_4886250 : Nat := 4983230072969 + 3 ^ 40 * 4886250 * 2
def baseEnd_4886250 : Nat := 836331616010537586034517

theorem tailTrace_4886250 : CollatzResearch.WordTrace tailWord_4886250 prefixEnd_4886250 836331616010537586034517 := by
  unfold tailWord_4886250
  simp only [CollatzResearch.WordTrace]
  refine ⟨44554044636989557476692051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118810785698638819937845469 44554044636989557476692051)
  ·
    refine ⟨66831066955484336215038077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44554044636989557476692051 66831066955484336215038077)
    ·
      refine ⟨25061650108306626080639279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66831066955484336215038077 25061650108306626080639279)
      ·
        refine ⟨37592475162459939120958919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25061650108306626080639279 37592475162459939120958919)
        ·
          refine ⟨56388712743689908681438379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37592475162459939120958919 56388712743689908681438379)
          ·
            refine ⟨84583069115534863022157569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56388712743689908681438379 84583069115534863022157569)
            ·
              refine ⟨63437301836651147266618177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84583069115534863022157569 63437301836651147266618177)
              ·
                refine ⟨47577976377488360449963633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63437301836651147266618177 47577976377488360449963633)
                ·
                  refine ⟨35683482283116270337472725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47577976377488360449963633 35683482283116270337472725)
                  ·
                    refine ⟨836331616010537586034517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35683482283116270337472725 836331616010537586034517)
                    ·
                      rfl

theorem cell23_4886250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_4886250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886250 prefixEnd_4886250 := by exact prefixLift 4886250
  have htrace : WordTrace (prefixWord ++ tailWord_4886250) baseStart_4886250 baseEnd_4886250 := by
    simpa [prefixWord, tailWord_4886250, baseEnd_4886250] using wordTrace_append hprefix tailTrace_4886250
  have hstable : (prefixWord ++ tailWord_4886250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886250).length < 2 ^ (prefixWord ++ tailWord_4886250).sum := by decide
  have hdescent : baseEnd_4886250 < baseStart_4886250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
