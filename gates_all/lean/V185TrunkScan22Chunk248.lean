import V185TrunkScan22Chunk247

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2213218 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 9]
def baseStart_2213218 : Nat := 118140960795 + 2213218 * 2 ^ 59
def prefixEnd_2213218 : Nat := 4983230072969 + 3 ^ 40 * 2213218 * 2
def baseEnd_2213218 : Nat := 252543250485028224021467

theorem tailTrace_2213218 : CollatzResearch.WordTrace tailWord_2213218 prefixEnd_2213218 252543250485028224021467 := by
  unfold tailWord_2213218
  simp only [CollatzResearch.WordTrace]
  refine ⟨20180673023974162096596077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53815128063931098924256205 20180673023974162096596077)
  ·
    refine ⟨7567752383990310786223529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20180673023974162096596077 7567752383990310786223529)
    ·
      refine ⟨5675814287992733089667647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7567752383990310786223529 5675814287992733089667647)
      ·
        refine ⟨8513721431989099634501471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5675814287992733089667647 8513721431989099634501471)
        ·
          refine ⟨12770582147983649451752207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8513721431989099634501471 12770582147983649451752207)
          ·
            refine ⟨19155873221975474177628311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12770582147983649451752207 19155873221975474177628311)
            ·
              refine ⟨28733809832963211266442467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19155873221975474177628311 28733809832963211266442467)
              ·
                refine ⟨43100714749444816899663701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28733809832963211266442467 43100714749444816899663701)
                ·
                  refine ⟨252543250485028224021467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43100714749444816899663701 252543250485028224021467)
                  ·
                    rfl

theorem cell22_2213218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_2213218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213218 prefixEnd_2213218 := by exact prefixLift 2213218
  have htrace : WordTrace (prefixWord ++ tailWord_2213218) baseStart_2213218 baseEnd_2213218 := by
    simpa [prefixWord, tailWord_2213218, baseEnd_2213218] using wordTrace_append hprefix tailTrace_2213218
  have hstable : (prefixWord ++ tailWord_2213218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213218).length < 2 ^ (prefixWord ++ tailWord_2213218).sum := by decide
  have hdescent : baseEnd_2213218 < baseStart_2213218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213252 : List Nat := [2, 3, 2, 1, 1, 5, 2, 1, 5]
def baseStart_2213252 : Nat := 118140960795 + 2213252 * 2 ^ 59
def prefixEnd_2213252 : Nat := 4983230072969 + 3 ^ 40 * 2213252 * 2
def baseEnd_2213252 : Nat := 252547130116639972238099

theorem tailTrace_2213252 : CollatzResearch.WordTrace tailWord_2213252 prefixEnd_2213252 252547130116639972238099 := by
  unfold tailWord_2213252
  simp only [CollatzResearch.WordTrace]
  refine ⟨40361966088886736096561005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53815954785182314795414673 40361966088886736096561005)
  ·
    refine ⟨15135737283332526036210377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40361966088886736096561005 15135737283332526036210377)
    ·
      refine ⟨11351802962499394527157783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15135737283332526036210377 11351802962499394527157783)
      ·
        refine ⟨17027704443749091790736675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11351802962499394527157783 17027704443749091790736675)
        ·
          refine ⟨25541556665623637686105013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17027704443749091790736675 25541556665623637686105013)
          ·
            refine ⟨2394520937402216033072345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25541556665623637686105013 2394520937402216033072345)
            ·
              refine ⟨1795890703051662024804259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2394520937402216033072345 1795890703051662024804259)
              ·
                refine ⟨2693836054577493037206389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1795890703051662024804259 2693836054577493037206389)
                ·
                  refine ⟨252547130116639972238099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2693836054577493037206389 252547130116639972238099)
                  ·
                    rfl

theorem cell22_2213252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_2213252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213252 prefixEnd_2213252 := by exact prefixLift 2213252
  have htrace : WordTrace (prefixWord ++ tailWord_2213252) baseStart_2213252 baseEnd_2213252 := by
    simpa [prefixWord, tailWord_2213252, baseEnd_2213252] using wordTrace_append hprefix tailTrace_2213252
  have hstable : (prefixWord ++ tailWord_2213252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213252).length < 2 ^ (prefixWord ++ tailWord_2213252).sum := by decide
  have hdescent : baseEnd_2213252 < baseStart_2213252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213280 : List Nat := [2, 1, 1, 4, 1, 2, 2, 5, 4]
def baseStart_2213280 : Nat := 118140960795 + 2213280 * 2 ^ 59
def prefixEnd_2213280 : Nat := 4983230072969 + 3 ^ 40 * 2213280 * 2
def baseEnd_2213280 : Nat := 252550325107379059004737

theorem tailTrace_2213280 : CollatzResearch.WordTrace tailWord_2213280 prefixEnd_2213280 252550325107379059004737 := by
  unfold tailWord_2213280
  simp only [CollatzResearch.WordTrace]
  refine ⟨40362476710836016487570647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53816635614448021983427529 40362476710836016487570647)
  ·
    refine ⟨60543715066254024731355971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40362476710836016487570647 60543715066254024731355971)
    ·
      refine ⟨90815572599381037097033957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60543715066254024731355971 90815572599381037097033957)
      ·
        refine ⟨17027919862383944455693867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90815572599381037097033957 17027919862383944455693867)
        ·
          refine ⟨25541879793575916683540801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17027919862383944455693867 25541879793575916683540801)
          ·
            refine ⟨19156409845181937512655601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25541879793575916683540801 19156409845181937512655601)
            ·
              refine ⟨14367307383886453134491701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19156409845181937512655601 14367307383886453134491701)
              ·
                refine ⟨1346935067239354981358597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14367307383886453134491701 1346935067239354981358597)
                ·
                  refine ⟨252550325107379059004737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1346935067239354981358597 252550325107379059004737)
                  ·
                    rfl

theorem cell22_2213280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 4].length) (baseStart_2213280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213280 prefixEnd_2213280 := by exact prefixLift 2213280
  have htrace : WordTrace (prefixWord ++ tailWord_2213280) baseStart_2213280 baseEnd_2213280 := by
    simpa [prefixWord, tailWord_2213280, baseEnd_2213280] using wordTrace_append hprefix tailTrace_2213280
  have hstable : (prefixWord ++ tailWord_2213280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213280).length < 2 ^ (prefixWord ++ tailWord_2213280).sum := by decide
  have hdescent : baseEnd_2213280 < baseStart_2213280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213447 : List Nat := [1, 1, 4, 1, 5, 1, 1, 2, 1, 5]
def baseStart_2213447 : Nat := 118140960795 + 2213447 * 2 ^ 59
def prefixEnd_2213447 : Nat := 4983230072969 + 3 ^ 40 * 2213447 * 2
def baseEnd_2213447 : Nat := 757708142835004408088699

theorem tailTrace_2213447 : CollatzResearch.WordTrace tailWord_2213447 prefixEnd_2213447 757708142835004408088699 := by
  unfold tailWord_2213447
  simp only [CollatzResearch.WordTrace]
  refine ⟨80731044412067020496470595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53820696274711346997647063 80731044412067020496470595)
  ·
    refine ⟨121096566618100530744705893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80731044412067020496470595 121096566618100530744705893)
    ·
      refine ⟨22705606240893849514632355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121096566618100530744705893 22705606240893849514632355)
      ·
        refine ⟨34058409361340774271948533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22705606240893849514632355 34058409361340774271948533)
        ·
          refine ⟨3192975877625697587995175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34058409361340774271948533 3192975877625697587995175)
          ·
            refine ⟨4789463816438546381992763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3192975877625697587995175 4789463816438546381992763)
            ·
              refine ⟨7184195724657819572989145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4789463816438546381992763 7184195724657819572989145)
              ·
                refine ⟨5388146793493364679741859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7184195724657819572989145 5388146793493364679741859)
                ·
                  refine ⟨8082220190240047019612789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5388146793493364679741859 8082220190240047019612789)
                  ·
                    refine ⟨757708142835004408088699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8082220190240047019612789 757708142835004408088699)
                    ·
                      rfl

theorem cell22_2213447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_2213447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213447 prefixEnd_2213447 := by exact prefixLift 2213447
  have htrace : WordTrace (prefixWord ++ tailWord_2213447) baseStart_2213447 baseEnd_2213447 := by
    simpa [prefixWord, tailWord_2213447, baseEnd_2213447] using wordTrace_append hprefix tailTrace_2213447
  have hstable : (prefixWord ++ tailWord_2213447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213447).length < 2 ^ (prefixWord ++ tailWord_2213447).sum := by decide
  have hdescent : baseEnd_2213447 < baseStart_2213447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213477 : List Nat := [1, 3, 1, 3, 3, 3, 1, 7]
def baseStart_2213477 : Nat := 118140960795 + 2213477 * 2 ^ 59
def prefixEnd_2213477 : Nat := 4983230072969 + 3 ^ 40 * 2213477 * 2
def baseEnd_2213477 : Nat := 84190934716454925537623

theorem tailTrace_2213477 : CollatzResearch.WordTrace tailWord_2213477 prefixEnd_2213477 84190934716454925537623 := by
  unfold tailWord_2213477
  simp only [CollatzResearch.WordTrace]
  refine ⟨80732138601958335620062685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53821425734638890413375123 80732138601958335620062685)
  ·
    refine ⟨30274551975734375857523507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80732138601958335620062685 30274551975734375857523507)
    ·
      refine ⟨45411827963601563786285261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30274551975734375857523507 45411827963601563786285261)
      ·
        refine ⟨17029435486350586419856973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45411827963601563786285261 17029435486350586419856973)
        ·
          refine ⟨6386038307381469907446365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17029435486350586419856973 6386038307381469907446365)
          ·
            refine ⟨2394764365268051215292387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6386038307381469907446365 2394764365268051215292387)
            ·
              refine ⟨3592146547902076822938581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2394764365268051215292387 3592146547902076822938581)
              ·
                refine ⟨84190934716454925537623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3592146547902076822938581 84190934716454925537623)
                ·
                  rfl

theorem cell22_2213477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 7].length) (baseStart_2213477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213477 prefixEnd_2213477 := by exact prefixLift 2213477
  have htrace : WordTrace (prefixWord ++ tailWord_2213477) baseStart_2213477 baseEnd_2213477 := by
    simpa [prefixWord, tailWord_2213477, baseEnd_2213477] using wordTrace_append hprefix tailTrace_2213477
  have hstable : (prefixWord ++ tailWord_2213477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213477).length < 2 ^ (prefixWord ++ tailWord_2213477).sum := by decide
  have hdescent : baseEnd_2213477 < baseStart_2213477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213494 : List Nat := [5, 1, 1, 2, 2, 2, 3, 6]
def baseStart_2213494 : Nat := 118140960795 + 2213494 * 2 ^ 59
def prefixEnd_2213494 : Nat := 4983230072969 + 3 ^ 40 * 2213494 * 2
def baseEnd_2213494 : Nat := 84191581321723550240395

theorem tailTrace_2213494 : CollatzResearch.WordTrace tailWord_2213494 prefixEnd_2213494 84191581321723550240395 := by
  unfold tailWord_2213494
  simp only [CollatzResearch.WordTrace]
  refine ⟨5045797415181046720214471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53821839095264498348954357 5045797415181046720214471)
  ·
    refine ⟨7568696122771570080321707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5045797415181046720214471 7568696122771570080321707)
    ·
      refine ⟨11353044184157355120482561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7568696122771570080321707 11353044184157355120482561)
      ·
        refine ⟨8514783138118016340361921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11353044184157355120482561 8514783138118016340361921)
        ·
          refine ⟨6386087353588512255271441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8514783138118016340361921 6386087353588512255271441)
          ·
            refine ⟨4789565515191384191453581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6386087353588512255271441 4789565515191384191453581)
            ·
              refine ⟨1796087068196769071795093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4789565515191384191453581 1796087068196769071795093)
              ·
                refine ⟨84191581321723550240395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1796087068196769071795093 84191581321723550240395)
                ·
                  rfl

theorem cell22_2213494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_2213494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213494 prefixEnd_2213494 := by exact prefixLift 2213494
  have htrace : WordTrace (prefixWord ++ tailWord_2213494) baseStart_2213494 baseEnd_2213494 := by
    simpa [prefixWord, tailWord_2213494, baseEnd_2213494] using wordTrace_append hprefix tailTrace_2213494
  have hstable : (prefixWord ++ tailWord_2213494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213494).length < 2 ^ (prefixWord ++ tailWord_2213494).sum := by decide
  have hdescent : baseEnd_2213494 < baseStart_2213494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213537 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 2, 5]
def baseStart_2213537 : Nat := 118140960795 + 2213537 * 2 ^ 59
def prefixEnd_2213537 : Nat := 4983230072969 + 3 ^ 40 * 2213537 * 2
def baseEnd_2213537 : Nat := 757738951674274173338423

theorem tailTrace_2213537 : CollatzResearch.WordTrace tailWord_2213537 prefixEnd_2213537 757738951674274173338423 := by
  unfold tailWord_2213537
  simp only [CollatzResearch.WordTrace]
  refine ⟨80734326981740965867246865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53822884654493977244831243 80734326981740965867246865)
  ·
    refine ⟨60550745236305724400435149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80734326981740965867246865 60550745236305724400435149)
    ·
      refine ⟨22706529463614646650163181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60550745236305724400435149 22706529463614646650163181)
      ·
        refine ⟨8514948548855492493811193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22706529463614646650163181 8514948548855492493811193)
        ·
          refine ⟨6386211411641619370358395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8514948548855492493811193 6386211411641619370358395)
          ·
            refine ⟨9579317117462429055537593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6386211411641619370358395 9579317117462429055537593)
            ·
              refine ⟨7184487838096821791653195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9579317117462429055537593 7184487838096821791653195)
              ·
                refine ⟨10776731757145232687479793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7184487838096821791653195 10776731757145232687479793)
                ·
                  refine ⟨8082548817858924515609845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10776731757145232687479793 8082548817858924515609845)
                  ·
                    refine ⟨757738951674274173338423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8082548817858924515609845 757738951674274173338423)
                    ·
                      rfl

theorem cell22_2213537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_2213537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213537 prefixEnd_2213537 := by exact prefixLift 2213537
  have htrace : WordTrace (prefixWord ++ tailWord_2213537) baseStart_2213537 baseEnd_2213537 := by
    simpa [prefixWord, tailWord_2213537, baseEnd_2213537] using wordTrace_append hprefix tailTrace_2213537
  have hstable : (prefixWord ++ tailWord_2213537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213537).length < 2 ^ (prefixWord ++ tailWord_2213537).sum := by decide
  have hdescent : baseEnd_2213537 < baseStart_2213537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213552 : List Nat := [2, 1, 1, 1, 2, 1, 5, 4, 1, 4]
def baseStart_2213552 : Nat := 118140960795 + 2213552 * 2 ^ 59
def prefixEnd_2213552 : Nat := 4983230072969 + 3 ^ 40 * 2213552 * 2
def baseEnd_2213552 : Nat := 757744086480819134213377

theorem tailTrace_2213552 : CollatzResearch.WordTrace tailWord_2213552 prefixEnd_2213552 757744086480819134213377 := by
  unfold tailWord_2213552
  simp only [CollatzResearch.WordTrace]
  refine ⟨40367437038343311714521455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53823249384457748952695273 40367437038343311714521455)
  ·
    refine ⟨60551155557514967571782183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40367437038343311714521455 60551155557514967571782183)
    ·
      refine ⟨90826733336272451357673275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60551155557514967571782183 90826733336272451357673275)
      ·
        refine ⟨136240100004408677036509913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90826733336272451357673275 136240100004408677036509913)
        ·
          refine ⟨102180075003306507777382435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136240100004408677036509913 102180075003306507777382435)
          ·
            refine ⟨153270112504959761666073653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102180075003306507777382435 153270112504959761666073653)
            ·
              refine ⟨14369073047339977656194405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 153270112504959761666073653 14369073047339977656194405)
              ·
                refine ⟨2694201196376245810536451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14369073047339977656194405 2694201196376245810536451)
                ·
                  refine ⟨4041301794564368715804677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2694201196376245810536451 4041301794564368715804677)
                  ·
                    refine ⟨757744086480819134213377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4041301794564368715804677 757744086480819134213377)
                    ·
                      rfl

theorem cell22_2213552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 1, 4].length) (baseStart_2213552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213552 prefixEnd_2213552 := by exact prefixLift 2213552
  have htrace : WordTrace (prefixWord ++ tailWord_2213552) baseStart_2213552 baseEnd_2213552 := by
    simpa [prefixWord, tailWord_2213552, baseEnd_2213552] using wordTrace_append hprefix tailTrace_2213552
  have hstable : (prefixWord ++ tailWord_2213552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213552).length < 2 ^ (prefixWord ++ tailWord_2213552).sum := by decide
  have hdescent : baseEnd_2213552 < baseStart_2213552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213590 : List Nat := [5, 2, 1, 3, 1, 2, 2, 1, 5]
def baseStart_2213590 : Nat := 118140960795 + 2213590 * 2 ^ 59
def prefixEnd_2213590 : Nat := 4983230072969 + 3 ^ 40 * 2213590 * 2
def baseEnd_2213590 : Nat := 252585698219133233921087

theorem tailTrace_2213590 : CollatzResearch.WordTrace tailWord_2213590 prefixEnd_2213590 252585698219133233921087 := by
  unfold tailWord_2213590
  simp only [CollatzResearch.WordTrace]
  refine ⟨5046016253159309744932889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53824173367032637279284149 5046016253159309744932889)
  ·
    refine ⟨3784512189869482308699667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5046016253159309744932889 3784512189869482308699667)
    ·
      refine ⟨5676768284804223463049501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3784512189869482308699667 5676768284804223463049501)
      ·
        refine ⟨2128788106801583798643563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5676768284804223463049501 2128788106801583798643563)
        ·
          refine ⟨3193182160202375697965345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2128788106801583798643563 3193182160202375697965345)
          ·
            refine ⟨2394886620151781773474009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3193182160202375697965345 2394886620151781773474009)
            ·
              refine ⟨1796164965113836330105507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2394886620151781773474009 1796164965113836330105507)
              ·
                refine ⟨2694247447670754495158261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1796164965113836330105507 2694247447670754495158261)
                ·
                  refine ⟨252585698219133233921087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2694247447670754495158261 252585698219133233921087)
                  ·
                    rfl

theorem cell22_2213590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_2213590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213590 prefixEnd_2213590 := by exact prefixLift 2213590
  have htrace : WordTrace (prefixWord ++ tailWord_2213590) baseStart_2213590 baseEnd_2213590 := by
    simpa [prefixWord, tailWord_2213590, baseEnd_2213590] using wordTrace_append hprefix tailTrace_2213590
  have hstable : (prefixWord ++ tailWord_2213590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213590).length < 2 ^ (prefixWord ++ tailWord_2213590).sum := by decide
  have hdescent : baseEnd_2213590 < baseStart_2213590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213599 : List Nat := [1, 1, 2, 3, 2, 2, 3, 3, 2, 3]
def baseStart_2213599 : Nat := 118140960795 + 2213599 * 2 ^ 59
def prefixEnd_2213599 : Nat := 4983230072969 + 3 ^ 40 * 2213599 * 2
def baseEnd_2213599 : Nat := 757760175541326678288233

theorem tailTrace_2213599 : CollatzResearch.WordTrace tailWord_2213599 prefixEnd_2213599 757760175541326678288233 := by
  unfold tailWord_2213599
  simp only [CollatzResearch.WordTrace]
  refine ⟨80736588307516350456003851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53824392205010900304002567 80736588307516350456003851)
  ·
    refine ⟨121104882461274525684005777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80736588307516350456003851 121104882461274525684005777)
    ·
      refine ⟨90828661845955894263004333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121104882461274525684005777 90828661845955894263004333)
      ·
        refine ⟨34060748192233460348626625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90828661845955894263004333 34060748192233460348626625)
        ·
          refine ⟨25545561144175095261469969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34060748192233460348626625 25545561144175095261469969)
          ·
            refine ⟨19159170858131321446102477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25545561144175095261469969 19159170858131321446102477)
            ·
              refine ⟨7184689071799245542288429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19159170858131321446102477 7184689071799245542288429)
              ·
                refine ⟨2694258401924717078358161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7184689071799245542288429 2694258401924717078358161)
                ·
                  refine ⟨2020693801443537808768621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2694258401924717078358161 2020693801443537808768621)
                  ·
                    refine ⟨757760175541326678288233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2020693801443537808768621 757760175541326678288233)
                    ·
                      rfl

theorem cell22_2213599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 3].length) (baseStart_2213599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213599 prefixEnd_2213599 := by exact prefixLift 2213599
  have htrace : WordTrace (prefixWord ++ tailWord_2213599) baseStart_2213599 baseEnd_2213599 := by
    simpa [prefixWord, tailWord_2213599, baseEnd_2213599] using wordTrace_append hprefix tailTrace_2213599
  have hstable : (prefixWord ++ tailWord_2213599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213599).length < 2 ^ (prefixWord ++ tailWord_2213599).sum := by decide
  have hdescent : baseEnd_2213599 < baseStart_2213599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213603 : List Nat := [1, 1, 1, 7, 3, 1, 1, 2, 1, 4]
def baseStart_2213603 : Nat := 118140960795 + 2213603 * 2 ^ 59
def prefixEnd_2213603 : Nat := 4983230072969 + 3 ^ 40 * 2213603 * 2
def baseEnd_2213603 : Nat := 757761544823072001188221

theorem tailTrace_2213603 : CollatzResearch.WordTrace tailWord_2213603 prefixEnd_2213603 757761544823072001188221 := by
  unfold tailWord_2213603
  simp only [CollatzResearch.WordTrace]
  refine ⟨80736734199501859139149463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53824489466334572759432975 80736734199501859139149463)
  ·
    refine ⟨121105101299252788708724195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80736734199501859139149463 121105101299252788708724195)
    ·
      refine ⟨181657651948879183063086293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121105101299252788708724195 181657651948879183063086293)
      ·
        refine ⟨4257601217551855853041085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 181657651948879183063086293 4257601217551855853041085)
        ·
          refine ⟨1596600456581945944890407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4257601217551855853041085 1596600456581945944890407)
          ·
            refine ⟨2394900684872918917335611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1596600456581945944890407 2394900684872918917335611)
            ·
              refine ⟨3592351027309378376003417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2394900684872918917335611 3592351027309378376003417)
              ·
                refine ⟨2694263270482033782002563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3592351027309378376003417 2694263270482033782002563)
                ·
                  refine ⟨4041394905723050673003845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2694263270482033782002563 4041394905723050673003845)
                  ·
                    refine ⟨757761544823072001188221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4041394905723050673003845 757761544823072001188221)
                    ·
                      rfl

theorem cell22_2213603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 1, 4].length) (baseStart_2213603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213603 prefixEnd_2213603 := by exact prefixLift 2213603
  have htrace : WordTrace (prefixWord ++ tailWord_2213603) baseStart_2213603 baseEnd_2213603 := by
    simpa [prefixWord, tailWord_2213603, baseEnd_2213603] using wordTrace_append hprefix tailTrace_2213603
  have hstable : (prefixWord ++ tailWord_2213603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213603).length < 2 ^ (prefixWord ++ tailWord_2213603).sum := by decide
  have hdescent : baseEnd_2213603 < baseStart_2213603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213614 : List Nat := [4, 1, 2, 1, 1, 2, 4, 1, 2, 4]
def baseStart_2213614 : Nat := 118140960795 + 2213614 * 2 ^ 59
def prefixEnd_2213614 : Nat := 4983230072969 + 3 ^ 40 * 2213614 * 2
def baseEnd_2213614 : Nat := 757765310347871639163187

theorem tailTrace_2213614 : CollatzResearch.WordTrace tailWord_2213614 prefixEnd_2213614 757765310347871639163187 := by
  unfold tailWord_2213614
  simp only [CollatzResearch.WordTrace]
  refine ⟨10092141925307751002224987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53824756934974672011866597 10092141925307751002224987)
  ·
    refine ⟨15138212887961626503337481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10092141925307751002224987 15138212887961626503337481)
    ·
      refine ⟨11353659665971219877503111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15138212887961626503337481 11353659665971219877503111)
      ·
        refine ⟨17030489498956829816254667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11353659665971219877503111 17030489498956829816254667)
        ·
          refine ⟨25545734248435244724382001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17030489498956829816254667 25545734248435244724382001)
          ·
            refine ⟨19159300686326433543286501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25545734248435244724382001 19159300686326433543286501)
            ·
              refine ⟨3592368878686206289366219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19159300686326433543286501 3592368878686206289366219)
              ·
                refine ⟨5388553318029309434049329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3592368878686206289366219 5388553318029309434049329)
                ·
                  refine ⟨4041414988521982075536997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5388553318029309434049329 4041414988521982075536997)
                  ·
                    refine ⟨757765310347871639163187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4041414988521982075536997 757765310347871639163187)
                    ·
                      rfl

theorem cell22_2213614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_2213614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213614 prefixEnd_2213614 := by exact prefixLift 2213614
  have htrace : WordTrace (prefixWord ++ tailWord_2213614) baseStart_2213614 baseEnd_2213614 := by
    simpa [prefixWord, tailWord_2213614, baseEnd_2213614] using wordTrace_append hprefix tailTrace_2213614
  have hstable : (prefixWord ++ tailWord_2213614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213614).length < 2 ^ (prefixWord ++ tailWord_2213614).sum := by decide
  have hdescent : baseEnd_2213614 < baseStart_2213614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213620 : List Nat := [2, 6, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_2213620 : Nat := 118140960795 + 2213620 * 2 ^ 59
def prefixEnd_2213620 : Nat := 4983230072969 + 3 ^ 40 * 2213620 * 2
def baseEnd_2213620 : Nat := 757767364270489623513169

theorem tailTrace_2213620 : CollatzResearch.WordTrace tailWord_2213620 prefixEnd_2213620 757767364270489623513169 := by
  unfold tailWord_2213620
  simp only [CollatzResearch.WordTrace]
  refine ⟨40368677120220135521259157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53824902826960180695012209 40368677120220135521259157)
  ·
    refine ⟨1892281740010318852559023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40368677120220135521259157 1892281740010318852559023)
    ·
      refine ⟨2838422610015478278838535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1892281740010318852559023 2838422610015478278838535)
      ·
        refine ⟨4257633915023217418257803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2838422610015478278838535 4257633915023217418257803)
        ·
          refine ⟨6386450872534826127386705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4257633915023217418257803 6386450872534826127386705)
          ·
            refine ⟨4789838154401119595540029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6386450872534826127386705 4789838154401119595540029)
            ·
              refine ⟨1796189307900419848327511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4789838154401119595540029 1796189307900419848327511)
              ·
                refine ⟨2694283961850629772491267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1796189307900419848327511 2694283961850629772491267)
                ·
                  refine ⟨4041425942775944658736901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2694283961850629772491267 4041425942775944658736901)
                  ·
                    refine ⟨757767364270489623513169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4041425942775944658736901 757767364270489623513169)
                    ·
                      rfl

theorem cell22_2213620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_2213620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213620 prefixEnd_2213620 := by exact prefixLift 2213620
  have htrace : WordTrace (prefixWord ++ tailWord_2213620) baseStart_2213620 baseEnd_2213620 := by
    simpa [prefixWord, tailWord_2213620, baseEnd_2213620] using wordTrace_append hprefix tailTrace_2213620
  have hstable : (prefixWord ++ tailWord_2213620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213620).length < 2 ^ (prefixWord ++ tailWord_2213620).sum := by decide
  have hdescent : baseEnd_2213620 < baseStart_2213620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213627 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 7, 3]
def baseStart_2213627 : Nat := 118140960795 + 2213627 * 2 ^ 59
def prefixEnd_2213627 : Nat := 4983230072969 + 3 ^ 40 * 2213627 * 2
def baseEnd_2213627 : Nat := 757769760513543938588147

theorem tailTrace_2213627 : CollatzResearch.WordTrace tailWord_2213627 prefixEnd_2213627 757769760513543938588147 := by
  unfold tailWord_2213627
  simp only [CollatzResearch.WordTrace]
  refine ⟨80737609551414911238023135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53825073034276607492015423 80737609551414911238023135)
  ·
    refine ⟨121106414327122366857034703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80737609551414911238023135 121106414327122366857034703)
    ·
      refine ⟨181659621490683550285552055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121106414327122366857034703 181659621490683550285552055)
      ·
        refine ⟨272489432236025325428328083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181659621490683550285552055 272489432236025325428328083)
        ·
          refine ⟨408734148354037988142492125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272489432236025325428328083 408734148354037988142492125)
          ·
            refine ⟨153275305632764245553434547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 408734148354037988142492125 153275305632764245553434547)
            ·
              refine ⟨229912958449146368330151821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153275305632764245553434547 229912958449146368330151821)
              ·
                refine ⟨86217359418429888123806933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 229912958449146368330151821 86217359418429888123806933)
                ·
                  refine ⟨2020719361369450502901725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 86217359418429888123806933 2020719361369450502901725)
                  ·
                    refine ⟨757769760513543938588147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2020719361369450502901725 757769760513543938588147)
                    ·
                      rfl

theorem cell22_2213627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 3].length) (baseStart_2213627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213627 prefixEnd_2213627 := by exact prefixLift 2213627
  have htrace : WordTrace (prefixWord ++ tailWord_2213627) baseStart_2213627 baseEnd_2213627 := by
    simpa [prefixWord, tailWord_2213627, baseEnd_2213627] using wordTrace_append hprefix tailTrace_2213627
  have hstable : (prefixWord ++ tailWord_2213627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213627).length < 2 ^ (prefixWord ++ tailWord_2213627).sum := by decide
  have hdescent : baseEnd_2213627 < baseStart_2213627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213642 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 2, 6]
def baseStart_2213642 : Nat := 118140960795 + 2213642 * 2 ^ 59
def prefixEnd_2213642 : Nat := 4983230072969 + 3 ^ 40 * 2213642 * 2
def baseEnd_2213642 : Nat := 757774895320088899463101

theorem tailTrace_2213642 : CollatzResearch.WordTrace tailWord_2213642 prefixEnd_2213642 757774895320088899463101 := by
  unfold tailWord_2213642
  simp only [CollatzResearch.WordTrace]
  refine ⟨20184539161590142199954795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53825437764240379199879453 20184539161590142199954795)
  ·
    refine ⟨30276808742385213299932193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20184539161590142199954795 30276808742385213299932193)
    ·
      refine ⟨22707606556788909974949145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30276808742385213299932193 22707606556788909974949145)
      ·
        refine ⟨17030704917591682481211859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22707606556788909974949145 17030704917591682481211859)
        ·
          refine ⟨25546057376387523721817789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17030704917591682481211859 25546057376387523721817789)
          ·
            refine ⟨9579771516145321395681671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25546057376387523721817789 9579771516145321395681671)
            ·
              refine ⟨14369657274217982093522507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9579771516145321395681671 14369657274217982093522507)
              ·
                refine ⟨21554485911326973140283761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14369657274217982093522507 21554485911326973140283761)
                ·
                  refine ⟨16165864433495229855212821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21554485911326973140283761 16165864433495229855212821)
                  ·
                    refine ⟨757774895320088899463101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16165864433495229855212821 757774895320088899463101)
                    ·
                      rfl

theorem cell22_2213642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_2213642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213642 prefixEnd_2213642 := by exact prefixLift 2213642
  have htrace : WordTrace (prefixWord ++ tailWord_2213642) baseStart_2213642 baseEnd_2213642 := by
    simpa [prefixWord, tailWord_2213642, baseEnd_2213642] using wordTrace_append hprefix tailTrace_2213642
  have hstable : (prefixWord ++ tailWord_2213642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213642).length < 2 ^ (prefixWord ++ tailWord_2213642).sum := by decide
  have hdescent : baseEnd_2213642 < baseStart_2213642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213687 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 5, 4]
def baseStart_2213687 : Nat := 118140960795 + 2213687 * 2 ^ 59
def prefixEnd_2213687 : Nat := 4983230072969 + 3 ^ 40 * 2213687 * 2
def baseEnd_2213687 : Nat := 757790299739723782087963

theorem tailTrace_2213687 : CollatzResearch.WordTrace tailWord_2213687 prefixEnd_2213687 757790299739723782087963 := by
  unfold tailWord_2213687
  simp only [CollatzResearch.WordTrace]
  refine ⟨80739797931197541485207315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53826531954131694323471543 80739797931197541485207315)
  ·
    refine ⟨121109696896796312227810973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80739797931197541485207315 121109696896796312227810973)
    ·
      refine ⟨45416136336298617085429115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121109696896796312227810973 45416136336298617085429115)
      ·
        refine ⟨68124204504447925628143673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45416136336298617085429115 68124204504447925628143673)
        ·
          refine ⟨51093153378335944221107755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68124204504447925628143673 51093153378335944221107755)
          ·
            refine ⟨76639730067503916331661633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51093153378335944221107755 76639730067503916331661633)
            ·
              refine ⟨57479797550627937248746225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76639730067503916331661633 57479797550627937248746225)
              ·
                refine ⟨43109848162970952936559669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57479797550627937248746225 43109848162970952936559669)
                ·
                  refine ⟨4041548265278526837802469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43109848162970952936559669 4041548265278526837802469)
                  ·
                    refine ⟨757790299739723782087963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4041548265278526837802469 757790299739723782087963)
                    ·
                      rfl

theorem cell22_2213687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_2213687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213687 prefixEnd_2213687 := by exact prefixLift 2213687
  have htrace : WordTrace (prefixWord ++ tailWord_2213687) baseStart_2213687 baseEnd_2213687 := by
    simpa [prefixWord, tailWord_2213687, baseEnd_2213687] using wordTrace_append hprefix tailTrace_2213687
  have hstable : (prefixWord ++ tailWord_2213687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213687).length < 2 ^ (prefixWord ++ tailWord_2213687).sum := by decide
  have hdescent : baseEnd_2213687 < baseStart_2213687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213768 : List Nat := [2, 1, 3, 3, 3, 1, 1, 3, 2, 3]
def baseStart_2213768 : Nat := 118140960795 + 2213768 * 2 ^ 59
def prefixEnd_2213768 : Nat := 4983230072969 + 3 ^ 40 * 2213768 * 2
def baseEnd_2213768 : Nat := 757818027695066570812715

theorem tailTrace_2213768 : CollatzResearch.WordTrace tailWord_2213768 prefixEnd_2213768 757818027695066570812715 := by
  unfold tailWord_2213768
  simp only [CollatzResearch.WordTrace]
  refine ⟨40371376121952046159452979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53828501495936061545937305 40371376121952046159452979)
  ·
    refine ⟨60557064182928069239179469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40371376121952046159452979 60557064182928069239179469)
    ·
      refine ⟨22708899068598025964692301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60557064182928069239179469 22708899068598025964692301)
      ·
        refine ⟨8515837150724259736759613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22708899068598025964692301 8515837150724259736759613)
        ·
          refine ⟨3193438931521597401284855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8515837150724259736759613 3193438931521597401284855)
          ·
            refine ⟨4790158397282396101927283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3193438931521597401284855 4790158397282396101927283)
            ·
              refine ⟨7185237595923594152890925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4790158397282396101927283 7185237595923594152890925)
              ·
                refine ⟨2694464098471347807334097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7185237595923594152890925 2694464098471347807334097)
                ·
                  refine ⟨2020848073853510855500573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2694464098471347807334097 2020848073853510855500573)
                  ·
                    refine ⟨757818027695066570812715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2020848073853510855500573 757818027695066570812715)
                    ·
                      rfl

theorem cell22_2213768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_2213768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213768 prefixEnd_2213768 := by exact prefixLift 2213768
  have htrace : WordTrace (prefixWord ++ tailWord_2213768) baseStart_2213768 baseEnd_2213768 := by
    simpa [prefixWord, tailWord_2213768, baseEnd_2213768] using wordTrace_append hprefix tailTrace_2213768
  have hstable : (prefixWord ++ tailWord_2213768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213768).length < 2 ^ (prefixWord ++ tailWord_2213768).sum := by decide
  have hdescent : baseEnd_2213768 < baseStart_2213768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213824 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 2, 5]
def baseStart_2213824 : Nat := 118140960795 + 2213824 * 2 ^ 59
def prefixEnd_2213824 : Nat := 4983230072969 + 3 ^ 40 * 2213824 * 2
def baseEnd_2213824 : Nat := 757837197639501091412543

theorem tailTrace_2213824 : CollatzResearch.WordTrace tailWord_2213824 prefixEnd_2213824 757837197639501091412543 := by
  unfold tailWord_2213824
  simp only [CollatzResearch.WordTrace]
  refine ⟨40372397365850606941472263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53829863154467475921963017 40372397365850606941472263)
  ·
    refine ⟨60558596048775910412208395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40372397365850606941472263 60558596048775910412208395)
    ·
      refine ⟨90837894073163865618312593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60558596048775910412208395 90837894073163865618312593)
      ·
        refine ⟨68128420554872899213734445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90837894073163865618312593 68128420554872899213734445)
        ·
          refine ⟨25548157708077337205150417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68128420554872899213734445 25548157708077337205150417)
          ·
            refine ⟨19161118281058002903862813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25548157708077337205150417 19161118281058002903862813)
            ·
              refine ⟨7185419355396751088948555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19161118281058002903862813 7185419355396751088948555)
              ·
                refine ⟨10778129033095126633422833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7185419355396751088948555 10778129033095126633422833)
                ·
                  refine ⟨8083596774821344975067125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10778129033095126633422833 8083596774821344975067125)
                  ·
                    refine ⟨757837197639501091412543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8083596774821344975067125 757837197639501091412543)
                    ·
                      rfl

theorem cell22_2213824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 2, 5].length) (baseStart_2213824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213824 prefixEnd_2213824 := by exact prefixLift 2213824
  have htrace : WordTrace (prefixWord ++ tailWord_2213824) baseStart_2213824 baseEnd_2213824 := by
    simpa [prefixWord, tailWord_2213824, baseEnd_2213824] using wordTrace_append hprefix tailTrace_2213824
  have hstable : (prefixWord ++ tailWord_2213824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213824).length < 2 ^ (prefixWord ++ tailWord_2213824).sum := by decide
  have hdescent : baseEnd_2213824 < baseStart_2213824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213839 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 3, 4]
def baseStart_2213839 : Nat := 118140960795 + 2213839 * 2 ^ 59
def prefixEnd_2213839 : Nat := 4983230072969 + 3 ^ 40 * 2213839 * 2
def baseEnd_2213839 : Nat := 757842332446046052287497

theorem tailTrace_2213839 : CollatzResearch.WordTrace tailWord_2213839 prefixEnd_2213839 757842332446046052287497 := by
  unfold tailWord_2213839
  simp only [CollatzResearch.WordTrace]
  refine ⟨80745341826646871444740571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53830227884431247629827047 80745341826646871444740571)
  ·
    refine ⟨121118012739970307167110857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80745341826646871444740571 121118012739970307167110857)
    ·
      refine ⟨90838509554977730375333143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121118012739970307167110857 90838509554977730375333143)
      ·
        refine ⟨136257764332466595562999715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90838509554977730375333143 136257764332466595562999715)
        ·
          refine ⟨204386646498699893344499573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136257764332466595562999715 204386646498699893344499573)
          ·
            refine ⟨19161248109253115001046835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 204386646498699893344499573 19161248109253115001046835)
            ·
              refine ⟨28741872163879672501570253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19161248109253115001046835 28741872163879672501570253)
              ·
                refine ⟨10778202061454877188088845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28741872163879672501570253 10778202061454877188088845)
                ·
                  refine ⟨4041825773045578945533317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10778202061454877188088845 4041825773045578945533317)
                  ·
                    refine ⟨757842332446046052287497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4041825773045578945533317 757842332446046052287497)
                    ·
                      rfl

theorem cell22_2213839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 4].length) (baseStart_2213839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213839 prefixEnd_2213839 := by exact prefixLift 2213839
  have htrace : WordTrace (prefixWord ++ tailWord_2213839) baseStart_2213839 baseEnd_2213839 := by
    simpa [prefixWord, tailWord_2213839, baseEnd_2213839] using wordTrace_append hprefix tailTrace_2213839
  have hstable : (prefixWord ++ tailWord_2213839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213839).length < 2 ^ (prefixWord ++ tailWord_2213839).sum := by decide
  have hdescent : baseEnd_2213839 < baseStart_2213839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213871 : List Nat := [1, 1, 2, 1, 4, 2, 1, 6, 4]
def baseStart_2213871 : Nat := 118140960795 + 2213871 * 2 ^ 59
def prefixEnd_2213871 : Nat := 4983230072969 + 3 ^ 40 * 2213871 * 2
def baseEnd_2213871 : Nat := 252617762233336211829133

theorem tailTrace_2213871 : CollatzResearch.WordTrace tailWord_2213871 prefixEnd_2213871 252617762233336211829133 := by
  unfold tailWord_2213871
  simp only [CollatzResearch.WordTrace]
  refine ⟨80746508962530940909905467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53831005975020627273270311 80746508962530940909905467)
  ·
    refine ⟨121119763443796411364858201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80746508962530940909905467 121119763443796411364858201)
    ·
      refine ⟨90839822582847308523643651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121119763443796411364858201 90839822582847308523643651)
      ·
        refine ⟨136259733874270962785465477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90839822582847308523643651 136259733874270962785465477)
        ·
          refine ⟨25548700101425805522274777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136259733874270962785465477 25548700101425805522274777)
          ·
            refine ⟨19161525076069354141706083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25548700101425805522274777 19161525076069354141706083)
            ·
              refine ⟨28742287614104031212559125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19161525076069354141706083 28742287614104031212559125)
              ·
                refine ⟨1347294731911126463088709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28742287614104031212559125 1347294731911126463088709)
                ·
                  refine ⟨252617762233336211829133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1347294731911126463088709 252617762233336211829133)
                  ·
                    rfl

theorem cell22_2213871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 4].length) (baseStart_2213871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213871 prefixEnd_2213871 := by exact prefixLift 2213871
  have htrace : WordTrace (prefixWord ++ tailWord_2213871) baseStart_2213871 baseEnd_2213871 := by
    simpa [prefixWord, tailWord_2213871, baseEnd_2213871] using wordTrace_append hprefix tailTrace_2213871
  have hstable : (prefixWord ++ tailWord_2213871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213871).length < 2 ^ (prefixWord ++ tailWord_2213871).sum := by decide
  have hdescent : baseEnd_2213871 < baseStart_2213871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213884 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 3, 6]
def baseStart_2213884 : Nat := 118140960795 + 2213884 * 2 ^ 59
def prefixEnd_2213884 : Nat := 4983230072969 + 3 ^ 40 * 2213884 * 2
def baseEnd_2213884 : Nat := 757857736865680934912359

theorem tailTrace_2213884 : CollatzResearch.WordTrace tailWord_2213884 prefixEnd_2213884 757857736865680934912359 := by
  unfold tailWord_2213884
  simp only [CollatzResearch.WordTrace]
  refine ⟨40373491555741922065064353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53831322074322562753419137 40373491555741922065064353)
  ·
    refine ⟨30280118666806441548798265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40373491555741922065064353 30280118666806441548798265)
    ·
      refine ⟨22710089000104831161598699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30280118666806441548798265 22710089000104831161598699)
      ·
        refine ⟨34065133500157246742398049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22710089000104831161598699 34065133500157246742398049)
        ·
          refine ⟨25548850125117935056798537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34065133500157246742398049 25548850125117935056798537)
          ·
            refine ⟨19161637593838451292598903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25548850125117935056798537 19161637593838451292598903)
            ·
              refine ⟨28742456390757676938898355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19161637593838451292598903 28742456390757676938898355)
              ·
                refine ⟨43113684586136515408347533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28742456390757676938898355 43113684586136515408347533)
                ·
                  refine ⟨16167631719801193278130325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43113684586136515408347533 16167631719801193278130325)
                  ·
                    refine ⟨757857736865680934912359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16167631719801193278130325 757857736865680934912359)
                    ·
                      rfl

theorem cell22_2213884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_2213884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213884 prefixEnd_2213884 := by exact prefixLift 2213884
  have htrace : WordTrace (prefixWord ++ tailWord_2213884) baseStart_2213884 baseEnd_2213884 := by
    simpa [prefixWord, tailWord_2213884, baseEnd_2213884] using wordTrace_append hprefix tailTrace_2213884
  have hstable : (prefixWord ++ tailWord_2213884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213884).length < 2 ^ (prefixWord ++ tailWord_2213884).sum := by decide
  have hdescent : baseEnd_2213884 < baseStart_2213884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213899 : List Nat := [1, 1, 1, 1, 6, 1, 3, 8]
def baseStart_2213899 : Nat := 118140960795 + 2213899 * 2 ^ 59
def prefixEnd_2213899 : Nat := 4983230072969 + 3 ^ 40 * 2213899 * 2
def baseEnd_2213899 : Nat := 84206985741358432865257

theorem tailTrace_2213899 : CollatzResearch.WordTrace tailWord_2213899 prefixEnd_2213899 84206985741358432865257 := by
  unfold tailWord_2213899
  simp only [CollatzResearch.WordTrace]
  refine ⟨80747530206429501691924751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53831686804286334461283167 80747530206429501691924751)
  ·
    refine ⟨121121295309644252537887127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80747530206429501691924751 121121295309644252537887127)
    ·
      refine ⟨181681942964466378806830691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121121295309644252537887127 181681942964466378806830691)
      ·
        refine ⟨272522914446699568210246037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181681942964466378806830691 272522914446699568210246037)
        ·
          refine ⟨12774511614689042259855283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 272522914446699568210246037 12774511614689042259855283)
          ·
            refine ⟨19161767422033563389782925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12774511614689042259855283 19161767422033563389782925)
            ·
              refine ⟨7185662783262586271168597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19161767422033563389782925 7185662783262586271168597)
              ·
                refine ⟨84206985741358432865257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7185662783262586271168597 84206985741358432865257)
                ·
                  rfl

theorem cell22_2213899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 8].length) (baseStart_2213899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213899 prefixEnd_2213899 := by exact prefixLift 2213899
  have htrace : WordTrace (prefixWord ++ tailWord_2213899) baseStart_2213899 baseEnd_2213899 := by
    simpa [prefixWord, tailWord_2213899, baseEnd_2213899] using wordTrace_append hprefix tailTrace_2213899
  have hstable : (prefixWord ++ tailWord_2213899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213899).length < 2 ^ (prefixWord ++ tailWord_2213899).sum := by decide
  have hdescent : baseEnd_2213899 < baseStart_2213899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213916 : List Nat := [2, 2, 3, 1, 3, 3, 8]
def baseStart_2213916 : Nat := 118140960795 + 2213916 * 2 ^ 59
def prefixEnd_2213916 : Nat := 4983230072969 + 3 ^ 40 * 2213916 * 2
def baseEnd_2213916 : Nat := 28069210782209019189343

theorem tailTrace_2213916 : CollatzResearch.WordTrace tailWord_2213916 prefixEnd_2213916 28069210782209019189343 := by
  unfold tailWord_2213916
  simp only [CollatzResearch.WordTrace]
  refine ⟨40374075123683956797646801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53832100164911942396862401 40374075123683956797646801)
  ·
    refine ⟨30280556342762967598235101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40374075123683956797646801 30280556342762967598235101)
    ·
      refine ⟨11355208628536112849338163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30280556342762967598235101 11355208628536112849338163)
      ·
        refine ⟨17032812942804169274007245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11355208628536112849338163 17032812942804169274007245)
        ·
          refine ⟨6387304853551563477752717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17032812942804169274007245 6387304853551563477752717)
          ·
            refine ⟨2395239320081836304157269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6387304853551563477752717 2395239320081836304157269)
            ·
              refine ⟨28069210782209019189343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2395239320081836304157269 28069210782209019189343)
              ·
                rfl

theorem cell22_2213916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 8].length) (baseStart_2213916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213916 prefixEnd_2213916 := by exact prefixLift 2213916
  have htrace : WordTrace (prefixWord ++ tailWord_2213916) baseStart_2213916 baseEnd_2213916 := by
    simpa [prefixWord, tailWord_2213916, baseEnd_2213916] using wordTrace_append hprefix tailTrace_2213916
  have hstable : (prefixWord ++ tailWord_2213916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213916).length < 2 ^ (prefixWord ++ tailWord_2213916).sum := by decide
  have hdescent : baseEnd_2213916 < baseStart_2213916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213931 : List Nat := [1, 1, 1, 1, 2, 1, 4, 5, 3, 3]
def baseStart_2213931 : Nat := 118140960795 + 2213931 * 2 ^ 59
def prefixEnd_2213931 : Nat := 4983230072969 + 3 ^ 40 * 2213931 * 2
def baseEnd_2213931 : Nat := 757873825926188478987215

theorem tailTrace_2213931 : CollatzResearch.WordTrace tailWord_2213931 prefixEnd_2213931 757873825926188478987215 := by
  unfold tailWord_2213931
  simp only [CollatzResearch.WordTrace]
  refine ⟨80748697342313571157089647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53832464894875714104726431 80748697342313571157089647)
  ·
    refine ⟨121123046013470356735634471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80748697342313571157089647 121123046013470356735634471)
    ·
      refine ⟨181684569020205535103451707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121123046013470356735634471 181684569020205535103451707)
      ·
        refine ⟨272526853530308302655177561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181684569020205535103451707 272526853530308302655177561)
        ·
          refine ⟨204395140147731226991383171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272526853530308302655177561 204395140147731226991383171)
          ·
            refine ⟨306592710221596840487074757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204395140147731226991383171 306592710221596840487074757)
            ·
              refine ⟨57486133166549407591326517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 306592710221596840487074757 57486133166549407591326517)
              ·
                refine ⟨5389324984364006961686861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57486133166549407591326517 5389324984364006961686861)
                ·
                  refine ⟨2020996869136502610632573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5389324984364006961686861 2020996869136502610632573)
                  ·
                    refine ⟨757873825926188478987215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2020996869136502610632573 757873825926188478987215)
                    ·
                      rfl

theorem cell22_2213931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 3].length) (baseStart_2213931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213931 prefixEnd_2213931 := by exact prefixLift 2213931
  have htrace : WordTrace (prefixWord ++ tailWord_2213931) baseStart_2213931 baseEnd_2213931 := by
    simpa [prefixWord, tailWord_2213931, baseEnd_2213931] using wordTrace_append hprefix tailTrace_2213931
  have hstable : (prefixWord ++ tailWord_2213931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213931).length < 2 ^ (prefixWord ++ tailWord_2213931).sum := by decide
  have hdescent : baseEnd_2213931 < baseStart_2213931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213991 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 5, 4]
def baseStart_2213991 : Nat := 118140960795 + 2213991 * 2 ^ 59
def prefixEnd_2213991 : Nat := 4983230072969 + 3 ^ 40 * 2213991 * 2
def baseEnd_2213991 : Nat := 757894365152368322487031

theorem tailTrace_2213991 : CollatzResearch.WordTrace tailWord_2213991 prefixEnd_2213991 757894365152368322487031 := by
  unfold tailWord_2213991
  simp only [CollatzResearch.WordTrace]
  refine ⟨80750885722096201404273827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53833923814730800936182551 80750885722096201404273827)
  ·
    refine ⟨121126328583144302106410741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80750885722096201404273827 121126328583144302106410741)
    ·
      refine ⟨11355593304669778322476007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121126328583144302106410741 11355593304669778322476007)
      ·
        refine ⟨17033389957004667483714011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11355593304669778322476007 17033389957004667483714011)
        ·
          refine ⟨25550084935507001225571017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17033389957004667483714011 25550084935507001225571017)
          ·
            refine ⟨19162563701630250919178263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25550084935507001225571017 19162563701630250919178263)
            ·
              refine ⟨28743845552445376378767395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19162563701630250919178263 28743845552445376378767395)
              ·
                refine ⟨43115768328668064568151093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28743845552445376378767395 43115768328668064568151093)
                ·
                  refine ⟨4042103280812631053264165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43115768328668064568151093 4042103280812631053264165)
                  ·
                    refine ⟨757894365152368322487031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4042103280812631053264165 757894365152368322487031)
                    ·
                      rfl

theorem cell22_2213991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_2213991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213991 prefixEnd_2213991 := by exact prefixLift 2213991
  have htrace : WordTrace (prefixWord ++ tailWord_2213991) baseStart_2213991 baseEnd_2213991 := by
    simpa [prefixWord, tailWord_2213991, baseEnd_2213991] using wordTrace_append hprefix tailTrace_2213991
  have hstable : (prefixWord ++ tailWord_2213991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213991).length < 2 ^ (prefixWord ++ tailWord_2213991).sum := by decide
  have hdescent : baseEnd_2213991 < baseStart_2213991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214023 : List Nat := [1, 1, 4, 2, 1, 1, 3, 5, 4]
def baseStart_2214023 : Nat := 118140960795 + 2214023 * 2 ^ 59
def prefixEnd_2214023 : Nat := 4983230072969 + 3 ^ 40 * 2214023 * 2
def baseEnd_2214023 : Nat := 252635106468776968562311

theorem tailTrace_2214023 : CollatzResearch.WordTrace tailWord_2214023 prefixEnd_2214023 252635106468776968562311 := by
  unfold tailWord_2214023
  simp only [CollatzResearch.WordTrace]
  refine ⟨80752052857980270869438723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53834701905320180579625815 80752052857980270869438723)
  ·
    refine ⟨121128079286970406304158085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80752052857980270869438723 121128079286970406304158085)
    ·
      refine ⟨22711514866306951182029641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121128079286970406304158085 22711514866306951182029641)
      ·
        refine ⟨17033636149730213386522231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22711514866306951182029641 17033636149730213386522231)
        ·
          refine ⟨25550454224595320079783347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17033636149730213386522231 25550454224595320079783347)
          ·
            refine ⟨38325681336892980119675021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25550454224595320079783347 38325681336892980119675021)
            ·
              refine ⟨14372130501334867544878133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38325681336892980119675021 14372130501334867544878133)
              ·
                refine ⟨1347387234500143832332325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14372130501334867544878133 1347387234500143832332325)
                ·
                  refine ⟨252635106468776968562311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1347387234500143832332325 252635106468776968562311)
                  ·
                    rfl

theorem cell22_2214023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 4].length) (baseStart_2214023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214023 prefixEnd_2214023 := by exact prefixLift 2214023
  have htrace : WordTrace (prefixWord ++ tailWord_2214023) baseStart_2214023 baseEnd_2214023 := by
    simpa [prefixWord, tailWord_2214023, baseEnd_2214023] using wordTrace_append hprefix tailTrace_2214023
  have hstable : (prefixWord ++ tailWord_2214023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214023).length < 2 ^ (prefixWord ++ tailWord_2214023).sum := by decide
  have hdescent : baseEnd_2214023 < baseStart_2214023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214066 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 2, 7]
def baseStart_2214066 : Nat := 118140960795 + 2214066 * 2 ^ 59
def prefixEnd_2214066 : Nat := 4983230072969 + 3 ^ 40 * 2214066 * 2
def baseEnd_2214066 : Nat := 757920039185093126861801

theorem tailTrace_2214066 : CollatzResearch.WordTrace tailWord_2214066 prefixEnd_2214066 757920039185093126861801 := by
  unfold tailWord_2214066
  simp only [CollatzResearch.WordTrace]
  refine ⟨20188405299206122303313513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53835747464549659475502701 20188405299206122303313513)
  ·
    refine ⟨15141303974404591727485135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20188405299206122303313513 15141303974404591727485135)
    ·
      refine ⟨22711955961606887591227703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15141303974404591727485135 22711955961606887591227703)
      ·
        refine ⟨34067933942410331386841555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22711955961606887591227703 34067933942410331386841555)
        ·
          refine ⟨51101900913615497080262333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34067933942410331386841555 51101900913615497080262333)
          ·
            refine ⟨19163212842605811405098375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51101900913615497080262333 19163212842605811405098375)
            ·
              refine ⟨28744819263908717107647563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19163212842605811405098375 28744819263908717107647563)
              ·
                refine ⟨43117228895863075661471345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28744819263908717107647563 43117228895863075661471345)
                ·
                  refine ⟨32337921671897306746103509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43117228895863075661471345 32337921671897306746103509)
                  ·
                    refine ⟨757920039185093126861801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32337921671897306746103509 757920039185093126861801)
                    ·
                      rfl

theorem cell22_2214066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_2214066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214066 prefixEnd_2214066 := by exact prefixLift 2214066
  have htrace : WordTrace (prefixWord ++ tailWord_2214066) baseStart_2214066 baseEnd_2214066 := by
    simpa [prefixWord, tailWord_2214066, baseEnd_2214066] using wordTrace_append hprefix tailTrace_2214066
  have hstable : (prefixWord ++ tailWord_2214066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214066).length < 2 ^ (prefixWord ++ tailWord_2214066).sum := by decide
  have hdescent : baseEnd_2214066 < baseStart_2214066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214111 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 1, 7]
def baseStart_2214111 : Nat := 118140960795 + 2214111 * 2 ^ 59
def prefixEnd_2214111 : Nat := 4983230072969 + 3 ^ 40 * 2214111 * 2
def baseEnd_2214111 : Nat := 757935443604728009486663

theorem tailTrace_2214111 : CollatzResearch.WordTrace tailWord_2214111 prefixEnd_2214111 757935443604728009486663 := by
  unfold tailWord_2214111
  simp only [CollatzResearch.WordTrace]
  refine ⟨80755262481661461898642187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53836841654440974599094791 80755262481661461898642187)
  ·
    refine ⟨121132893722492192847963281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80755262481661461898642187 121132893722492192847963281)
    ·
      refine ⟨90849670291869144635972461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121132893722492192847963281 90849670291869144635972461)
      ·
        refine ⟨34068626359450929238489673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90849670291869144635972461 34068626359450929238489673)
        ·
          refine ⟨25551469769588196928867255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34068626359450929238489673 25551469769588196928867255)
          ·
            refine ⟨38327204654382295393300883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25551469769588196928867255 38327204654382295393300883)
            ·
              refine ⟨57490806981573443089951325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38327204654382295393300883 57490806981573443089951325)
              ·
                refine ⟨21559052618090041158731747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57490806981573443089951325 21559052618090041158731747)
                ·
                  refine ⟨32338578927135061738097621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21559052618090041158731747 32338578927135061738097621)
                  ·
                    refine ⟨757935443604728009486663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32338578927135061738097621 757935443604728009486663)
                    ·
                      rfl

theorem cell22_2214111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_2214111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214111 prefixEnd_2214111 := by exact prefixLift 2214111
  have htrace : WordTrace (prefixWord ++ tailWord_2214111) baseStart_2214111 baseEnd_2214111 := by
    simpa [prefixWord, tailWord_2214111, baseEnd_2214111] using wordTrace_append hprefix tailTrace_2214111
  have hstable : (prefixWord ++ tailWord_2214111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214111).length < 2 ^ (prefixWord ++ tailWord_2214111).sum := by decide
  have hdescent : baseEnd_2214111 < baseStart_2214111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214113 : List Nat := [1, 2, 3, 1, 3, 1, 3, 3, 5]
def baseStart_2214113 : Nat := 118140960795 + 2214113 * 2 ^ 59
def prefixEnd_2214113 : Nat := 4983230072969 + 3 ^ 40 * 2214113 * 2
def baseEnd_2214113 : Nat := 252645376081866890312219

theorem tailTrace_2214113 : CollatzResearch.WordTrace tailWord_2214113 prefixEnd_2214113 252645376081866890312219 := by
  unfold tailWord_2214113
  simp only [CollatzResearch.WordTrace]
  refine ⟨80755335427654216240214993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53836890285102810826809995 80755335427654216240214993)
  ·
    refine ⟨60566501570740662180161245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80755335427654216240214993 60566501570740662180161245)
    ·
      refine ⟨22712438089027748317560467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60566501570740662180161245 22712438089027748317560467)
      ·
        refine ⟨34068657133541622476340701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22712438089027748317560467 34068657133541622476340701)
        ·
          refine ⟨12775746425078108428627763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34068657133541622476340701 12775746425078108428627763)
          ·
            refine ⟨19163619637617162642941645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12775746425078108428627763 19163619637617162642941645)
            ·
              refine ⟨7186357364106435991103117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19163619637617162642941645 7186357364106435991103117)
              ·
                refine ⟨2694884011539913496663669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7186357364106435991103117 2694884011539913496663669)
                ·
                  refine ⟨252645376081866890312219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2694884011539913496663669 252645376081866890312219)
                  ·
                    rfl

theorem cell22_2214113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 5].length) (baseStart_2214113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214113 prefixEnd_2214113 := by exact prefixLift 2214113
  have htrace : WordTrace (prefixWord ++ tailWord_2214113) baseStart_2214113 baseEnd_2214113 := by
    simpa [prefixWord, tailWord_2214113, baseEnd_2214113] using wordTrace_append hprefix tailTrace_2214113
  have hstable : (prefixWord ++ tailWord_2214113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214113).length < 2 ^ (prefixWord ++ tailWord_2214113).sum := by decide
  have hdescent : baseEnd_2214113 < baseStart_2214113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214158 : List Nat := [4, 1, 1, 2, 1, 2, 2, 3, 6]
def baseStart_2214158 : Nat := 118140960795 + 2214158 * 2 ^ 59
def prefixEnd_2214158 : Nat := 4983230072969 + 3 ^ 40 * 2214158 * 2
def baseEnd_2214158 : Nat := 252650510888411851187173

theorem tailTrace_2214158 : CollatzResearch.WordTrace tailWord_2214158 prefixEnd_2214158 252650510888411851187173 := by
  unfold tailWord_2214158
  simp only [CollatzResearch.WordTrace]
  refine ⟨10094622089061398615700391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53837984474994125950402085 10094622089061398615700391)
  ·
    refine ⟨15141933133592097923550587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10094622089061398615700391 15141933133592097923550587)
    ·
      refine ⟨22712899700388146885325881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15141933133592097923550587 22712899700388146885325881)
      ·
        refine ⟨17034674775291110163994411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22712899700388146885325881 17034674775291110163994411)
        ·
          refine ⟨25552012162936665245991617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17034674775291110163994411 25552012162936665245991617)
          ·
            refine ⟨19164009122202498934493713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25552012162936665245991617 19164009122202498934493713)
            ·
              refine ⟨14373006841651874200870285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19164009122202498934493713 14373006841651874200870285)
              ·
                refine ⟨5389877565619452825326357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14373006841651874200870285 5389877565619452825326357)
                ·
                  refine ⟨252650510888411851187173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5389877565619452825326357 252650510888411851187173)
                  ·
                    rfl

theorem cell22_2214158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_2214158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214158 prefixEnd_2214158 := by exact prefixLift 2214158
  have htrace : WordTrace (prefixWord ++ tailWord_2214158) baseStart_2214158 baseEnd_2214158 := by
    simpa [prefixWord, tailWord_2214158, baseEnd_2214158] using wordTrace_append hprefix tailTrace_2214158
  have hstable : (prefixWord ++ tailWord_2214158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214158).length < 2 ^ (prefixWord ++ tailWord_2214158).sum := by decide
  have hdescent : baseEnd_2214158 < baseStart_2214158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214194 : List Nat := [3, 2, 1, 1, 5, 2, 2, 1, 1, 4]
def baseStart_2214194 : Nat := 118140960795 + 2214194 * 2 ^ 59
def prefixEnd_2214194 : Nat := 4983230072969 + 3 ^ 40 * 2214194 * 2
def baseEnd_2214194 : Nat := 757963856200943459661409

theorem tailTrace_2214194 : CollatzResearch.WordTrace tailWord_2214194 prefixEnd_2214194 757963856200943459661409 := by
  unfold tailWord_2214194
  simp only [CollatzResearch.WordTrace]
  refine ⟨20189572435090191768478409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53838859826907178049275757 20189572435090191768478409)
  ·
    refine ⟨15142179326317643826358807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20189572435090191768478409 15142179326317643826358807)
    ·
      refine ⟨22713268989476465739538211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15142179326317643826358807 22713268989476465739538211)
      ·
        refine ⟨34069903484214698609307317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22713268989476465739538211 34069903484214698609307317)
        ·
          refine ⟨3194053451645127994622561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34069903484214698609307317 3194053451645127994622561)
          ·
            refine ⟨2395540088733845995966921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3194053451645127994622561 2395540088733845995966921)
            ·
              refine ⟨1796655066550384496975191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2395540088733845995966921 1796655066550384496975191)
              ·
                refine ⟨2694982599825576745462787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1796655066550384496975191 2694982599825576745462787)
                ·
                  refine ⟨4042473899738365118194181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2694982599825576745462787 4042473899738365118194181)
                  ·
                    refine ⟨757963856200943459661409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4042473899738365118194181 757963856200943459661409)
                    ·
                      rfl

theorem cell22_2214194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_2214194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214194 prefixEnd_2214194 := by exact prefixLift 2214194
  have htrace : WordTrace (prefixWord ++ tailWord_2214194) baseStart_2214194 baseEnd_2214194 := by
    simpa [prefixWord, tailWord_2214194, baseEnd_2214194] using wordTrace_append hprefix tailTrace_2214194
  have hstable : (prefixWord ++ tailWord_2214194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214194).length < 2 ^ (prefixWord ++ tailWord_2214194).sum := by decide
  have hdescent : baseEnd_2214194 < baseStart_2214194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214263 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 2, 5]
def baseStart_2214263 : Nat := 118140960795 + 2214263 * 2 ^ 59
def prefixEnd_2214263 : Nat := 4983230072969 + 3 ^ 40 * 2214263 * 2
def baseEnd_2214263 : Nat := 757987476311050279686197

theorem tailTrace_2214263 : CollatzResearch.WordTrace tailWord_2214263 prefixEnd_2214263 757987476311050279686197 := by
  unfold tailWord_2214263
  simp only [CollatzResearch.WordTrace]
  refine ⟨80760806377110791858175443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53840537584740527905450295 80760806377110791858175443)
  ·
    refine ⟨121141209565666187787263165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80760806377110791858175443 121141209565666187787263165)
    ·
      refine ⟨45427953587124820420223687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121141209565666187787263165 45427953587124820420223687)
      ·
        refine ⟨68141930380687230630335531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45427953587124820420223687 68141930380687230630335531)
        ·
          refine ⟨102212895571030845945503297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68141930380687230630335531 102212895571030845945503297)
          ·
            refine ⟨76659671678273134459127473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102212895571030845945503297 76659671678273134459127473)
            ·
              refine ⟨57494753758704850844345605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76659671678273134459127473 57494753758704850844345605)
              ·
                refine ⟨10780266329757159533314801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57494753758704850844345605 10780266329757159533314801)
                ·
                  refine ⟨8085199747317869649986101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10780266329757159533314801 8085199747317869649986101)
                  ·
                    refine ⟨757987476311050279686197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8085199747317869649986101 757987476311050279686197)
                    ·
                      rfl

theorem cell22_2214263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_2214263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214263 prefixEnd_2214263 := by exact prefixLift 2214263
  have htrace : WordTrace (prefixWord ++ tailWord_2214263) baseStart_2214263 baseEnd_2214263 := by
    simpa [prefixWord, tailWord_2214263, baseEnd_2214263] using wordTrace_append hprefix tailTrace_2214263
  have hstable : (prefixWord ++ tailWord_2214263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214263).length < 2 ^ (prefixWord ++ tailWord_2214263).sum := by decide
  have hdescent : baseEnd_2214263 < baseStart_2214263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214293 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 8]
def baseStart_2214293 : Nat := 118140960795 + 2214293 * 2 ^ 59
def prefixEnd_2214293 : Nat := 4983230072969 + 3 ^ 40 * 2214293 * 2
def baseEnd_2214293 : Nat := 252665915308046733812035

theorem tailTrace_2214293 : CollatzResearch.WordTrace tailWord_2214293 prefixEnd_2214293 252665915308046733812035 := by
  unfold tailWord_2214293
  simp only [CollatzResearch.WordTrace]
  refine ⟨80761900567002106981767533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53841267044668071321178355 80761900567002106981767533)
  ·
    refine ⟨30285712712625790118162825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80761900567002106981767533 30285712712625790118162825)
    ·
      refine ⟨22714284534469342588622119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30285712712625790118162825 22714284534469342588622119)
      ·
        refine ⟨34071426801704013882933179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22714284534469342588622119 34071426801704013882933179)
        ·
          refine ⟨51107140202556020824399769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34071426801704013882933179 51107140202556020824399769)
          ·
            refine ⟨38330355151917015618299827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51107140202556020824399769 38330355151917015618299827)
            ·
              refine ⟨57495532727875523427449741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38330355151917015618299827 57495532727875523427449741)
              ·
                refine ⟨21560824772953321285293653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57495532727875523427449741 21560824772953321285293653)
                ·
                  refine ⟨252665915308046733812035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21560824772953321285293653 252665915308046733812035)
                  ·
                    rfl

theorem cell22_2214293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_2214293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214293 prefixEnd_2214293 := by exact prefixLift 2214293
  have htrace : WordTrace (prefixWord ++ tailWord_2214293) baseStart_2214293 baseEnd_2214293 := by
    simpa [prefixWord, tailWord_2214293, baseEnd_2214293] using wordTrace_append hprefix tailTrace_2214293
  have hstable : (prefixWord ++ tailWord_2214293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214293).length < 2 ^ (prefixWord ++ tailWord_2214293).sum := by decide
  have hdescent : baseEnd_2214293 < baseStart_2214293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214323 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 5, 6]
def baseStart_2214323 : Nat := 118140960795 + 2214323 * 2 ^ 59
def prefixEnd_2214323 : Nat := 4983230072969 + 3 ^ 40 * 2214323 * 2
def baseEnd_2214323 : Nat := 758008015537230123186013

theorem tailTrace_2214323 : CollatzResearch.WordTrace tailWord_2214323 prefixEnd_2214323 758008015537230123186013 := by
  unfold tailWord_2214323
  simp only [CollatzResearch.WordTrace]
  refine ⟨80762994756893422105359623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53841996504595614736906415 80762994756893422105359623)
  ·
    refine ⟨121144492135340133158039435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80762994756893422105359623 121144492135340133158039435)
    ·
      refine ⟨181716738203010199737059153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121144492135340133158039435 181716738203010199737059153)
      ·
        refine ⟨136287553652257649802794365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181716738203010199737059153 136287553652257649802794365)
        ·
          refine ⟨51107832619596618676047887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136287553652257649802794365 51107832619596618676047887)
          ·
            refine ⟨76661748929394928014071831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51107832619596618676047887 76661748929394928014071831)
            ·
              refine ⟨114992623394092392021107747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76661748929394928014071831 114992623394092392021107747)
              ·
                refine ⟨172488935091138588031661621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114992623394092392021107747 172488935091138588031661621)
                ·
                  refine ⟨16170837664794242627968277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 172488935091138588031661621 16170837664794242627968277)
                  ·
                    refine ⟨758008015537230123186013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16170837664794242627968277 758008015537230123186013)
                    ·
                      rfl

theorem cell22_2214323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 6].length) (baseStart_2214323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214323 prefixEnd_2214323 := by exact prefixLift 2214323
  have htrace : WordTrace (prefixWord ++ tailWord_2214323) baseStart_2214323 baseEnd_2214323 := by
    simpa [prefixWord, tailWord_2214323, baseEnd_2214323] using wordTrace_append hprefix tailTrace_2214323
  have hstable : (prefixWord ++ tailWord_2214323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214323).length < 2 ^ (prefixWord ++ tailWord_2214323).sum := by decide
  have hdescent : baseEnd_2214323 < baseStart_2214323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214327 : List Nat := [1, 1, 3, 1, 3, 4, 1, 4, 4]
def baseStart_2214327 : Nat := 118140960795 + 2214327 * 2 ^ 59
def prefixEnd_2214327 : Nat := 4983230072969 + 3 ^ 40 * 2214327 * 2
def baseEnd_2214327 : Nat := 252669794939658482028667

theorem tailTrace_2214327 : CollatzResearch.WordTrace tailWord_2214327 prefixEnd_2214327 252669794939658482028667 := by
  unfold tailWord_2214327
  simp only [CollatzResearch.WordTrace]
  refine ⟨80763140648878930788505235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53842093765919287192336823 80763140648878930788505235)
  ·
    refine ⟨121144710973318396182757853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80763140648878930788505235 121144710973318396182757853)
    ·
      refine ⟨45429266614994398568534195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121144710973318396182757853 45429266614994398568534195)
      ·
        refine ⟨68143899922491597852801293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45429266614994398568534195 68143899922491597852801293)
        ·
          refine ⟨25553962470934349194800485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68143899922491597852801293 25553962470934349194800485)
          ·
            refine ⟨4791367963300190474025091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25553962470934349194800485 4791367963300190474025091)
            ·
              refine ⟨7187051944950285711037637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4791367963300190474025091 7187051944950285711037637)
              ·
                refine ⟨1347572239678178570819557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7187051944950285711037637 1347572239678178570819557)
                ·
                  refine ⟨252669794939658482028667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1347572239678178570819557 252669794939658482028667)
                  ·
                    rfl

theorem cell22_2214327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 4].length) (baseStart_2214327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214327 prefixEnd_2214327 := by exact prefixLift 2214327
  have htrace : WordTrace (prefixWord ++ tailWord_2214327) baseStart_2214327 baseEnd_2214327 := by
    simpa [prefixWord, tailWord_2214327, baseEnd_2214327] using wordTrace_append hprefix tailTrace_2214327
  have hstable : (prefixWord ++ tailWord_2214327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214327).length < 2 ^ (prefixWord ++ tailWord_2214327).sum := by decide
  have hdescent : baseEnd_2214327 < baseStart_2214327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214357 : List Nat := [1, 3, 2, 3, 1, 2, 3, 1, 2, 4]
def baseStart_2214357 : Nat := 118140960795 + 2214357 * 2 ^ 59
def prefixEnd_2214357 : Nat := 4983230072969 + 3 ^ 40 * 2214357 * 2
def baseEnd_2214357 : Nat := 758019654432065367835909

theorem tailTrace_2214357 : CollatzResearch.WordTrace tailWord_2214357 prefixEnd_2214357 758019654432065367835909 := by
  unfold tailWord_2214357
  simp only [CollatzResearch.WordTrace]
  refine ⟨80764234838770245912097325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53842823225846830608064883 80764234838770245912097325)
  ·
    refine ⟨30286588064538842217036497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80764234838770245912097325 30286588064538842217036497)
    ·
      refine ⟨22714941048404131662777373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30286588064538842217036497 22714941048404131662777373)
      ·
        refine ⟨8518102893151549373541515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22714941048404131662777373 8518102893151549373541515)
        ·
          refine ⟨12777154339727324060312273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8518102893151549373541515 12777154339727324060312273)
          ·
            refine ⟨9582865754795493045234205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12777154339727324060312273 9582865754795493045234205)
            ·
              refine ⟨3593574658048309891962827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9582865754795493045234205 3593574658048309891962827)
              ·
                refine ⟨5390361987072464837944241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3593574658048309891962827 5390361987072464837944241)
                ·
                  refine ⟨4042771490304348628458181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5390361987072464837944241 4042771490304348628458181)
                  ·
                    refine ⟨758019654432065367835909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4042771490304348628458181 758019654432065367835909)
                    ·
                      rfl

theorem cell22_2214357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_2214357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214357 prefixEnd_2214357 := by exact prefixLift 2214357
  have htrace : WordTrace (prefixWord ++ tailWord_2214357) baseStart_2214357 baseEnd_2214357 := by
    simpa [prefixWord, tailWord_2214357, baseEnd_2214357] using wordTrace_append hprefix tailTrace_2214357
  have hstable : (prefixWord ++ tailWord_2214357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214357).length < 2 ^ (prefixWord ++ tailWord_2214357).sum := by decide
  have hdescent : baseEnd_2214357 < baseStart_2214357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214387 : List Nat := [1, 1, 1, 2, 2, 2, 6, 1, 3, 3]
def baseStart_2214387 : Nat := 118140960795 + 2214387 * 2 ^ 59
def prefixEnd_2214387 : Nat := 4983230072969 + 3 ^ 40 * 2214387 * 2
def baseEnd_2214387 : Nat := 758029924045155289585817

theorem tailTrace_2214387 : CollatzResearch.WordTrace tailWord_2214387 prefixEnd_2214387 758029924045155289585817 := by
  unfold tailWord_2214387
  simp only [CollatzResearch.WordTrace]
  refine ⟨80765329028661561035689415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53843552685774374023792943 80765329028661561035689415)
  ·
    refine ⟨121147993542992341553534123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80765329028661561035689415 121147993542992341553534123)
    ·
      refine ⟨181721990314488512330301185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121147993542992341553534123 181721990314488512330301185)
      ·
        refine ⟨136291492735866384247725889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181721990314488512330301185 136291492735866384247725889)
        ·
          refine ⟨102218619551899788185794417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136291492735866384247725889 102218619551899788185794417)
          ·
            refine ⟨76663964663924841139345813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102218619551899788185794417 76663964663924841139345813)
            ·
              refine ⟨3593623343621476928406835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76663964663924841139345813 3593623343621476928406835)
              ·
                refine ⟨5390435015432215392610253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3593623343621476928406835 5390435015432215392610253)
                ·
                  refine ⟨2021413130787080772228845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5390435015432215392610253 2021413130787080772228845)
                  ·
                    refine ⟨758029924045155289585817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2021413130787080772228845 758029924045155289585817)
                    ·
                      rfl

theorem cell22_2214387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 3].length) (baseStart_2214387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214387 prefixEnd_2214387 := by exact prefixLift 2214387
  have htrace : WordTrace (prefixWord ++ tailWord_2214387) baseStart_2214387 baseEnd_2214387 := by
    simpa [prefixWord, tailWord_2214387, baseEnd_2214387] using wordTrace_append hprefix tailTrace_2214387
  have hstable : (prefixWord ++ tailWord_2214387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214387).length < 2 ^ (prefixWord ++ tailWord_2214387).sum := by decide
  have hdescent : baseEnd_2214387 < baseStart_2214387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214404 : List Nat := [2, 3, 2, 3, 1, 1, 2, 2, 3, 3]
def baseStart_2214404 : Nat := 118140960795 + 2214404 * 2 ^ 59
def prefixEnd_2214404 : Nat := 4983230072969 + 3 ^ 40 * 2214404 * 2
def baseEnd_2214404 : Nat := 758035743492572911910765

theorem tailTrace_2214404 : CollatzResearch.WordTrace tailWord_2214404 prefixEnd_2214404 758035743492572911910765 := by
  unfold tailWord_2214404
  simp only [CollatzResearch.WordTrace]
  refine ⟨40382974534799986469529133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53843966046399981959372177 40382974534799986469529133)
  ·
    refine ⟨15143615450549994926073425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40382974534799986469529133 15143615450549994926073425)
    ·
      refine ⟨11357711587912496194555069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15143615450549994926073425 11357711587912496194555069)
      ·
        refine ⟨4259141845467186072958151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11357711587912496194555069 4259141845467186072958151)
        ·
          refine ⟨6388712768200779109437227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4259141845467186072958151 6388712768200779109437227)
          ·
            refine ⟨9583069152301168664155841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6388712768200779109437227 9583069152301168664155841)
            ·
              refine ⟨7187301864225876498116881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9583069152301168664155841 7187301864225876498116881)
              ·
                refine ⟨5390476398169407373587661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7187301864225876498116881 5390476398169407373587661)
                ·
                  refine ⟨2021428649313527765095373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5390476398169407373587661 2021428649313527765095373)
                  ·
                    refine ⟨758035743492572911910765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2021428649313527765095373 758035743492572911910765)
                    ·
                      rfl

theorem cell22_2214404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_2214404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214404 prefixEnd_2214404 := by exact prefixLift 2214404
  have htrace : WordTrace (prefixWord ++ tailWord_2214404) baseStart_2214404 baseEnd_2214404 := by
    simpa [prefixWord, tailWord_2214404, baseEnd_2214404] using wordTrace_append hprefix tailTrace_2214404
  have hstable : (prefixWord ++ tailWord_2214404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214404).length < 2 ^ (prefixWord ++ tailWord_2214404).sum := by decide
  have hdescent : baseEnd_2214404 < baseStart_2214404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214406 : List Nat := [6, 2, 1, 1, 1, 2, 1, 8]
def baseStart_2214406 : Nat := 118140960795 + 2214406 * 2 ^ 59
def prefixEnd_2214406 : Nat := 4983230072969 + 3 ^ 40 * 2214406 * 2
def baseEnd_2214406 : Nat := 84226269792605063706751

theorem tailTrace_2214406 : CollatzResearch.WordTrace tailWord_2214406 prefixEnd_2214406 84226269792605063706751 := by
  unfold tailWord_2214406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2523938187987272727519721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53844014677061818187087381 2523938187987272727519721)
  ·
    refine ⟨1892953640990454545639791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2523938187987272727519721 1892953640990454545639791)
    ·
      refine ⟨2839430461485681818459687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1892953640990454545639791 2839430461485681818459687)
      ·
        refine ⟨4259145692228522727689531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2839430461485681818459687 4259145692228522727689531)
        ·
          refine ⟨6388718538342784091534297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4259145692228522727689531 6388718538342784091534297)
          ·
            refine ⟨4791538903757088068650723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6388718538342784091534297 4791538903757088068650723)
            ·
              refine ⟨7187308355635632102976085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4791538903757088068650723 7187308355635632102976085)
              ·
                refine ⟨84226269792605063706751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7187308355635632102976085 84226269792605063706751)
                ·
                  rfl

theorem cell22_2214406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_2214406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214406 prefixEnd_2214406 := by exact prefixLift 2214406
  have htrace : WordTrace (prefixWord ++ tailWord_2214406) baseStart_2214406 baseEnd_2214406 := by
    simpa [prefixWord, tailWord_2214406, baseEnd_2214406] using wordTrace_append hprefix tailTrace_2214406
  have hstable : (prefixWord ++ tailWord_2214406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214406).length < 2 ^ (prefixWord ++ tailWord_2214406).sum := by decide
  have hdescent : baseEnd_2214406 < baseStart_2214406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214475 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 1, 6]
def baseStart_2214475 : Nat := 118140960795 + 2214475 * 2 ^ 59
def prefixEnd_2214475 : Nat := 4983230072969 + 3 ^ 40 * 2214475 * 2
def baseEnd_2214475 : Nat := 758060048243552393385547

theorem tailTrace_2214475 : CollatzResearch.WordTrace tailWord_2214475 prefixEnd_2214475 758060048243552393385547 := by
  unfold tailWord_2214475
  simp only [CollatzResearch.WordTrace]
  refine ⟨80768538652342752064892879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53845692434895168043261919 80768538652342752064892879)
  ·
    refine ⟨121152807978514128097339319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80768538652342752064892879 121152807978514128097339319)
    ·
      refine ⟨181729211967771192146008979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121152807978514128097339319 181729211967771192146008979)
      ·
        refine ⟨272593817951656788219013469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181729211967771192146008979 272593817951656788219013469)
        ·
          refine ⟨102222681731871295582130051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 272593817951656788219013469 102222681731871295582130051)
          ·
            refine ⟨153334022597806943373195077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102222681731871295582130051 153334022597806943373195077)
            ·
              refine ⟨28750129237088801882474077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153334022597806943373195077 28750129237088801882474077)
              ·
                refine ⟨10781298463908300705927779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28750129237088801882474077 10781298463908300705927779)
                ·
                  refine ⟨16171947695862451058891669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10781298463908300705927779 16171947695862451058891669)
                  ·
                    refine ⟨758060048243552393385547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16171947695862451058891669 758060048243552393385547)
                    ·
                      rfl

theorem cell22_2214475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 6].length) (baseStart_2214475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214475 prefixEnd_2214475 := by exact prefixLift 2214475
  have htrace : WordTrace (prefixWord ++ tailWord_2214475) baseStart_2214475 baseEnd_2214475 := by
    simpa [prefixWord, tailWord_2214475, baseEnd_2214475] using wordTrace_append hprefix tailTrace_2214475
  have hstable : (prefixWord ++ tailWord_2214475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214475).length < 2 ^ (prefixWord ++ tailWord_2214475).sum := by decide
  have hdescent : baseEnd_2214475 < baseStart_2214475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214505 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 2, 7]
def baseStart_2214505 : Nat := 118140960795 + 2214505 * 2 ^ 59
def prefixEnd_2214505 : Nat := 4983230072969 + 3 ^ 40 * 2214505 * 2
def baseEnd_2214505 : Nat := 758070317856642315135455

theorem tailTrace_2214505 : CollatzResearch.WordTrace tailWord_2214505 prefixEnd_2214505 758070317856642315135455 := by
  unfold tailWord_2214505
  simp only [CollatzResearch.WordTrace]
  refine ⟨80769632842234067188484969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53846421894822711458989979 80769632842234067188484969)
  ·
    refine ⟨60577224631675550391363727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80769632842234067188484969 60577224631675550391363727)
    ·
      refine ⟨90865836947513325587045591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60577224631675550391363727 90865836947513325587045591)
      ·
        refine ⟨136298755421269988380568387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90865836947513325587045591 136298755421269988380568387)
        ·
          refine ⟨204448133131904982570852581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136298755421269988380568387 204448133131904982570852581)
          ·
            refine ⟨38334024962232184232034859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 204448133131904982570852581 38334024962232184232034859)
            ·
              refine ⟨57501037443348276348052289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38334024962232184232034859 57501037443348276348052289)
              ·
                refine ⟨43125778082511207261039217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57501037443348276348052289 43125778082511207261039217)
                ·
                  refine ⟨32344333561883405445779413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43125778082511207261039217 32344333561883405445779413)
                  ·
                    refine ⟨758070317856642315135455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32344333561883405445779413 758070317856642315135455)
                    ·
                      rfl

theorem cell22_2214505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_2214505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214505 prefixEnd_2214505 := by exact prefixLift 2214505
  have htrace : WordTrace (prefixWord ++ tailWord_2214505) baseStart_2214505 baseEnd_2214505 := by
    simpa [prefixWord, tailWord_2214505, baseEnd_2214505] using wordTrace_append hprefix tailTrace_2214505
  have hstable : (prefixWord ++ tailWord_2214505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214505).length < 2 ^ (prefixWord ++ tailWord_2214505).sum := by decide
  have hdescent : baseEnd_2214505 < baseStart_2214505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214552 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 7]
def baseStart_2214552 : Nat := 118140960795 + 2214552 * 2 ^ 59
def prefixEnd_2214552 : Nat := 4983230072969 + 3 ^ 40 * 2214552 * 2
def baseEnd_2214552 : Nat := 252695468972383286403437

theorem tailTrace_2214552 : CollatzResearch.WordTrace tailWord_2214552 prefixEnd_2214552 252695468972383286403437 := by
  unfold tailWord_2214552
  simp only [CollatzResearch.WordTrace]
  refine ⟨40385673536531897107722955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53847564715375862810297273 40385673536531897107722955)
  ·
    refine ⟨60578510304797845661584433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40385673536531897107722955 60578510304797845661584433)
    ·
      refine ⟨45433882728598384246188325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60578510304797845661584433 45433882728598384246188325)
      ·
        refine ⟨8518853011612197046160311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45433882728598384246188325 8518853011612197046160311)
        ·
          refine ⟨12778279517418295569240467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8518853011612197046160311 12778279517418295569240467)
          ·
            refine ⟨19167419276127443353860701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12778279517418295569240467 19167419276127443353860701)
            ·
              refine ⟨7187782228547791257697763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19167419276127443353860701 7187782228547791257697763)
              ·
                refine ⟨10781673342821686886546645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7187782228547791257697763 10781673342821686886546645)
                ·
                  refine ⟨252695468972383286403437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10781673342821686886546645 252695468972383286403437)
                  ·
                    rfl

theorem cell22_2214552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 7].length) (baseStart_2214552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214552 prefixEnd_2214552 := by exact prefixLift 2214552
  have htrace : WordTrace (prefixWord ++ tailWord_2214552) baseStart_2214552 baseEnd_2214552 := by
    simpa [prefixWord, tailWord_2214552, baseEnd_2214552] using wordTrace_append hprefix tailTrace_2214552
  have hstable : (prefixWord ++ tailWord_2214552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214552).length < 2 ^ (prefixWord ++ tailWord_2214552).sum := by decide
  have hdescent : baseEnd_2214552 < baseStart_2214552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214556 : List Nat := [2, 2, 3, 2, 2, 2, 2, 1, 3, 3]
def baseStart_2214556 : Nat := 118140960795 + 2214556 * 2 ^ 59
def prefixEnd_2214556 : Nat := 4983230072969 + 3 ^ 40 * 2214556 * 2
def baseEnd_2214556 : Nat := 758087776198895182110299

theorem tailTrace_2214556 : CollatzResearch.WordTrace tailWord_2214556 prefixEnd_2214556 758087776198895182110299 := by
  unfold tailWord_2214556
  simp only [CollatzResearch.WordTrace]
  refine ⟨40385746482524651449295761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53847661976699535265727681 40385746482524651449295761)
  ·
    refine ⟨30289309861893488586971821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40385746482524651449295761 30289309861893488586971821)
    ·
      refine ⟨11358491198210058220114433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30289309861893488586971821 11358491198210058220114433)
      ·
        refine ⟨8518868398657543665085825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11358491198210058220114433 8518868398657543665085825)
        ·
          refine ⟨6389151298993157748814369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8518868398657543665085825 6389151298993157748814369)
          ·
            refine ⟨4791863474244868311610777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6389151298993157748814369 4791863474244868311610777)
            ·
              refine ⟨3593897605683651233708083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4791863474244868311610777 3593897605683651233708083)
              ·
                refine ⟨5390846408525476850562125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3593897605683651233708083 5390846408525476850562125)
                ·
                  refine ⟨2021567403197053818960797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5390846408525476850562125 2021567403197053818960797)
                  ·
                    refine ⟨758087776198895182110299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2021567403197053818960797 758087776198895182110299)
                    ·
                      rfl

theorem cell22_2214556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_2214556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214556 prefixEnd_2214556 := by exact prefixLift 2214556
  have htrace : WordTrace (prefixWord ++ tailWord_2214556) baseStart_2214556 baseEnd_2214556 := by
    simpa [prefixWord, tailWord_2214556, baseEnd_2214556] using wordTrace_append hprefix tailTrace_2214556
  have hstable : (prefixWord ++ tailWord_2214556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214556).length < 2 ^ (prefixWord ++ tailWord_2214556).sum := by decide
  have hdescent : baseEnd_2214556 < baseStart_2214556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214663 : List Nat := [1, 1, 4, 4, 1, 2, 2, 2, 2, 3]
def baseStart_2214663 : Nat := 118140960795 + 2214663 * 2 ^ 59
def prefixEnd_2214663 : Nat := 4983230072969 + 3 ^ 40 * 2214663 * 2
def baseEnd_2214663 : Nat := 758124404485582569684971

theorem tailTrace_2214663 : CollatzResearch.WordTrace tailWord_2214663 prefixEnd_2214663 758124404485582569684971 := by
  unfold tailWord_2214663
  simp only [CollatzResearch.WordTrace]
  refine ⟨80775395575661660172736643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53850263717107773448491095 80775395575661660172736643)
  ·
    refine ⟨121163093363492490259104965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80775395575661660172736643 121163093363492490259104965)
    ·
      refine ⟨22718080005654841923582181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121163093363492490259104965 22718080005654841923582181)
      ·
        refine ⟨4259640001060282860671659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22718080005654841923582181 4259640001060282860671659)
        ·
          refine ⟨6389460001590424291007489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4259640001060282860671659 6389460001590424291007489)
          ·
            refine ⟨4792095001192818218255617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6389460001590424291007489 4792095001192818218255617)
            ·
              refine ⟨3594071250894613663691713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4792095001192818218255617 3594071250894613663691713)
              ·
                refine ⟨2695553438170960247768785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3594071250894613663691713 2695553438170960247768785)
                ·
                  refine ⟨2021665078628220185826589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2695553438170960247768785 2021665078628220185826589)
                  ·
                    refine ⟨758124404485582569684971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2021665078628220185826589 758124404485582569684971)
                    ·
                      rfl

theorem cell22_2214663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_2214663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214663 prefixEnd_2214663 := by exact prefixLift 2214663
  have htrace : WordTrace (prefixWord ++ tailWord_2214663) baseStart_2214663 baseEnd_2214663 := by
    simpa [prefixWord, tailWord_2214663, baseEnd_2214663] using wordTrace_append hprefix tailTrace_2214663
  have hstable : (prefixWord ++ tailWord_2214663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214663).length < 2 ^ (prefixWord ++ tailWord_2214663).sum := by decide
  have hdescent : baseEnd_2214663 < baseStart_2214663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214719 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 2, 5]
def baseStart_2214719 : Nat := 118140960795 + 2214719 * 2 ^ 59
def prefixEnd_2214719 : Nat := 4983230072969 + 3 ^ 40 * 2214719 * 2
def baseEnd_2214719 : Nat := 758143574430017090284799

theorem tailTrace_2214719 : CollatzResearch.WordTrace tailWord_2214719 prefixEnd_2214719 758143574430017090284799 := by
  unfold tailWord_2214719
  simp only [CollatzResearch.WordTrace]
  refine ⟨80777438063458781736775211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53851625375639187824516807 80777438063458781736775211)
  ·
    refine ⟨121166157095188172605162817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80777438063458781736775211 121166157095188172605162817)
    ·
      refine ⟨90874617821391129453872113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121166157095188172605162817 90874617821391129453872113)
      ·
        refine ⟨68155963366043347090404085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90874617821391129453872113 68155963366043347090404085)
        ·
          refine ⟨6389621565566563789725383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68155963366043347090404085 6389621565566563789725383)
          ·
            refine ⟨9584432348349845684588075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6389621565566563789725383 9584432348349845684588075)
            ·
              refine ⟨14376648522524768526882113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9584432348349845684588075 14376648522524768526882113)
              ·
                refine ⟨10782486391893576395161585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14376648522524768526882113 10782486391893576395161585)
                ·
                  refine ⟨8086864793920182296371189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10782486391893576395161585 8086864793920182296371189)
                  ·
                    refine ⟨758143574430017090284799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8086864793920182296371189 758143574430017090284799)
                    ·
                      rfl

theorem cell22_2214719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 5].length) (baseStart_2214719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214719 prefixEnd_2214719 := by exact prefixLift 2214719
  have htrace : WordTrace (prefixWord ++ tailWord_2214719) baseStart_2214719 baseEnd_2214719 := by
    simpa [prefixWord, tailWord_2214719, baseEnd_2214719] using wordTrace_append hprefix tailTrace_2214719
  have hstable : (prefixWord ++ tailWord_2214719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214719).length < 2 ^ (prefixWord ++ tailWord_2214719).sum := by decide
  have hdescent : baseEnd_2214719 < baseStart_2214719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214734 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 5, 4]
def baseStart_2214734 : Nat := 118140960795 + 2214734 * 2 ^ 59
def prefixEnd_2214734 : Nat := 4983230072969 + 3 ^ 40 * 2214734 * 2
def baseEnd_2214734 : Nat := 758148709236562051159753

theorem tailTrace_2214734 : CollatzResearch.WordTrace tailWord_2214734 prefixEnd_2214734 758148709236562051159753 := by
  unfold tailWord_2214734
  simp only [CollatzResearch.WordTrace]
  refine ⟨10097248144800554912321407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53851990105602959532380837 10097248144800554912321407)
  ·
    refine ⟨15145872217200832368482111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10097248144800554912321407 15145872217200832368482111)
    ·
      refine ⟨22718808325801248552723167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15145872217200832368482111 22718808325801248552723167)
      ·
        refine ⟨34078212488701872829084751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22718808325801248552723167 34078212488701872829084751)
        ·
          refine ⟨51117318733052809243627127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34078212488701872829084751 51117318733052809243627127)
          ·
            refine ⟨76675978099579213865440691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51117318733052809243627127 76675978099579213865440691)
            ·
              refine ⟨115013967149368820798161037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76675978099579213865440691 115013967149368820798161037)
              ·
                refine ⟨43130237681013307799310389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115013967149368820798161037 43130237681013307799310389)
                ·
                  refine ⟨4043459782594997606185349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43130237681013307799310389 4043459782594997606185349)
                  ·
                    refine ⟨758148709236562051159753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4043459782594997606185349 758148709236562051159753)
                    ·
                      rfl

theorem cell22_2214734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_2214734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214734 prefixEnd_2214734 := by exact prefixLift 2214734
  have htrace : WordTrace (prefixWord ++ tailWord_2214734) baseStart_2214734 baseEnd_2214734 := by
    simpa [prefixWord, tailWord_2214734, baseEnd_2214734] using wordTrace_append hprefix tailTrace_2214734
  have hstable : (prefixWord ++ tailWord_2214734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214734).length < 2 ^ (prefixWord ++ tailWord_2214734).sum := by decide
  have hdescent : baseEnd_2214734 < baseStart_2214734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214751 : List Nat := [1, 1, 2, 3, 1, 3, 4, 2, 1, 4]
def baseStart_2214751 : Nat := 118140960795 + 2214751 * 2 ^ 59
def prefixEnd_2214751 : Nat := 4983230072969 + 3 ^ 40 * 2214751 * 2
def baseEnd_2214751 : Nat := 758154528683979673484701

theorem tailTrace_2214751 : CollatzResearch.WordTrace tailWord_2214751 prefixEnd_2214751 758154528683979673484701 := by
  unfold tailWord_2214751
  simp only [CollatzResearch.WordTrace]
  refine ⟨80778605199342851201940107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53852403466228567467960071 80778605199342851201940107)
  ·
    refine ⟨121167907799014276802910161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80778605199342851201940107 121167907799014276802910161)
    ·
      refine ⟨90875930849260707602182621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121167907799014276802910161 90875930849260707602182621)
      ·
        refine ⟨34078474068472765350818483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90875930849260707602182621 34078474068472765350818483)
        ·
          refine ⟨51117711102709148026227725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34078474068472765350818483 51117711102709148026227725)
          ·
            refine ⟨19169141663515930509835397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51117711102709148026227725 19169141663515930509835397)
            ·
              refine ⟨3594214061909236970594137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19169141663515930509835397 3594214061909236970594137)
              ·
                refine ⟨2695660546431927727945603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3594214061909236970594137 2695660546431927727945603)
                ·
                  refine ⟨4043490819647891591918405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2695660546431927727945603 4043490819647891591918405)
                  ·
                    refine ⟨758154528683979673484701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4043490819647891591918405 758154528683979673484701)
                    ·
                      rfl

theorem cell22_2214751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 4].length) (baseStart_2214751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214751 prefixEnd_2214751 := by exact prefixLift 2214751
  have htrace : WordTrace (prefixWord ++ tailWord_2214751) baseStart_2214751 baseEnd_2214751 := by
    simpa [prefixWord, tailWord_2214751, baseEnd_2214751] using wordTrace_append hprefix tailTrace_2214751
  have hstable : (prefixWord ++ tailWord_2214751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214751).length < 2 ^ (prefixWord ++ tailWord_2214751).sum := by decide
  have hdescent : baseEnd_2214751 < baseStart_2214751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214764 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 3, 5]
def baseStart_2214764 : Nat := 118140960795 + 2214764 * 2 ^ 59
def prefixEnd_2214764 : Nat := 4983230072969 + 3 ^ 40 * 2214764 * 2
def baseEnd_2214764 : Nat := 758158978849651972909661

theorem tailTrace_2214764 : CollatzResearch.WordTrace tailWord_2214764 prefixEnd_2214764 758158978849651972909661 := by
  unfold tailWord_2214764
  simp only [CollatzResearch.WordTrace]
  refine ⟨40389539674147877211081673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53852719565530502948108897 40389539674147877211081673)
  ·
    refine ⟨30292154755610907908311255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40389539674147877211081673 30292154755610907908311255)
    ·
      refine ⟨45438232133416361862466883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30292154755610907908311255 45438232133416361862466883)
      ·
        refine ⟨68157348200124542793700325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45438232133416361862466883 68157348200124542793700325)
        ·
          refine ⟨12779502787523351773818811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68157348200124542793700325 12779502787523351773818811)
          ·
            refine ⟨19169254181285027660728217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12779502787523351773818811 19169254181285027660728217)
            ·
              refine ⟨14376940635963770745546163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19169254181285027660728217 14376940635963770745546163)
              ·
                refine ⟨21565410953945656118319245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14376940635963770745546163 21565410953945656118319245)
                ·
                  refine ⟨8087029107729621044369717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21565410953945656118319245 8087029107729621044369717)
                  ·
                    refine ⟨758158978849651972909661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8087029107729621044369717 758158978849651972909661)
                    ·
                      rfl

theorem cell22_2214764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_2214764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214764 prefixEnd_2214764 := by exact prefixLift 2214764
  have htrace : WordTrace (prefixWord ++ tailWord_2214764) baseStart_2214764 baseEnd_2214764 := by
    simpa [prefixWord, tailWord_2214764, baseEnd_2214764] using wordTrace_append hprefix tailTrace_2214764
  have hstable : (prefixWord ++ tailWord_2214764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214764).length < 2 ^ (prefixWord ++ tailWord_2214764).sum := by decide
  have hdescent : baseEnd_2214764 < baseStart_2214764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214779 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 4, 4]
def baseStart_2214779 : Nat := 118140960795 + 2214779 * 2 ^ 59
def prefixEnd_2214779 : Nat := 4983230072969 + 3 ^ 40 * 2214779 * 2
def baseEnd_2214779 : Nat := 758164113656196933784615

theorem tailTrace_2214779 : CollatzResearch.WordTrace tailWord_2214779 prefixEnd_2214779 758164113656196933784615 := by
  unfold tailWord_2214779
  simp only [CollatzResearch.WordTrace]
  refine ⟨80779626443241411983959391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53853084295494274655972927 80779626443241411983959391)
  ·
    refine ⟨121169439664862117975939087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80779626443241411983959391 121169439664862117975939087)
    ·
      refine ⟨181754159497293176963908631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121169439664862117975939087 181754159497293176963908631)
      ·
        refine ⟨272631239245939765445862947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181754159497293176963908631 272631239245939765445862947)
        ·
          refine ⟨408946858868909648168794421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272631239245939765445862947 408946858868909648168794421)
          ·
            refine ⟨38338768018960279515824477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 408946858868909648168794421 38338768018960279515824477)
            ·
              refine ⟨14377038007110104818434179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38338768018960279515824477 14377038007110104818434179)
              ·
                refine ⟨21565557010665157227651269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14377038007110104818434179 21565557010665157227651269)
                ·
                  refine ⟨4043541939499716980184613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21565557010665157227651269 4043541939499716980184613)
                  ·
                    refine ⟨758164113656196933784615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4043541939499716980184613 758164113656196933784615)
                    ·
                      rfl

theorem cell22_2214779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 4].length) (baseStart_2214779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214779 prefixEnd_2214779 := by exact prefixLift 2214779
  have htrace : WordTrace (prefixWord ++ tailWord_2214779) baseStart_2214779 baseEnd_2214779 := by
    simpa [prefixWord, tailWord_2214779, baseEnd_2214779] using wordTrace_append hprefix tailTrace_2214779
  have hstable : (prefixWord ++ tailWord_2214779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214779).length < 2 ^ (prefixWord ++ tailWord_2214779).sum := by decide
  have hdescent : baseEnd_2214779 < baseStart_2214779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214781 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 4, 3]
def baseStart_2214781 : Nat := 118140960795 + 2214781 * 2 ^ 59
def prefixEnd_2214781 : Nat := 4983230072969 + 3 ^ 40 * 2214781 * 2
def baseEnd_2214781 : Nat := 758164798297069595234609

theorem tailTrace_2214781 : CollatzResearch.WordTrace tailWord_2214781 prefixEnd_2214781 758164798297069595234609 := by
  unfold tailWord_2214781
  simp only [CollatzResearch.WordTrace]
  refine ⟨80779699389234166325532197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53853132926156110883688131 80779699389234166325532197)
  ·
    refine ⟨15146193635481406186037287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80779699389234166325532197 15146193635481406186037287)
    ·
      refine ⟨22719290453222109279055931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15146193635481406186037287 22719290453222109279055931)
      ·
        refine ⟨34078935679833163918583897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22719290453222109279055931 34078935679833163918583897)
        ·
          refine ⟨25559201759874872938937923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34078935679833163918583897 25559201759874872938937923)
          ·
            refine ⟨38338802639812309408406885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25559201759874872938937923 38338802639812309408406885)
            ·
              refine ⟨7188525494964808014076291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38338802639812309408406885 7188525494964808014076291)
              ·
                refine ⟨10782788242447212021114437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7188525494964808014076291 10782788242447212021114437)
                ·
                  refine ⟨2021772795458852253958957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10782788242447212021114437 2021772795458852253958957)
                  ·
                    refine ⟨758164798297069595234609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2021772795458852253958957 758164798297069595234609)
                    ·
                      rfl

theorem cell22_2214781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_2214781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214781 prefixEnd_2214781 := by exact prefixLift 2214781
  have htrace : WordTrace (prefixWord ++ tailWord_2214781) baseStart_2214781 baseEnd_2214781 := by
    simpa [prefixWord, tailWord_2214781, baseEnd_2214781] using wordTrace_append hprefix tailTrace_2214781
  have hstable : (prefixWord ++ tailWord_2214781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214781).length < 2 ^ (prefixWord ++ tailWord_2214781).sum := by decide
  have hdescent : baseEnd_2214781 < baseStart_2214781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214802 : List Nat := [3, 2, 3, 2, 3, 1, 1, 2, 1, 4]
def baseStart_2214802 : Nat := 118140960795 + 2214802 * 2 ^ 59
def prefixEnd_2214802 : Nat := 4983230072969 + 3 ^ 40 * 2214802 * 2
def baseEnd_2214802 : Nat := 758171987026232540459545

theorem tailTrace_2214802 : CollatzResearch.WordTrace tailWord_2214802 prefixEnd_2214802 758171987026232540459545 := by
  unfold tailWord_2214802
  simp only [CollatzResearch.WordTrace]
  refine ⟨20195116330539521728011665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53853643548105391274697773 20195116330539521728011665)
  ·
    refine ⟨15146337247904641296008749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20195116330539521728011665 15146337247904641296008749)
    ·
      refine ⟨5679876467964240486003281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15146337247904641296008749 5679876467964240486003281)
      ·
        refine ⟨4259907350973180364502461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5679876467964240486003281 4259907350973180364502461)
        ·
          refine ⟨1597465256614942636688423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4259907350973180364502461 1597465256614942636688423)
          ·
            refine ⟨2396197884922413955032635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1597465256614942636688423 2396197884922413955032635)
            ·
              refine ⟨3594296827383620932548953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2396197884922413955032635 3594296827383620932548953)
              ·
                refine ⟨2695722620537715699411715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3594296827383620932548953 2695722620537715699411715)
                ·
                  refine ⟨4043583930806573549117573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2695722620537715699411715 4043583930806573549117573)
                  ·
                    refine ⟨758171987026232540459545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4043583930806573549117573 758171987026232540459545)
                    ·
                      rfl

theorem cell22_2214802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_2214802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214802 prefixEnd_2214802 := by exact prefixLift 2214802
  have htrace : WordTrace (prefixWord ++ tailWord_2214802) baseStart_2214802 baseEnd_2214802 := by
    simpa [prefixWord, tailWord_2214802, baseEnd_2214802] using wordTrace_append hprefix tailTrace_2214802
  have hstable : (prefixWord ++ tailWord_2214802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214802).length < 2 ^ (prefixWord ++ tailWord_2214802).sum := by decide
  have hdescent : baseEnd_2214802 < baseStart_2214802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214839 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 7]
def baseStart_2214839 : Nat := 118140960795 + 2214839 * 2 ^ 59
def prefixEnd_2214839 : Nat := 4983230072969 + 3 ^ 40 * 2214839 * 2
def baseEnd_2214839 : Nat := 252728217627458925761477

theorem tailTrace_2214839 : CollatzResearch.WordTrace tailWord_2214839 prefixEnd_2214839 252728217627458925761477 := by
  unfold tailWord_2214839
  simp only [CollatzResearch.WordTrace]
  refine ⟨80781814823024042231143571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53854543215349361487429047 80781814823024042231143571)
  ·
    refine ⟨121172722234536063346715357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80781814823024042231143571 121172722234536063346715357)
    ·
      refine ⟨45439770837951023755018259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121172722234536063346715357 45439770837951023755018259)
      ·
        refine ⟨68159656256926535632527389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45439770837951023755018259 68159656256926535632527389)
        ·
          refine ⟨25559871096347450862197771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68159656256926535632527389 25559871096347450862197771)
          ·
            refine ⟨38339806644521176293296657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25559871096347450862197771 38339806644521176293296657)
            ·
              refine ⟨28754854983390882219972493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38339806644521176293296657 28754854983390882219972493)
              ·
                refine ⟨10783070618771580832489685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28754854983390882219972493 10783070618771580832489685)
                ·
                  refine ⟨252728217627458925761477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10783070618771580832489685 252728217627458925761477)
                  ·
                    rfl

theorem cell22_2214839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 7].length) (baseStart_2214839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214839 prefixEnd_2214839 := by exact prefixLift 2214839
  have htrace : WordTrace (prefixWord ++ tailWord_2214839) baseStart_2214839 baseEnd_2214839 := by
    simpa [prefixWord, tailWord_2214839, baseEnd_2214839] using wordTrace_append hprefix tailTrace_2214839
  have hstable : (prefixWord ++ tailWord_2214839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214839).length < 2 ^ (prefixWord ++ tailWord_2214839).sum := by decide
  have hdescent : baseEnd_2214839 < baseStart_2214839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214877 : List Nat := [1, 4, 3, 1, 2, 2, 2, 3, 1, 3]
def baseStart_2214877 : Nat := 118140960795 + 2214877 * 2 ^ 59
def prefixEnd_2214877 : Nat := 4983230072969 + 3 ^ 40 * 2214877 * 2
def baseEnd_2214877 : Nat := 758197661058957344834315

theorem tailTrace_2214877 : CollatzResearch.WordTrace tailWord_2214877 prefixEnd_2214877 758197661058957344834315 := by
  unfold tailWord_2214877
  simp only [CollatzResearch.WordTrace]
  refine ⟨80783200796886374721026885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53855467197924249814017923 80783200796886374721026885)
  ·
    refine ⟨15146850149416195260192541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80783200796886374721026885 15146850149416195260192541)
    ·
      refine ⟨5680068806031073222572203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15146850149416195260192541 5680068806031073222572203)
      ·
        refine ⟨8520103209046609833858305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5680068806031073222572203 8520103209046609833858305)
        ·
          refine ⟨6390077406784957375393729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8520103209046609833858305 6390077406784957375393729)
          ·
            refine ⟨4792558055088718031545297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6390077406784957375393729 4792558055088718031545297)
            ·
              refine ⟨3594418541316538523658973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4792558055088718031545297 3594418541316538523658973)
              ·
                refine ⟨1347906952993701946372115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3594418541316538523658973 1347906952993701946372115)
                ·
                  refine ⟨2021860429490552919558173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1347906952993701946372115 2021860429490552919558173)
                  ·
                    refine ⟨758197661058957344834315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2021860429490552919558173 758197661058957344834315)
                    ·
                      rfl

theorem cell22_2214877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_2214877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214877 prefixEnd_2214877 := by exact prefixLift 2214877
  have htrace : WordTrace (prefixWord ++ tailWord_2214877) baseStart_2214877 baseEnd_2214877 := by
    simpa [prefixWord, tailWord_2214877, baseEnd_2214877] using wordTrace_append hprefix tailTrace_2214877
  have hstable : (prefixWord ++ tailWord_2214877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214877).length < 2 ^ (prefixWord ++ tailWord_2214877).sum := by decide
  have hdescent : baseEnd_2214877 < baseStart_2214877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214899 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 2, 9]
def baseStart_2214899 : Nat := 118140960795 + 2214899 * 2 ^ 59
def prefixEnd_2214899 : Nat := 4983230072969 + 3 ^ 40 * 2214899 * 2
def baseEnd_2214899 : Nat := 758205192108556620784247

theorem tailTrace_2214899 : CollatzResearch.WordTrace tailWord_2214899 prefixEnd_2214899 758205192108556620784247 := by
  unfold tailWord_2214899
  simp only [CollatzResearch.WordTrace]
  refine ⟨80784003202806672478327751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53856002135204448318885167 80784003202806672478327751)
  ·
    refine ⟨121176004804210008717491627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80784003202806672478327751 121176004804210008717491627)
    ·
      refine ⟨181764007206315013076237441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121176004804210008717491627 181764007206315013076237441)
      ·
        refine ⟨136323005404736259807178081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181764007206315013076237441 136323005404736259807178081)
        ·
          refine ⟨102242254053552194855383561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136323005404736259807178081 102242254053552194855383561)
          ·
            refine ⟨76681690540164146141537671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102242254053552194855383561 76681690540164146141537671)
            ·
              refine ⟨115022535810246219212306507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76681690540164146141537671 115022535810246219212306507)
              ·
                refine ⟨172533803715369328818459761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115022535810246219212306507 172533803715369328818459761)
                ·
                  refine ⟨129400352786526996613844821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172533803715369328818459761 129400352786526996613844821)
                  ·
                    refine ⟨758205192108556620784247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 129400352786526996613844821 758205192108556620784247)
                    ·
                      rfl

theorem cell22_2214899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 9].length) (baseStart_2214899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214899 prefixEnd_2214899 := by exact prefixLift 2214899
  have htrace : WordTrace (prefixWord ++ tailWord_2214899) baseStart_2214899 baseEnd_2214899 := by
    simpa [prefixWord, tailWord_2214899, baseEnd_2214899] using wordTrace_append hprefix tailTrace_2214899
  have hstable : (prefixWord ++ tailWord_2214899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214899).length < 2 ^ (prefixWord ++ tailWord_2214899).sum := by decide
  have hdescent : baseEnd_2214899 < baseStart_2214899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214931 : List Nat := [1, 1, 1, 2, 1, 4, 1, 5, 2, 4]
def baseStart_2214931 : Nat := 118140960795 + 2214931 * 2 ^ 59
def prefixEnd_2214931 : Nat := 4983230072969 + 3 ^ 40 * 2214931 * 2
def baseEnd_2214931 : Nat := 758216146362519203984149

theorem tailTrace_2214931 : CollatzResearch.WordTrace tailWord_2214931 prefixEnd_2214931 758216146362519203984149 := by
  unfold tailWord_2214931
  simp only [CollatzResearch.WordTrace]
  refine ⟨80785170338690741943492647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53856780225793827962328431 80785170338690741943492647)
  ·
    refine ⟨121177755508036112915238971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80785170338690741943492647 121177755508036112915238971)
    ·
      refine ⟨181766633262054169372858457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121177755508036112915238971 181766633262054169372858457)
      ·
        refine ⟨136324974946540627029643843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181766633262054169372858457 136324974946540627029643843)
        ·
          refine ⟨204487462419810940544465765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136324974946540627029643843 204487462419810940544465765)
          ·
            refine ⟨38341399203714551352087331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 204487462419810940544465765 38341399203714551352087331)
            ·
              refine ⟨57512098805571827028130997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38341399203714551352087331 57512098805571827028130997)
              ·
                refine ⟨5391759263022358783887281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57512098805571827028130997 5391759263022358783887281)
                ·
                  refine ⟨4043819447266769087915461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5391759263022358783887281 4043819447266769087915461)
                  ·
                    refine ⟨758216146362519203984149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4043819447266769087915461 758216146362519203984149)
                    ·
                      rfl

theorem cell22_2214931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 4].length) (baseStart_2214931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214931 prefixEnd_2214931 := by exact prefixLift 2214931
  have htrace : WordTrace (prefixWord ++ tailWord_2214931) baseStart_2214931 baseEnd_2214931 := by
    simpa [prefixWord, tailWord_2214931, baseEnd_2214931] using wordTrace_append hprefix tailTrace_2214931
  have hstable : (prefixWord ++ tailWord_2214931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214931).length < 2 ^ (prefixWord ++ tailWord_2214931).sum := by decide
  have hdescent : baseEnd_2214931 < baseStart_2214931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214933 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 4, 3]
def baseStart_2214933 : Nat := 118140960795 + 2214933 * 2 ^ 59
def prefixEnd_2214933 : Nat := 4983230072969 + 3 ^ 40 * 2214933 * 2
def baseEnd_2214933 : Nat := 758216831003391865434143

theorem tailTrace_2214933 : CollatzResearch.WordTrace tailWord_2214933 prefixEnd_2214933 758216831003391865434143 := by
  unfold tailWord_2214933
  simp only [CollatzResearch.WordTrace]
  refine ⟨80785243284683496285065453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53856828856455664190043635 80785243284683496285065453)
  ·
    refine ⟨30294466231756311106899545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80785243284683496285065453 30294466231756311106899545)
    ·
      refine ⟨22720849673817233330174659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30294466231756311106899545 22720849673817233330174659)
      ·
        refine ⟨34081274510725849995261989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22720849673817233330174659 34081274510725849995261989)
        ·
          refine ⟨6390238970761096874111623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34081274510725849995261989 6390238970761096874111623)
          ·
            refine ⟨9585358456141645311167435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6390238970761096874111623 9585358456141645311167435)
            ·
              refine ⟨14378037684212467966751153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9585358456141645311167435 14378037684212467966751153)
              ·
                refine ⟨10783528263159350975063365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14378037684212467966751153 10783528263159350975063365)
                ·
                  refine ⟨2021911549342378307824381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10783528263159350975063365 2021911549342378307824381)
                  ·
                    refine ⟨758216831003391865434143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2021911549342378307824381 758216831003391865434143)
                    ·
                      rfl

theorem cell22_2214933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_2214933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214933 prefixEnd_2214933 := by exact prefixLift 2214933
  have htrace : WordTrace (prefixWord ++ tailWord_2214933) baseStart_2214933 baseEnd_2214933 := by
    simpa [prefixWord, tailWord_2214933, baseEnd_2214933] using wordTrace_append hprefix tailTrace_2214933
  have hstable : (prefixWord ++ tailWord_2214933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214933).length < 2 ^ (prefixWord ++ tailWord_2214933).sum := by decide
  have hdescent : baseEnd_2214933 < baseStart_2214933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214935 : List Nat := [1, 1, 3, 5, 1, 1, 3, 3, 4]
def baseStart_2214935 : Nat := 118140960795 + 2214935 * 2 ^ 59
def prefixEnd_2214935 : Nat := 4983230072969 + 3 ^ 40 * 2214935 * 2
def baseEnd_2214935 : Nat := 252739171881421508961379

theorem tailTrace_2214935 : CollatzResearch.WordTrace tailWord_2214935 prefixEnd_2214935 252739171881421508961379 := by
  unfold tailWord_2214935
  simp only [CollatzResearch.WordTrace]
  refine ⟨80785316230676250626638259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53856877487117500417758839 80785316230676250626638259)
  ·
    refine ⟨121177974346014375939957389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80785316230676250626638259 121177974346014375939957389)
    ·
      refine ⟨45441740379755390977484021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121177974346014375939957389 45441740379755390977484021)
      ·
        refine ⟨4260163160602067904139127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45441740379755390977484021 4260163160602067904139127)
        ·
          refine ⟨6390244740903101856208691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4260163160602067904139127 6390244740903101856208691)
          ·
            refine ⟨9585367111354652784313037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6390244740903101856208691 9585367111354652784313037)
            ·
              refine ⟨3594512666757994794117389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9585367111354652784313037 3594512666757994794117389)
              ·
                refine ⟨1347942250034248047794021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3594512666757994794117389 1347942250034248047794021)
                ·
                  refine ⟨252739171881421508961379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1347942250034248047794021 252739171881421508961379)
                  ·
                    rfl

theorem cell22_2214935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 4].length) (baseStart_2214935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214935 prefixEnd_2214935 := by exact prefixLift 2214935
  have htrace : WordTrace (prefixWord ++ tailWord_2214935) baseStart_2214935 baseEnd_2214935 := by
    simpa [prefixWord, tailWord_2214935, baseEnd_2214935] using wordTrace_append hprefix tailTrace_2214935
  have hstable : (prefixWord ++ tailWord_2214935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214935).length < 2 ^ (prefixWord ++ tailWord_2214935).sum := by decide
  have hdescent : baseEnd_2214935 < baseStart_2214935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214946 : List Nat := [3, 3, 1, 1, 1, 3, 10]
def baseStart_2214946 : Nat := 118140960795 + 2214946 * 2 ^ 59
def prefixEnd_2214946 : Nat := 4983230072969 + 3 ^ 40 * 2214946 * 2
def baseEnd_2214946 : Nat := 28082269672928302402189

theorem tailTrace_2214946 : CollatzResearch.WordTrace tailWord_2214946 prefixEnd_2214946 28082269672928302402189 := by
  unfold tailWord_2214946
  simp only [CollatzResearch.WordTrace]
  refine ⟨20196429358409099876322173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53857144955757599670192461 20196429358409099876322173)
  ·
    refine ⟨7573661009403412453620815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20196429358409099876322173 7573661009403412453620815)
    ·
      refine ⟨11360491514105118680431223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7573661009403412453620815 11360491514105118680431223)
      ·
        refine ⟨17040737271157678020646835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11360491514105118680431223 17040737271157678020646835)
        ·
          refine ⟨25561105906736517030970253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17040737271157678020646835 25561105906736517030970253)
          ·
            refine ⟨9585414715026193886613845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25561105906736517030970253 9585414715026193886613845)
            ·
              refine ⟨28082269672928302402189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9585414715026193886613845 28082269672928302402189)
              ·
                rfl

theorem cell22_2214946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 10].length) (baseStart_2214946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214946 prefixEnd_2214946 := by exact prefixLift 2214946
  have htrace : WordTrace (prefixWord ++ tailWord_2214946) baseStart_2214946 baseEnd_2214946 := by
    simpa [prefixWord, tailWord_2214946, baseEnd_2214946] using wordTrace_append hprefix tailTrace_2214946
  have hstable : (prefixWord ++ tailWord_2214946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214946).length < 2 ^ (prefixWord ++ tailWord_2214946).sum := by decide
  have hdescent : baseEnd_2214946 < baseStart_2214946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214948 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 4, 4]
def baseStart_2214948 : Nat := 118140960795 + 2214948 * 2 ^ 59
def prefixEnd_2214948 : Nat := 4983230072969 + 3 ^ 40 * 2214948 * 2
def baseEnd_2214948 : Nat := 758221965809936826309097

theorem tailTrace_2214948 : CollatzResearch.WordTrace tailWord_2214948 prefixEnd_2214948 758221965809936826309097 := by
  unfold tailWord_2214948
  simp only [CollatzResearch.WordTrace]
  refine ⟨40392895189814576923430749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53857193586419435897907665 40392895189814576923430749)
  ·
    refine ⟨15147335696180466346286531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40392895189814576923430749 15147335696180466346286531)
    ·
      refine ⟨22721003544270699519429797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15147335696180466346286531 22721003544270699519429797)
      ·
        refine ⟨4260188164550756159893087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22721003544270699519429797 4260188164550756159893087)
        ·
          refine ⟨6390282246826134239839631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4260188164550756159893087 6390282246826134239839631)
          ·
            refine ⟨9585423370239201359759447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6390282246826134239839631 9585423370239201359759447)
            ·
              refine ⟨14378135055358802039639171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9585423370239201359759447 14378135055358802039639171)
              ·
                refine ⟨21567202583038203059458757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14378135055358802039639171 21567202583038203059458757)
                ·
                  refine ⟨4043850484319663073648517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21567202583038203059458757 4043850484319663073648517)
                  ·
                    refine ⟨758221965809936826309097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4043850484319663073648517 758221965809936826309097)
                    ·
                      rfl

theorem cell22_2214948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_2214948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214948 prefixEnd_2214948 := by exact prefixLift 2214948
  have htrace : WordTrace (prefixWord ++ tailWord_2214948) baseStart_2214948 baseEnd_2214948 := by
    simpa [prefixWord, tailWord_2214948, baseEnd_2214948] using wordTrace_append hprefix tailTrace_2214948
  have hstable : (prefixWord ++ tailWord_2214948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214948).length < 2 ^ (prefixWord ++ tailWord_2214948).sum := by decide
  have hdescent : baseEnd_2214948 < baseStart_2214948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214982 : List Nat := [6, 1, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_2214982 : Nat := 118140960795 + 2214982 * 2 ^ 59
def prefixEnd_2214982 : Nat := 4983230072969 + 3 ^ 40 * 2214982 * 2
def baseEnd_2214982 : Nat := 758233604704772070958993

theorem tailTrace_2214982 : CollatzResearch.WordTrace tailWord_2214982 prefixEnd_2214982 758233604704772070958993 := by
  unfold tailWord_2214982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2524594701922061801674975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53858020307670651769066133 2524594701922061801674975)
  ·
    refine ⟨3786892052883092702512463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2524594701922061801674975 3786892052883092702512463)
    ·
      refine ⟨5680338079324639053768695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3786892052883092702512463 5680338079324639053768695)
      ·
        refine ⟨8520507118986958580653043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5680338079324639053768695 8520507118986958580653043)
        ·
          refine ⟨12780760678480437870979565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8520507118986958580653043 12780760678480437870979565)
          ·
            refine ⟨4792785254430164201617337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12780760678480437870979565 4792785254430164201617337)
            ·
              refine ⟨3594588940822623151213003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4792785254430164201617337 3594588940822623151213003)
              ·
                refine ⟨5391883411233934726819505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3594588940822623151213003 5391883411233934726819505)
                ·
                  refine ⟨4043912558425451045114629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5391883411233934726819505 4043912558425451045114629)
                  ·
                    refine ⟨758233604704772070958993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4043912558425451045114629 758233604704772070958993)
                    ·
                      rfl

theorem cell22_2214982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_2214982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2214982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2214982 prefixEnd_2214982 := by exact prefixLift 2214982
  have htrace : WordTrace (prefixWord ++ tailWord_2214982) baseStart_2214982 baseEnd_2214982 := by
    simpa [prefixWord, tailWord_2214982, baseEnd_2214982] using wordTrace_append hprefix tailTrace_2214982
  have hstable : (prefixWord ++ tailWord_2214982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214982).length < 2 ^ (prefixWord ++ tailWord_2214982).sum := by decide
  have hdescent : baseEnd_2214982 < baseStart_2214982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215008 : List Nat := [2, 1, 1, 3, 2, 2, 4, 2, 5]
def baseStart_2215008 : Nat := 118140960795 + 2215008 * 2 ^ 59
def prefixEnd_2215008 : Nat := 4983230072969 + 3 ^ 40 * 2215008 * 2
def baseEnd_2215008 : Nat := 252747501678705556602971

theorem tailTrace_2215008 : CollatzResearch.WordTrace tailWord_2215008 prefixEnd_2215008 252747501678705556602971 := by
  unfold tailWord_2215008
  simp only [CollatzResearch.WordTrace]
  refine ⟨40393989379705892047022839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53858652506274522729363785 40393989379705892047022839)
  ·
    refine ⟨60590984069558838070534259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40393989379705892047022839 60590984069558838070534259)
    ·
      refine ⟨90886476104338257105801389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60590984069558838070534259 90886476104338257105801389)
      ·
        refine ⟨34082428539126846414675521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90886476104338257105801389 34082428539126846414675521)
        ·
          refine ⟨25561821404345134811006641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34082428539126846414675521 25561821404345134811006641)
          ·
            refine ⟨19171366053258851108254981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25561821404345134811006641 19171366053258851108254981)
            ·
              refine ⟨3594631134986034582797809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19171366053258851108254981 3594631134986034582797809)
              ·
                refine ⟨2695973351239525937098357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3594631134986034582797809 2695973351239525937098357)
                ·
                  refine ⟨252747501678705556602971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2695973351239525937098357 252747501678705556602971)
                  ·
                    rfl

theorem cell22_2215008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 5].length) (baseStart_2215008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215008 prefixEnd_2215008 := by exact prefixLift 2215008
  have htrace : WordTrace (prefixWord ++ tailWord_2215008) baseStart_2215008 baseEnd_2215008 := by
    simpa [prefixWord, tailWord_2215008, baseEnd_2215008] using wordTrace_append hprefix tailTrace_2215008
  have hstable : (prefixWord ++ tailWord_2215008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215008).length < 2 ^ (prefixWord ++ tailWord_2215008).sum := by decide
  have hdescent : baseEnd_2215008 < baseStart_2215008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215070 : List Nat := [4, 3, 1, 1, 2, 1, 1, 3, 6]
def baseStart_2215070 : Nat := 118140960795 + 2215070 * 2 ^ 59
def prefixEnd_2215070 : Nat := 4983230072969 + 3 ^ 40 * 2215070 * 2
def baseEnd_2215070 : Nat := 252754576301056391586241

theorem tailTrace_2215070 : CollatzResearch.WordTrace tailWord_2215070 prefixEnd_2215070 252754576301056391586241 := by
  unfold tailWord_2215070
  simp only [CollatzResearch.WordTrace]
  refine ⟨10098780010648396085350333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53860160056791445788535109 10098780010648396085350333)
  ·
    refine ⟨3787042503993148532006375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10098780010648396085350333 3787042503993148532006375)
    ·
      refine ⟨5680563755989722798009563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3787042503993148532006375 5680563755989722798009563)
      ·
        refine ⟨8520845633984584197014345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5680563755989722798009563 8520845633984584197014345)
        ·
          refine ⟨6390634225488438147760759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8520845633984584197014345 6390634225488438147760759)
          ·
            refine ⟨9585951338232657221641139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6390634225488438147760759 9585951338232657221641139)
            ·
              refine ⟨14378927007348985832461709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9585951338232657221641139 14378927007348985832461709)
              ·
                refine ⟨5392097627755869687173141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14378927007348985832461709 5392097627755869687173141)
                ·
                  refine ⟨252754576301056391586241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5392097627755869687173141 252754576301056391586241)
                  ·
                    rfl

theorem cell22_2215070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_2215070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215070 prefixEnd_2215070 := by exact prefixLift 2215070
  have htrace : WordTrace (prefixWord ++ tailWord_2215070) baseStart_2215070 baseEnd_2215070 := by
    simpa [prefixWord, tailWord_2215070, baseEnd_2215070] using wordTrace_append hprefix tailTrace_2215070
  have hstable : (prefixWord ++ tailWord_2215070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215070).length < 2 ^ (prefixWord ++ tailWord_2215070).sum := by decide
  have hdescent : baseEnd_2215070 < baseStart_2215070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215104 : List Nat := [2, 1, 1, 2, 7, 1, 1, 3, 4]
def baseStart_2215104 : Nat := 118140960795 + 2215104 * 2 ^ 59
def prefixEnd_2215104 : Nat := 4983230072969 + 3 ^ 40 * 2215104 * 2
def baseEnd_2215104 : Nat := 252758455932668139802873

theorem tailTrace_2215104 : CollatzResearch.WordTrace tailWord_2215104 prefixEnd_2215104 252758455932668139802873 := by
  unfold tailWord_2215104
  simp only [CollatzResearch.WordTrace]
  refine ⟨40395740083531996244770183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53860986778042661659693577 40395740083531996244770183)
  ·
    refine ⟨60593610125297994367155275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40395740083531996244770183 60593610125297994367155275)
    ·
      refine ⟨90890415187946991550732913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60593610125297994367155275 90890415187946991550732913)
      ·
        refine ⟨68167811390960243663049685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90890415187946991550732913 68167811390960243663049685)
        ·
          refine ⟨1597683079475630710852727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 68167811390960243663049685 1597683079475630710852727)
          ·
            refine ⟨2396524619213446066279091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1597683079475630710852727 2396524619213446066279091)
            ·
              refine ⟨3594786928820169099418637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2396524619213446066279091 3594786928820169099418637)
              ·
                refine ⟨1348045098307563412281989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3594786928820169099418637 1348045098307563412281989)
                ·
                  refine ⟨252758455932668139802873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1348045098307563412281989 252758455932668139802873)
                  ·
                    rfl

theorem cell22_2215104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 4].length) (baseStart_2215104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215104 prefixEnd_2215104 := by exact prefixLift 2215104
  have htrace : WordTrace (prefixWord ++ tailWord_2215104) baseStart_2215104 baseEnd_2215104 := by
    simpa [prefixWord, tailWord_2215104, baseEnd_2215104] using wordTrace_append hprefix tailTrace_2215104
  have hstable : (prefixWord ++ tailWord_2215104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215104).length < 2 ^ (prefixWord ++ tailWord_2215104).sum := by decide
  have hdescent : baseEnd_2215104 < baseStart_2215104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215205 : List Nat := [1, 3, 1, 2, 4, 2, 1, 2, 6]
def baseStart_2215205 : Nat := 118140960795 + 2215205 * 2 ^ 59
def prefixEnd_2215205 : Nat := 4983230072969 + 3 ^ 40 * 2215205 * 2
def baseEnd_2215205 : Nat := 252769980720691274211103

theorem tailTrace_2215205 : CollatzResearch.WordTrace tailWord_2215205 prefixEnd_2215205 252769980720691274211103 := by
  unfold tailWord_2215205
  simp only [CollatzResearch.WordTrace]
  refine ⟨80795163939698086738967069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53863442626465391159311379 80795163939698086738967069)
  ·
    refine ⟨30298186477386782527112651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80795163939698086738967069 30298186477386782527112651)
    ·
      refine ⟨45447279716080173790668977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30298186477386782527112651 45447279716080173790668977)
      ·
        refine ⟨34085459787060130343001733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45447279716080173790668977 34085459787060130343001733)
        ·
          refine ⟨6391023710073774439312825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34085459787060130343001733 6391023710073774439312825)
          ·
            refine ⟨4793267782555330829484619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6391023710073774439312825 4793267782555330829484619)
            ·
              refine ⟨7189901673832996244226929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4793267782555330829484619 7189901673832996244226929)
              ·
                refine ⟨5392426255374747183170197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7189901673832996244226929 5392426255374747183170197)
                ·
                  refine ⟨252769980720691274211103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5392426255374747183170197 252769980720691274211103)
                  ·
                    rfl

theorem cell22_2215205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_2215205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215205 prefixEnd_2215205 := by exact prefixLift 2215205
  have htrace : WordTrace (prefixWord ++ tailWord_2215205) baseStart_2215205 baseEnd_2215205 := by
    simpa [prefixWord, tailWord_2215205, baseEnd_2215205] using wordTrace_append hprefix tailTrace_2215205
  have hstable : (prefixWord ++ tailWord_2215205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215205).length < 2 ^ (prefixWord ++ tailWord_2215205).sum := by decide
  have hdescent : baseEnd_2215205 < baseStart_2215205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215267 : List Nat := [1, 1, 1, 5, 2, 4, 2, 6]
def baseStart_2215267 : Nat := 118140960795 + 2215267 * 2 ^ 59
def prefixEnd_2215267 : Nat := 4983230072969 + 3 ^ 40 * 2215267 * 2
def baseEnd_2215267 : Nat := 84259018447680703064791

theorem tailTrace_2215267 : CollatzResearch.WordTrace tailWord_2215267 prefixEnd_2215267 84259018447680703064791 := by
  unfold tailWord_2215267
  simp only [CollatzResearch.WordTrace]
  refine ⟨80797425265473471327724055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53864950176982314218482703 80797425265473471327724055)
  ·
    refine ⟨121196137898210206991586083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80797425265473471327724055 121196137898210206991586083)
    ·
      refine ⟨181794206847315310487379125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121196137898210206991586083 181794206847315310487379125)
      ·
        refine ⟨17043206891935810358191793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 181794206847315310487379125 17043206891935810358191793)
        ·
          refine ⟨12782405168951857768643845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17043206891935810358191793 12782405168951857768643845)
          ·
            refine ⟨2396700969178473331620721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12782405168951857768643845 2396700969178473331620721)
            ·
              refine ⟨1797525726883854998715541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2396700969178473331620721 1797525726883854998715541)
              ·
                refine ⟨84259018447680703064791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1797525726883854998715541 84259018447680703064791)
                ·
                  rfl

theorem cell22_2215267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 6].length) (baseStart_2215267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215267 prefixEnd_2215267 := by exact prefixLift 2215267
  have htrace : WordTrace (prefixWord ++ tailWord_2215267) baseStart_2215267 baseEnd_2215267 := by
    simpa [prefixWord, tailWord_2215267, baseEnd_2215267] using wordTrace_append hprefix tailTrace_2215267
  have hstable : (prefixWord ++ tailWord_2215267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215267).length < 2 ^ (prefixWord ++ tailWord_2215267).sum := by decide
  have hdescent : baseEnd_2215267 < baseStart_2215267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215299 : List Nat := [1, 1, 1, 3, 5, 3, 1, 1, 3, 3]
def baseStart_2215299 : Nat := 118140960795 + 2215299 * 2 ^ 59
def prefixEnd_2215299 : Nat := 4983230072969 + 3 ^ 40 * 2215299 * 2
def baseEnd_2215299 : Nat := 758342120283088910783021

theorem tailTrace_2215299 : CollatzResearch.WordTrace tailWord_2215299 prefixEnd_2215299 758342120283088910783021 := by
  unfold tailWord_2215299
  simp only [CollatzResearch.WordTrace]
  refine ⟨80798592401357540792888951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53865728267571693861925967 80798592401357540792888951)
  ·
    refine ⟨121197888602036311189333427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80798592401357540792888951 121197888602036311189333427)
    ·
      refine ⟨181796832903054466784000141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121197888602036311189333427 181796832903054466784000141)
      ·
        refine ⟨68173812338645425044000053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181796832903054466784000141 68173812338645425044000053)
        ·
          refine ⟨6391294906748008597875005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68173812338645425044000053 6391294906748008597875005)
          ·
            refine ⟨2396735590030503224203127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6391294906748008597875005 2396735590030503224203127)
            ·
              refine ⟨3595103385045754836304691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2396735590030503224203127 3595103385045754836304691)
              ·
                refine ⟨5392655077568632254457037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3595103385045754836304691 5392655077568632254457037)
                ·
                  refine ⟨2022245654088237095421389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5392655077568632254457037 2022245654088237095421389)
                  ·
                    refine ⟨758342120283088910783021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2022245654088237095421389 758342120283088910783021)
                    ·
                      rfl

theorem cell22_2215299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 3].length) (baseStart_2215299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215299 prefixEnd_2215299 := by exact prefixLift 2215299
  have htrace : WordTrace (prefixWord ++ tailWord_2215299) baseStart_2215299 baseEnd_2215299 := by
    simpa [prefixWord, tailWord_2215299, baseEnd_2215299] using wordTrace_append hprefix tailTrace_2215299
  have hstable : (prefixWord ++ tailWord_2215299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215299).length < 2 ^ (prefixWord ++ tailWord_2215299).sum := by decide
  have hdescent : baseEnd_2215299 < baseStart_2215299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215372 : List Nat := [2, 2, 1, 4, 2, 1, 1, 3, 1, 5]
def baseStart_2215372 : Nat := 118140960795 + 2215372 * 2 ^ 59
def prefixEnd_2215372 : Nat := 4983230072969 + 3 ^ 40 * 2215372 * 2
def baseEnd_2215372 : Nat := 758367109674941053707797

theorem tailTrace_2215372 : CollatzResearch.WordTrace tailWord_2215372 prefixEnd_2215372 758367109674941053707797 := by
  unfold tailWord_2215372
  simp only [CollatzResearch.WordTrace]
  refine ⟨40400627465046537130148185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53867503286728716173530913 40400627465046537130148185)
  ·
    refine ⟨30300470598784902847611139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40400627465046537130148185 30300470598784902847611139)
    ·
      refine ⟨45450705898177354271416709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30300470598784902847611139 45450705898177354271416709)
      ·
        refine ⟨8522007355908253925890633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45450705898177354271416709 8522007355908253925890633)
        ·
          refine ⟨6391505516931190444417975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8522007355908253925890633 6391505516931190444417975)
          ·
            refine ⟨9587258275396785666626963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6391505516931190444417975 9587258275396785666626963)
            ·
              refine ⟨14380887413095178499940445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9587258275396785666626963 14380887413095178499940445)
              ·
                refine ⟨5392832779910691937477667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14380887413095178499940445 5392832779910691937477667)
                ·
                  refine ⟨8089249169866037906216501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5392832779910691937477667 8089249169866037906216501)
                  ·
                    refine ⟨758367109674941053707797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8089249169866037906216501 758367109674941053707797)
                    ·
                      rfl

theorem cell22_2215372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_2215372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215372 prefixEnd_2215372 := by exact prefixLift 2215372
  have htrace : WordTrace (prefixWord ++ tailWord_2215372) baseStart_2215372 baseEnd_2215372 := by
    simpa [prefixWord, tailWord_2215372, baseEnd_2215372] using wordTrace_append hprefix tailTrace_2215372
  have hstable : (prefixWord ++ tailWord_2215372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215372).length < 2 ^ (prefixWord ++ tailWord_2215372).sum := by decide
  have hdescent : baseEnd_2215372 < baseStart_2215372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215402 : List Nat := [3, 1, 3, 1, 4, 1, 9]
def baseStart_2215402 : Nat := 118140960795 + 2215402 * 2 ^ 59
def prefixEnd_2215402 : Nat := 4983230072969 + 3 ^ 40 * 2215402 * 2
def baseEnd_2215402 : Nat := 28088051084741887979915

theorem tailTrace_2215402 : CollatzResearch.WordTrace tailWord_2215402 prefixEnd_2215402 28088051084741887979915 := by
  unfold tailWord_2215402
  simp only [CollatzResearch.WordTrace]
  refine ⟨20200587279996097345972115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53868232746656259589258973 20200587279996097345972115)
  ·
    refine ⟨30300880919994146018958173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20200587279996097345972115 30300880919994146018958173)
    ·
      refine ⟨11362830344997804757109315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30300880919994146018958173 11362830344997804757109315)
      ·
        refine ⟨17044245517496707135663973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11362830344997804757109315 17044245517496707135663973)
        ·
          refine ⟨3195796034530632587936995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17044245517496707135663973 3195796034530632587936995)
          ·
            refine ⟨4793694051795948881905493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3195796034530632587936995 4793694051795948881905493)
            ·
              refine ⟨28088051084741887979915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4793694051795948881905493 28088051084741887979915)
              ·
                rfl

theorem cell22_2215402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 9].length) (baseStart_2215402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215402 prefixEnd_2215402 := by exact prefixLift 2215402
  have htrace : WordTrace (prefixWord ++ tailWord_2215402) baseStart_2215402 baseEnd_2215402 := by
    simpa [prefixWord, tailWord_2215402, baseEnd_2215402] using wordTrace_append hprefix tailTrace_2215402
  have hstable : (prefixWord ++ tailWord_2215402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215402).length < 2 ^ (prefixWord ++ tailWord_2215402).sum := by decide
  have hdescent : baseEnd_2215402 < baseStart_2215402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215415 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 2, 6]
def baseStart_2215415 : Nat := 118140960795 + 2215415 * 2 ^ 59
def prefixEnd_2215415 : Nat := 4983230072969 + 3 ^ 40 * 2215415 * 2
def baseEnd_2215415 : Nat := 758381829453703274882665

theorem tailTrace_2215415 : CollatzResearch.WordTrace tailWord_2215415 prefixEnd_2215415 758381829453703274882665 := by
  unfold tailWord_2215415
  simp only [CollatzResearch.WordTrace]
  refine ⟨80802823268937292604111699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53868548845958195069407799 80802823268937292604111699)
  ·
    refine ⟨121204234903405938906167549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80802823268937292604111699 121204234903405938906167549)
    ·
      refine ⟨45451588088777227089812831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121204234903405938906167549 45451588088777227089812831)
      ·
        refine ⟨68177382133165840634719247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45451588088777227089812831 68177382133165840634719247)
        ·
          refine ⟨102266073199748760952078871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68177382133165840634719247 102266073199748760952078871)
          ·
            refine ⟨153399109799623141428118307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102266073199748760952078871 153399109799623141428118307)
            ·
              refine ⟨230098664699434712142177461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153399109799623141428118307 230098664699434712142177461)
              ·
                refine ⟨21571749815572004263329137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 230098664699434712142177461 21571749815572004263329137)
                ·
                  refine ⟨16178812361679003197496853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21571749815572004263329137 16178812361679003197496853)
                  ·
                    refine ⟨758381829453703274882665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16178812361679003197496853 758381829453703274882665)
                    ·
                      rfl

theorem cell22_2215415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_2215415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215415 prefixEnd_2215415 := by exact prefixLift 2215415
  have htrace : WordTrace (prefixWord ++ tailWord_2215415) baseStart_2215415 baseEnd_2215415 := by
    simpa [prefixWord, tailWord_2215415, baseEnd_2215415] using wordTrace_append hprefix tailTrace_2215415
  have hstable : (prefixWord ++ tailWord_2215415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215415).length < 2 ^ (prefixWord ++ tailWord_2215415).sum := by decide
  have hdescent : baseEnd_2215415 < baseStart_2215415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215434 : List Nat := [3, 1, 2, 2, 2, 2, 2, 2, 3, 3]
def baseStart_2215434 : Nat := 118140960795 + 2215434 * 2 ^ 59
def prefixEnd_2215434 : Nat := 4983230072969 + 3 ^ 40 * 2215434 * 2
def baseEnd_2215434 : Nat := 758388333541993558657607

theorem tailTrace_2215434 : CollatzResearch.WordTrace tailWord_2215434 prefixEnd_2215434 758388333541993558657607 := by
  unfold tailWord_2215434
  simp only [CollatzResearch.WordTrace]
  refine ⟨20200879063967114712263339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53869010837245639232702237 20200879063967114712263339)
  ·
    refine ⟨30301318595950672068395009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20200879063967114712263339 30301318595950672068395009)
    ·
      refine ⟨22725988946963004051296257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30301318595950672068395009 22725988946963004051296257)
      ·
        refine ⟨17044491710222253038472193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22725988946963004051296257 17044491710222253038472193)
        ·
          refine ⟨12783368782666689778854145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17044491710222253038472193 12783368782666689778854145)
          ·
            refine ⟨9587526587000017334140609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12783368782666689778854145 9587526587000017334140609)
            ·
              refine ⟨7190644940250013000605457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9587526587000017334140609 7190644940250013000605457)
              ·
                refine ⟨5392983705187509750454093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7190644940250013000605457 5392983705187509750454093)
                ·
                  refine ⟨2022368889445316156420285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5392983705187509750454093 2022368889445316156420285)
                  ·
                    refine ⟨758388333541993558657607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2022368889445316156420285 758388333541993558657607)
                    ·
                      rfl

theorem cell22_2215434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_2215434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215434 prefixEnd_2215434 := by exact prefixLift 2215434
  have htrace : WordTrace (prefixWord ++ tailWord_2215434) baseStart_2215434 baseEnd_2215434 := by
    simpa [prefixWord, tailWord_2215434, baseEnd_2215434] using wordTrace_append hprefix tailTrace_2215434
  have hstable : (prefixWord ++ tailWord_2215434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215434).length < 2 ^ (prefixWord ++ tailWord_2215434).sum := by decide
  have hdescent : baseEnd_2215434 < baseStart_2215434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215436 : List Nat := [2, 2, 1, 2, 6, 1, 2, 6]
def baseStart_2215436 : Nat := 118140960795 + 2215436 * 2 ^ 59
def prefixEnd_2215436 : Nat := 4983230072969 + 3 ^ 40 * 2215436 * 2
def baseEnd_2215436 : Nat := 84265446464762913345289

theorem tailTrace_2215436 : CollatzResearch.WordTrace tailWord_2215436 prefixEnd_2215436 84265446464762913345289 := by
  unfold tailWord_2215436
  simp only [CollatzResearch.WordTrace]
  refine ⟨40401794600930606595313081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53869059467907475460417441 40401794600930606595313081)
  ·
    refine ⟨30301345950697954946484811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40401794600930606595313081 30301345950697954946484811)
    ·
      refine ⟨45452018926046932419727217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30301345950697954946484811 45452018926046932419727217)
      ·
        refine ⟨34089014194535199314795413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45452018926046932419727217 34089014194535199314795413)
        ·
          refine ⟨1597922540368837467881035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34089014194535199314795413 1597922540368837467881035)
          ·
            refine ⟨2396883810553256201821553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1597922540368837467881035 2396883810553256201821553)
            ·
              refine ⟨1797662857914942151366165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2396883810553256201821553 1797662857914942151366165)
              ·
                refine ⟨84265446464762913345289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1797662857914942151366165 84265446464762913345289)
                ·
                  rfl

theorem cell22_2215436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 6].length) (baseStart_2215436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215436 prefixEnd_2215436 := by exact prefixLift 2215436
  have htrace : WordTrace (prefixWord ++ tailWord_2215436) baseStart_2215436 baseEnd_2215436 := by
    simpa [prefixWord, tailWord_2215436, baseEnd_2215436] using wordTrace_append hprefix tailTrace_2215436
  have hstable : (prefixWord ++ tailWord_2215436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215436).length < 2 ^ (prefixWord ++ tailWord_2215436).sum := by decide
  have hdescent : baseEnd_2215436 < baseStart_2215436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215481 : List Nat := [1, 2, 1, 5, 1, 4, 2, 1, 5]
def baseStart_2215481 : Nat := 118140960795 + 2215481 * 2 ^ 59
def prefixEnd_2215481 : Nat := 4983230072969 + 3 ^ 40 * 2215481 * 2
def baseEnd_2215481 : Nat := 252801474200833700910821

theorem tailTrace_2215481 : CollatzResearch.WordTrace tailWord_2215481 prefixEnd_2215481 252801474200833700910821 := by
  unfold tailWord_2215481
  simp only [CollatzResearch.WordTrace]
  refine ⟨80805230486698185876014297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53870153657798790584009531 80805230486698185876014297)
  ·
    refine ⟨60603922865023639407010723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80805230486698185876014297 60603922865023639407010723)
    ·
      refine ⟨90905884297535459110516085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60603922865023639407010723 90905884297535459110516085)
      ·
        refine ⟨8522426652893949291610883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90905884297535459110516085 8522426652893949291610883)
        ·
          refine ⟨12783639979340923937416325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8522426652893949291610883 12783639979340923937416325)
          ·
            refine ⟨2396932496126423238265561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12783639979340923937416325 2396932496126423238265561)
            ·
              refine ⟨1797699372094817428699171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2396932496126423238265561 1797699372094817428699171)
              ·
                refine ⟨2696549058142226143048757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1797699372094817428699171 2696549058142226143048757)
                ·
                  refine ⟨252801474200833700910821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2696549058142226143048757 252801474200833700910821)
                  ·
                    rfl

theorem cell22_2215481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 5].length) (baseStart_2215481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215481 prefixEnd_2215481 := by exact prefixLift 2215481
  have htrace : WordTrace (prefixWord ++ tailWord_2215481) baseStart_2215481 baseEnd_2215481 := by
    simpa [prefixWord, tailWord_2215481, baseEnd_2215481] using wordTrace_append hprefix tailTrace_2215481
  have hstable : (prefixWord ++ tailWord_2215481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215481).length < 2 ^ (prefixWord ++ tailWord_2215481).sum := by decide
  have hdescent : baseEnd_2215481 < baseStart_2215481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215509 : List Nat := [1, 3, 2, 2, 1, 1, 1, 7, 4]
def baseStart_2215509 : Nat := 118140960795 + 2215509 * 2 ^ 59
def prefixEnd_2215509 : Nat := 4983230072969 + 3 ^ 40 * 2215509 * 2
def baseEnd_2215509 : Nat := 252804669191572787677459

theorem tailTrace_2215509 : CollatzResearch.WordTrace tailWord_2215509 prefixEnd_2215509 252804669191572787677459 := by
  unfold tailWord_2215509
  simp only [CollatzResearch.WordTrace]
  refine ⟨80806251730596746658033581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53870834487064497772022387 80806251730596746658033581)
  ·
    refine ⟨30302344398973779996762593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80806251730596746658033581 30302344398973779996762593)
    ·
      refine ⟨22726758299230334997571945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30302344398973779996762593 22726758299230334997571945)
      ·
        refine ⟨17045068724422751248178959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22726758299230334997571945 17045068724422751248178959)
        ·
          refine ⟨25567603086634126872268439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17045068724422751248178959 25567603086634126872268439)
          ·
            refine ⟨38351404629951190308402659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25567603086634126872268439 38351404629951190308402659)
            ·
              refine ⟨57527106944926785462603989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38351404629951190308402659 57527106944926785462603989)
              ·
                refine ⟨1348291569021721534279781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 57527106944926785462603989 1348291569021721534279781)
                ·
                  refine ⟨252804669191572787677459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1348291569021721534279781 252804669191572787677459)
                  ·
                    rfl

theorem cell22_2215509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 4].length) (baseStart_2215509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215509 prefixEnd_2215509 := by exact prefixLift 2215509
  have htrace : WordTrace (prefixWord ++ tailWord_2215509) baseStart_2215509 baseEnd_2215509 := by
    simpa [prefixWord, tailWord_2215509, baseEnd_2215509] using wordTrace_append hprefix tailTrace_2215509
  have hstable : (prefixWord ++ tailWord_2215509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215509).length < 2 ^ (prefixWord ++ tailWord_2215509).sum := by decide
  have hdescent : baseEnd_2215509 < baseStart_2215509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215511 : List Nat := [1, 1, 3, 2, 2, 4, 3, 1, 1, 4]
def baseStart_2215511 : Nat := 118140960795 + 2215511 * 2 ^ 59
def prefixEnd_2215511 : Nat := 4983230072969 + 3 ^ 40 * 2215511 * 2
def baseEnd_2215511 : Nat := 758414692215591024482371

theorem tailTrace_2215511 : CollatzResearch.WordTrace tailWord_2215511 prefixEnd_2215511 758414692215591024482371 := by
  unfold tailWord_2215511
  simp only [CollatzResearch.WordTrace]
  refine ⟨80806324676589500999606387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53870883117726333999737591 80806324676589500999606387)
  ·
    refine ⟨121209487014884251499409581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80806324676589500999606387 121209487014884251499409581)
    ·
      refine ⟨45453557630581594312278593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121209487014884251499409581 45453557630581594312278593)
      ·
        refine ⟨34090168222936195734208945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45453557630581594312278593 34090168222936195734208945)
        ·
          refine ⟨25567626167202146800656709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34090168222936195734208945 25567626167202146800656709)
          ·
            refine ⟨4793929906350402525123133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25567626167202146800656709 4793929906350402525123133)
            ·
              refine ⟨1797723714881400946921175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4793929906350402525123133 1797723714881400946921175)
              ·
                refine ⟨2696585572322101420381763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1797723714881400946921175 2696585572322101420381763)
                ·
                  refine ⟨4044878358483152130572645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2696585572322101420381763 4044878358483152130572645)
                  ·
                    refine ⟨758414692215591024482371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4044878358483152130572645 758414692215591024482371)
                    ·
                      rfl

theorem cell22_2215511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 1, 4].length) (baseStart_2215511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215511 prefixEnd_2215511 := by exact prefixLift 2215511
  have htrace : WordTrace (prefixWord ++ tailWord_2215511) baseStart_2215511 baseEnd_2215511 := by
    simpa [prefixWord, tailWord_2215511, baseEnd_2215511] using wordTrace_append hprefix tailTrace_2215511
  have hstable : (prefixWord ++ tailWord_2215511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215511).length < 2 ^ (prefixWord ++ tailWord_2215511).sum := by decide
  have hdescent : baseEnd_2215511 < baseStart_2215511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215541 : List Nat := [1, 3, 4, 2, 1, 2, 2, 1, 1, 5]
def baseStart_2215541 : Nat := 118140960795 + 2215541 * 2 ^ 59
def prefixEnd_2215541 : Nat := 4983230072969 + 3 ^ 40 * 2215541 * 2
def baseEnd_2215541 : Nat := 758424961828680946232279

theorem tailTrace_2215541 : CollatzResearch.WordTrace tailWord_2215541 prefixEnd_2215541 758424961828680946232279 := by
  unfold tailWord_2215541
  simp only [CollatzResearch.WordTrace]
  refine ⟨80807418866480816123198477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53871612577653877415465651 80807418866480816123198477)
  ·
    refine ⟨30302782074930306046199429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80807418866480816123198477 30302782074930306046199429)
    ·
      refine ⟨5681771639049432383662393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30302782074930306046199429 5681771639049432383662393)
      ·
        refine ⟨4261328729287074287746795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5681771639049432383662393 4261328729287074287746795)
        ·
          refine ⟨6391993093930611431620193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4261328729287074287746795 6391993093930611431620193)
          ·
            refine ⟨4793994820447958573715145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6391993093930611431620193 4793994820447958573715145)
            ·
              refine ⟨3595496115335968930286359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4793994820447958573715145 3595496115335968930286359)
              ·
                refine ⟨5393244173003953395429539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3595496115335968930286359 5393244173003953395429539)
                ·
                  refine ⟨8089866259505930093144309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5393244173003953395429539 8089866259505930093144309)
                  ·
                    refine ⟨758424961828680946232279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8089866259505930093144309 758424961828680946232279)
                    ·
                      rfl

theorem cell22_2215541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_2215541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215541 prefixEnd_2215541 := by exact prefixLift 2215541
  have htrace : WordTrace (prefixWord ++ tailWord_2215541) baseStart_2215541 baseEnd_2215541 := by
    simpa [prefixWord, tailWord_2215541, baseEnd_2215541] using wordTrace_append hprefix tailTrace_2215541
  have hstable : (prefixWord ++ tailWord_2215541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215541).length < 2 ^ (prefixWord ++ tailWord_2215541).sum := by decide
  have hdescent : baseEnd_2215541 < baseStart_2215541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215592 : List Nat := [2, 1, 7, 1, 2, 1, 1, 1, 1, 5]
def baseStart_2215592 : Nat := 118140960795 + 2215592 * 2 ^ 59
def prefixEnd_2215592 : Nat := 4983230072969 + 3 ^ 40 * 2215592 * 2
def baseEnd_2215592 : Nat := 758442420170933813207123

theorem tailTrace_2215592 : CollatzResearch.WordTrace tailWord_2215592 prefixEnd_2215592 758442420170933813207123 := by
  unfold tailWord_2215592
  simp only [CollatzResearch.WordTrace]
  refine ⟨40404639494648025916652515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53872852659530701222203353 40404639494648025916652515)
  ·
    refine ⟨60606959241972038874978773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40404639494648025916652515 60606959241972038874978773)
    ·
      refine ⟨1420475607233719661132315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 60606959241972038874978773 1420475607233719661132315)
      ·
        refine ⟨2130713410850579491698473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1420475607233719661132315 2130713410850579491698473)
        ·
          refine ⟨1598035058137934618773855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2130713410850579491698473 1598035058137934618773855)
          ·
            refine ⟨2397052587206901928160783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1598035058137934618773855 2397052587206901928160783)
            ·
              refine ⟨3595578880810352892241175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2397052587206901928160783 3595578880810352892241175)
              ·
                refine ⟨5393368321215529338361763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3595578880810352892241175 5393368321215529338361763)
                ·
                  refine ⟨8090052481823294007542645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5393368321215529338361763 8090052481823294007542645)
                  ·
                    refine ⟨758442420170933813207123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8090052481823294007542645 758442420170933813207123)
                    ·
                      rfl

theorem cell22_2215592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_2215592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215592 prefixEnd_2215592 := by exact prefixLift 2215592
  have htrace : WordTrace (prefixWord ++ tailWord_2215592) baseStart_2215592 baseEnd_2215592 := by
    simpa [prefixWord, tailWord_2215592, baseEnd_2215592] using wordTrace_append hprefix tailTrace_2215592
  have hstable : (prefixWord ++ tailWord_2215592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215592).length < 2 ^ (prefixWord ++ tailWord_2215592).sum := by decide
  have hdescent : baseEnd_2215592 < baseStart_2215592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215627 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 8]
def baseStart_2215627 : Nat := 118140960795 + 2215627 * 2 ^ 59
def prefixEnd_2215627 : Nat := 4983230072969 + 3 ^ 40 * 2215627 * 2
def baseEnd_2215627 : Nat := 252818133795401796194005

theorem tailTrace_2215627 : CollatzResearch.WordTrace tailWord_2215627 prefixEnd_2215627 252818133795401796194005 := by
  unfold tailWord_2215627
  simp only [CollatzResearch.WordTrace]
  refine ⟨80810555544169252810829135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53873703696112835207219423 80810555544169252810829135)
  ·
    refine ⟨121215833316253879216243703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80810555544169252810829135 121215833316253879216243703)
    ·
      refine ⟨181823749974380818824365555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121215833316253879216243703 181823749974380818824365555)
      ·
        refine ⟨272735624961571228236548333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181823749974380818824365555 272735624961571228236548333)
        ·
          refine ⟨102275859360589210588705625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 272735624961571228236548333 102275859360589210588705625)
          ·
            refine ⟨76706894520441907941529219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102275859360589210588705625 76706894520441907941529219)
            ·
              refine ⟨115060341780662861912293829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76706894520441907941529219 115060341780662861912293829)
              ·
                refine ⟨21573814083874286608555093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115060341780662861912293829 21573814083874286608555093)
                ·
                  refine ⟨252818133795401796194005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21573814083874286608555093 252818133795401796194005)
                  ·
                    rfl

theorem cell22_2215627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 8].length) (baseStart_2215627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215627 prefixEnd_2215627 := by exact prefixLift 2215627
  have htrace : WordTrace (prefixWord ++ tailWord_2215627) baseStart_2215627 baseEnd_2215627 := by
    simpa [prefixWord, tailWord_2215627, baseEnd_2215627] using wordTrace_append hprefix tailTrace_2215627
  have hstable : (prefixWord ++ tailWord_2215627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215627).length < 2 ^ (prefixWord ++ tailWord_2215627).sum := by decide
  have hdescent : baseEnd_2215627 < baseStart_2215627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215706 : List Nat := [3, 1, 1, 3, 2, 4, 1, 7]
def baseStart_2215706 : Nat := 118140960795 + 2215706 * 2 ^ 59
def prefixEnd_2215706 : Nat := 4983230072969 + 3 ^ 40 * 2215706 * 2
def baseEnd_2215706 : Nat := 84275716077852835095197

theorem tailTrace_2215706 : CollatzResearch.WordTrace tailWord_2215706 prefixEnd_2215706 84275716077852835095197 := by
  unfold tailWord_2215706
  simp only [CollatzResearch.WordTrace]
  refine ⟨20203359227720762325738743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53875624607255366201969981 20203359227720762325738743)
  ·
    refine ⟨30305038841581143488608115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20203359227720762325738743 30305038841581143488608115)
    ·
      refine ⟨45457558262371715232912173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30305038841581143488608115 45457558262371715232912173)
      ·
        refine ⟨17046584348389393212342065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45457558262371715232912173 17046584348389393212342065)
        ·
          refine ⟨12784938261292044909256549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17046584348389393212342065 12784938261292044909256549)
          ·
            refine ⟨2397175923992258420485603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12784938261292044909256549 2397175923992258420485603)
            ·
              refine ⟨3595763885988387630728405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2397175923992258420485603 3595763885988387630728405)
              ·
                refine ⟨84275716077852835095197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3595763885988387630728405 84275716077852835095197)
                ·
                  rfl

theorem cell22_2215706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 7].length) (baseStart_2215706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215706 prefixEnd_2215706 := by exact prefixLift 2215706
  have htrace : WordTrace (prefixWord ++ tailWord_2215706) baseStart_2215706 baseEnd_2215706 := by
    simpa [prefixWord, tailWord_2215706, baseEnd_2215706] using wordTrace_append hprefix tailTrace_2215706
  have hstable : (prefixWord ++ tailWord_2215706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215706).length < 2 ^ (prefixWord ++ tailWord_2215706).sum := by decide
  have hdescent : baseEnd_2215706 < baseStart_2215706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215749 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 4, 5]
def baseStart_2215749 : Nat := 118140960795 + 2215749 * 2 ^ 59
def prefixEnd_2215749 : Nat := 4983230072969 + 3 ^ 40 * 2215749 * 2
def baseEnd_2215749 : Nat := 758496164479437737031641

theorem tailTrace_2215749 : CollatzResearch.WordTrace tailWord_2215749 prefixEnd_2215749 758496164479437737031641 := by
  unfold tailWord_2215749
  simp only [CollatzResearch.WordTrace]
  refine ⟨80815005249727267646770301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53876670166484845097846867 80815005249727267646770301)
  ·
    refine ⟨30305626968647725367538863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80815005249727267646770301 30305626968647725367538863)
    ·
      refine ⟨45458440452971588051308295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30305626968647725367538863 45458440452971588051308295)
      ·
        refine ⟨68187660679457382076962443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45458440452971588051308295 68187660679457382076962443)
        ·
          refine ⟨102281491019186073115443665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68187660679457382076962443 102281491019186073115443665)
          ·
            refine ⟨76711118264389554836582749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102281491019186073115443665 76711118264389554836582749)
            ·
              refine ⟨28766669349146083063718531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76711118264389554836582749 28766669349146083063718531)
              ·
                refine ⟨43150004023719124595577797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28766669349146083063718531 43150004023719124595577797)
                ·
                  refine ⟨8090625754447335861670837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43150004023719124595577797 8090625754447335861670837)
                  ·
                    refine ⟨758496164479437737031641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8090625754447335861670837 758496164479437737031641)
                    ·
                      rfl

theorem cell22_2215749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_2215749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215749 prefixEnd_2215749 := by exact prefixLift 2215749
  have htrace : WordTrace (prefixWord ++ tailWord_2215749) baseStart_2215749 baseEnd_2215749 := by
    simpa [prefixWord, tailWord_2215749, baseEnd_2215749] using wordTrace_append hprefix tailTrace_2215749
  have hstable : (prefixWord ++ tailWord_2215749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215749).length < 2 ^ (prefixWord ++ tailWord_2215749).sum := by decide
  have hdescent : baseEnd_2215749 < baseStart_2215749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215751 : List Nat := [1, 1, 4, 1, 2, 1, 5, 2, 5]
def baseStart_2215751 : Nat := 118140960795 + 2215751 * 2 ^ 59
def prefixEnd_2215751 : Nat := 4983230072969 + 3 ^ 40 * 2215751 * 2
def baseEnd_2215751 : Nat := 252832283040103466160545

theorem tailTrace_2215751 : CollatzResearch.WordTrace tailWord_2215751 prefixEnd_2215751 252832283040103466160545 := by
  unfold tailWord_2215751
  simp only [CollatzResearch.WordTrace]
  refine ⟨80815078195720021988343107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53876718797146681325562071 80815078195720021988343107)
  ·
    refine ⟨121222617293580032982514661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80815078195720021988343107 121222617293580032982514661)
    ·
      refine ⟨22729240742546256184221499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121222617293580032982514661 22729240742546256184221499)
      ·
        refine ⟨34093861113819384276332249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22729240742546256184221499 34093861113819384276332249)
        ·
          refine ⟨25570395835364538207249187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34093861113819384276332249 25570395835364538207249187)
          ·
            refine ⟨38355593753046807310873781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25570395835364538207249187 38355593753046807310873781)
            ·
              refine ⟨3595836914348138185394417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38355593753046807310873781 3595836914348138185394417)
              ·
                refine ⟨2696877685761103639045813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3595836914348138185394417 2696877685761103639045813)
                ·
                  refine ⟨252832283040103466160545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2696877685761103639045813 252832283040103466160545)
                  ·
                    rfl

theorem cell22_2215751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 5].length) (baseStart_2215751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215751 prefixEnd_2215751 := by exact prefixLift 2215751
  have htrace : WordTrace (prefixWord ++ tailWord_2215751) baseStart_2215751 baseEnd_2215751 := by
    simpa [prefixWord, tailWord_2215751, baseEnd_2215751] using wordTrace_append hprefix tailTrace_2215751
  have hstable : (prefixWord ++ tailWord_2215751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215751).length < 2 ^ (prefixWord ++ tailWord_2215751).sum := by decide
  have hdescent : baseEnd_2215751 < baseStart_2215751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215824 : List Nat := [2, 1, 1, 1, 1, 1, 2, 13]
def baseStart_2215824 : Nat := 118140960795 + 2215824 * 2 ^ 59
def prefixEnd_2215824 : Nat := 4983230072969 + 3 ^ 40 * 2215824 * 2
def baseEnd_2215824 : Nat := 84280204279129171267379

theorem tailTrace_2215824 : CollatzResearch.WordTrace tailWord_2215824 prefixEnd_2215824 84280204279129171267379 := by
  unfold tailWord_2215824
  simp only [CollatzResearch.WordTrace]
  refine ⟨40408870362227777727875263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53878493816303703637167017 40408870362227777727875263)
  ·
    refine ⟨60613305543341666591812895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40408870362227777727875263 60613305543341666591812895)
    ·
      refine ⟨90919958315012499887719343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60613305543341666591812895 90919958315012499887719343)
      ·
        refine ⟨136379937472518749831579015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90919958315012499887719343 136379937472518749831579015)
        ·
          refine ⟨204569906208778124747368523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136379937472518749831579015 204569906208778124747368523)
          ·
            refine ⟨306854859313167187121052785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204569906208778124747368523 306854859313167187121052785)
            ·
              refine ⟨230141144484875390340789589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 306854859313167187121052785 230141144484875390340789589)
              ·
                refine ⟨84280204279129171267379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 230141144484875390340789589 84280204279129171267379)
                ·
                  rfl

theorem cell22_2215824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 13].length) (baseStart_2215824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215824 prefixEnd_2215824 := by exact prefixLift 2215824
  have htrace : WordTrace (prefixWord ++ tailWord_2215824) baseStart_2215824 baseEnd_2215824 := by
    simpa [prefixWord, tailWord_2215824, baseEnd_2215824] using wordTrace_append hprefix tailTrace_2215824
  have hstable : (prefixWord ++ tailWord_2215824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215824).length < 2 ^ (prefixWord ++ tailWord_2215824).sum := by decide
  have hdescent : baseEnd_2215824 < baseStart_2215824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215832 : List Nat := [2, 1, 2, 6, 1, 2, 1, 2, 1, 4]
def baseStart_2215832 : Nat := 118140960795 + 2215832 * 2 ^ 59
def prefixEnd_2215832 : Nat := 4983230072969 + 3 ^ 40 * 2215832 * 2
def baseEnd_2215832 : Nat := 758524577075653187206387

theorem tailTrace_2215832 : CollatzResearch.WordTrace tailWord_2215832 prefixEnd_2215832 758524577075653187206387 := by
  unfold tailWord_2215832
  simp only [CollatzResearch.WordTrace]
  refine ⟨40409016254213286411020875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53878688338951048548027833 40409016254213286411020875)
  ·
    refine ⟨60613524381319929616531313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40409016254213286411020875 60613524381319929616531313)
    ·
      refine ⟨45460143285989947212398485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60613524381319929616531313 45460143285989947212398485)
      ·
        refine ⟨2130944216530778775581179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 45460143285989947212398485 2130944216530778775581179)
        ·
          refine ⟨3196416324796168163371769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2130944216530778775581179 3196416324796168163371769)
          ·
            refine ⟨2397312243597126122528827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3196416324796168163371769 2397312243597126122528827)
            ·
              refine ⟨3595968365395689183793241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2397312243597126122528827 3595968365395689183793241)
              ·
                refine ⟨2696976274046766887844931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3595968365395689183793241 2696976274046766887844931)
                ·
                  refine ⟨4045464411070150331767397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2696976274046766887844931 4045464411070150331767397)
                  ·
                    refine ⟨758524577075653187206387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4045464411070150331767397 758524577075653187206387)
                    ·
                      rfl

theorem cell22_2215832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 1, 4].length) (baseStart_2215832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215832 prefixEnd_2215832 := by exact prefixLift 2215832
  have htrace : WordTrace (prefixWord ++ tailWord_2215832) baseStart_2215832 baseEnd_2215832 := by
    simpa [prefixWord, tailWord_2215832, baseEnd_2215832] using wordTrace_append hprefix tailTrace_2215832
  have hstable : (prefixWord ++ tailWord_2215832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215832).length < 2 ^ (prefixWord ++ tailWord_2215832).sum := by decide
  have hdescent : baseEnd_2215832 < baseStart_2215832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215894 : List Nat := [5, 2, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_2215894 : Nat := 118140960795 + 2215894 * 2 ^ 59
def prefixEnd_2215894 : Nat := 4983230072969 + 3 ^ 40 * 2215894 * 2
def baseEnd_2215894 : Nat := 758545800942705692156197

theorem tailTrace_2215894 : CollatzResearch.WordTrace tailWord_2215894 prefixEnd_2215894 758545800942705692156197 := by
  unfold tailWord_2215894
  simp only [CollatzResearch.WordTrace]
  refine ⟨5051268364637622338174921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53880195889467971607199157 5051268364637622338174921)
  ·
    refine ⟨3788451273478216753631191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5051268364637622338174921 3788451273478216753631191)
    ·
      refine ⟨5682676910217325130446787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3788451273478216753631191 5682676910217325130446787)
      ·
        refine ⟨8524015365325987695670181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5682676910217325130446787 8524015365325987695670181)
        ·
          refine ⟨1598252880998622692938159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8524015365325987695670181 1598252880998622692938159)
          ·
            refine ⟨2397379321497934039407239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1598252880998622692938159 2397379321497934039407239)
            ·
              refine ⟨3596068982246901059110859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2397379321497934039407239 3596068982246901059110859)
              ·
                refine ⟨5394103473370351588666289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3596068982246901059110859 5394103473370351588666289)
                ·
                  refine ⟨4045577605027763691499717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5394103473370351588666289 4045577605027763691499717)
                  ·
                    refine ⟨758545800942705692156197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4045577605027763691499717 758545800942705692156197)
                    ·
                      rfl

theorem cell22_2215894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_2215894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215894 prefixEnd_2215894 := by exact prefixLift 2215894
  have htrace : WordTrace (prefixWord ++ tailWord_2215894) baseStart_2215894 baseEnd_2215894 := by
    simpa [prefixWord, tailWord_2215894, baseEnd_2215894] using wordTrace_append hprefix tailTrace_2215894
  have hstable : (prefixWord ++ tailWord_2215894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215894).length < 2 ^ (prefixWord ++ tailWord_2215894).sum := by decide
  have hdescent : baseEnd_2215894 < baseStart_2215894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215907 : List Nat := [1, 1, 1, 6, 1, 3, 2, 3, 1, 3]
def baseStart_2215907 : Nat := 118140960795 + 2215907 * 2 ^ 59
def prefixEnd_2215907 : Nat := 4983230072969 + 3 ^ 40 * 2215907 * 2
def baseEnd_2215907 : Nat := 758550251108377991581157

theorem tailTrace_2215907 : CollatzResearch.WordTrace tailWord_2215907 prefixEnd_2215907 758550251108377991581157 := by
  unfold tailWord_2215907
  simp only [CollatzResearch.WordTrace]
  refine ⟨80820767983154860631021975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53880511988769907087347983 80820767983154860631021975)
  ·
    refine ⟨121231151974732290946532963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80820767983154860631021975 121231151974732290946532963)
    ·
      refine ⟨181846727962098436419799445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121231151974732290946532963 181846727962098436419799445)
      ·
        refine ⟨8524065373223364207178099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 181846727962098436419799445 8524065373223364207178099)
        ·
          refine ⟨12786098059835046310767149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8524065373223364207178099 12786098059835046310767149)
          ·
            refine ⟨4794786772438142366537681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12786098059835046310767149 4794786772438142366537681)
            ·
              refine ⟨3596090079328606774903261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4794786772438142366537681 3596090079328606774903261)
              ·
                refine ⟨1348533779748227540588723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3596090079328606774903261 1348533779748227540588723)
                ·
                  refine ⟨2022800669622341310883085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1348533779748227540588723 2022800669622341310883085)
                  ·
                    refine ⟨758550251108377991581157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2022800669622341310883085 758550251108377991581157)
                    ·
                      rfl

theorem cell22_2215907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 1, 3].length) (baseStart_2215907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215907 prefixEnd_2215907 := by exact prefixLift 2215907
  have htrace : WordTrace (prefixWord ++ tailWord_2215907) baseStart_2215907 baseEnd_2215907 := by
    simpa [prefixWord, tailWord_2215907, baseEnd_2215907] using wordTrace_append hprefix tailTrace_2215907
  have hstable : (prefixWord ++ tailWord_2215907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215907).length < 2 ^ (prefixWord ++ tailWord_2215907).sum := by decide
  have hdescent : baseEnd_2215907 < baseStart_2215907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215918 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 2, 5]
def baseStart_2215918 : Nat := 118140960795 + 2215918 * 2 ^ 59
def prefixEnd_2215918 : Nat := 4983230072969 + 3 ^ 40 * 2215918 * 2
def baseEnd_2215918 : Nat := 758554016633177629556123

theorem tailTrace_2215918 : CollatzResearch.WordTrace tailWord_2215918 prefixEnd_2215918 758554016633177629556123 := by
  unfold tailWord_2215918
  simp only [CollatzResearch.WordTrace]
  refine ⟨10102646148264376188709051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53880779457410006339781605 10102646148264376188709051)
  ·
    refine ⟨15153969222396564283063577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10102646148264376188709051 15153969222396564283063577)
    ·
      refine ⟨11365476916797423212297683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15153969222396564283063577 11365476916797423212297683)
      ·
        refine ⟨17048215375196134818446525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11365476916797423212297683 17048215375196134818446525)
        ·
          refine ⟨6393080765698550556917447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17048215375196134818446525 6393080765698550556917447)
          ·
            refine ⟨9589621148547825835376171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6393080765698550556917447 9589621148547825835376171)
            ·
              refine ⟨14384431722821738753064257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9589621148547825835376171 14384431722821738753064257)
              ·
                refine ⟨10788323792116304064798193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14384431722821738753064257 10788323792116304064798193)
                ·
                  refine ⟨8091242844087228048598645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10788323792116304064798193 8091242844087228048598645)
                  ·
                    refine ⟨758554016633177629556123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8091242844087228048598645 758554016633177629556123)
                    ·
                      rfl

theorem cell22_2215918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_2215918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215918 prefixEnd_2215918 := by exact prefixLift 2215918
  have htrace : WordTrace (prefixWord ++ tailWord_2215918) baseStart_2215918 baseEnd_2215918 := by
    simpa [prefixWord, tailWord_2215918, baseEnd_2215918] using wordTrace_append hprefix tailTrace_2215918
  have hstable : (prefixWord ++ tailWord_2215918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215918).length < 2 ^ (prefixWord ++ tailWord_2215918).sum := by decide
  have hdescent : baseEnd_2215918 < baseStart_2215918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215931 : List Nat := [1, 1, 1, 1, 1, 3, 5, 3, 6]
def baseStart_2215931 : Nat := 118140960795 + 2215931 * 2 ^ 59
def prefixEnd_2215931 : Nat := 4983230072969 + 3 ^ 40 * 2215931 * 2
def baseEnd_2215931 : Nat := 252852822266283309660361

theorem tailTrace_2215931 : CollatzResearch.WordTrace tailWord_2215931 prefixEnd_2215931 252852822266283309660361 := by
  unfold tailWord_2215931
  simp only [CollatzResearch.WordTrace]
  refine ⟨80821643335067912729895647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53881095556711941819930431 80821643335067912729895647)
  ·
    refine ⟨121232465002601869094843471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80821643335067912729895647 121232465002601869094843471)
    ·
      refine ⟨181848697503902803642265207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121232465002601869094843471 181848697503902803642265207)
      ·
        refine ⟨272773046255854205463397811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181848697503902803642265207 272773046255854205463397811)
        ·
          refine ⟨409159569383781308195096717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272773046255854205463397811 409159569383781308195096717)
          ·
            refine ⟨153434838518917990573161269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 409159569383781308195096717 153434838518917990573161269)
            ·
              refine ⟨14384516111148561616233869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 153434838518917990573161269 14384516111148561616233869)
              ·
                refine ⟨5394193541680710606087701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14384516111148561616233869 5394193541680710606087701)
                ·
                  refine ⟨252852822266283309660361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5394193541680710606087701 252852822266283309660361)
                  ·
                    rfl

theorem cell22_2215931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 6].length) (baseStart_2215931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215931 prefixEnd_2215931 := by exact prefixLift 2215931
  have htrace : WordTrace (prefixWord ++ tailWord_2215931) baseStart_2215931 baseEnd_2215931 := by
    simpa [prefixWord, tailWord_2215931, baseEnd_2215931] using wordTrace_append hprefix tailTrace_2215931
  have hstable : (prefixWord ++ tailWord_2215931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215931).length < 2 ^ (prefixWord ++ tailWord_2215931).sum := by decide
  have hdescent : baseEnd_2215931 < baseStart_2215931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215950 : List Nat := [4, 1, 1, 2, 2, 1, 4, 2, 1, 4]
def baseStart_2215950 : Nat := 118140960795 + 2215950 * 2 ^ 59
def prefixEnd_2215950 : Nat := 4983230072969 + 3 ^ 40 * 2215950 * 2
def baseEnd_2215950 : Nat := 758564970887140212756025

theorem tailTrace_2215950 : CollatzResearch.WordTrace tailWord_2215950 prefixEnd_2215950 758564970887140212756025 := by
  unfold tailWord_2215950
  simp only [CollatzResearch.WordTrace]
  refine ⟨10102792040249884871854663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53881557547999385983224869 10102792040249884871854663)
  ·
    refine ⟨15154188060374827307781995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10102792040249884871854663 15154188060374827307781995)
    ·
      refine ⟨22731282090562240961672993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15154188060374827307781995 22731282090562240961672993)
      ·
        refine ⟨17048461567921680721254745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22731282090562240961672993 17048461567921680721254745)
        ·
          refine ⟨12786346175941260540941059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17048461567921680721254745 12786346175941260540941059)
          ·
            refine ⟨19179519263911890811411589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12786346175941260540941059 19179519263911890811411589)
            ·
              refine ⟨3596159861983479527139673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19179519263911890811411589 3596159861983479527139673)
              ·
                refine ⟨2697119896487609645354755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3596159861983479527139673 2697119896487609645354755)
                ·
                  refine ⟨4045679844731414468032133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2697119896487609645354755 4045679844731414468032133)
                  ·
                    refine ⟨758564970887140212756025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4045679844731414468032133 758564970887140212756025)
                    ·
                      rfl

theorem cell22_2215950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_2215950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2215950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2215950 prefixEnd_2215950 := by exact prefixLift 2215950
  have htrace : WordTrace (prefixWord ++ tailWord_2215950) baseStart_2215950 baseEnd_2215950 := by
    simpa [prefixWord, tailWord_2215950, baseEnd_2215950] using wordTrace_append hprefix tailTrace_2215950
  have hstable : (prefixWord ++ tailWord_2215950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215950).length < 2 ^ (prefixWord ++ tailWord_2215950).sum := by decide
  have hdescent : baseEnd_2215950 < baseStart_2215950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216085 : List Nat := [1, 3, 2, 1, 1, 1, 5, 3, 1, 4]
def baseStart_2216085 : Nat := 118140960795 + 2216085 * 2 ^ 59
def prefixEnd_2216085 : Nat := 4983230072969 + 3 ^ 40 * 2216085 * 2
def baseEnd_2216085 : Nat := 758611184146044860630611

theorem tailTrace_2216085 : CollatzResearch.WordTrace tailWord_2216085 prefixEnd_2216085 758611184146044860630611 := by
  unfold tailWord_2216085
  simp only [CollatzResearch.WordTrace]
  refine ⟨80827260176509997031001709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53884840117673331354001139 80827260176509997031001709)
  ·
    refine ⟨30310222566191248886625641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80827260176509997031001709 30310222566191248886625641)
    ·
      refine ⟨22732666924643436664969231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30310222566191248886625641 22732666924643436664969231)
      ·
        refine ⟨34099000386965154997453847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22732666924643436664969231 34099000386965154997453847)
        ·
          refine ⟨51148500580447732496180771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34099000386965154997453847 51148500580447732496180771)
          ·
            refine ⟨76722750870671598744271157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51148500580447732496180771 76722750870671598744271157)
            ·
              refine ⟨7192757894125462382275421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76722750870671598744271157 7192757894125462382275421)
              ·
                refine ⟨2697284210297048393353283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7192757894125462382275421 2697284210297048393353283)
                ·
                  refine ⟨4045926315445572590029925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2697284210297048393353283 4045926315445572590029925)
                  ·
                    refine ⟨758611184146044860630611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4045926315445572590029925 758611184146044860630611)
                    ·
                      rfl

theorem cell22_2216085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_2216085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216085 prefixEnd_2216085 := by exact prefixLift 2216085
  have htrace : WordTrace (prefixWord ++ tailWord_2216085) baseStart_2216085 baseEnd_2216085 := by
    simpa [prefixWord, tailWord_2216085, baseEnd_2216085] using wordTrace_append hprefix tailTrace_2216085
  have hstable : (prefixWord ++ tailWord_2216085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216085).length < 2 ^ (prefixWord ++ tailWord_2216085).sum := by decide
  have hdescent : baseEnd_2216085 < baseStart_2216085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216132 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 4, 3]
def baseStart_2216132 : Nat := 118140960795 + 2216132 * 2 ^ 59
def prefixEnd_2216132 : Nat := 4983230072969 + 3 ^ 40 * 2216132 * 2
def baseEnd_2216132 : Nat := 758627273206552404705467

theorem tailTrace_2216132 : CollatzResearch.WordTrace tailWord_2216132 prefixEnd_2216132 758627273206552404705467 := by
  unfold tailWord_2216132
  simp only [CollatzResearch.WordTrace]
  refine ⟨40414487203669862028981325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53885982938226482705308433 40414487203669862028981325)
  ·
    refine ⟨15155432701376198260867997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40414487203669862028981325 15155432701376198260867997)
    ·
      refine ⟨5683287263016074347825499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15155432701376198260867997 5683287263016074347825499)
      ·
        refine ⟨8524930894524111521738249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5683287263016074347825499 8524930894524111521738249)
        ·
          refine ⟨6393698170893083641303687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8524930894524111521738249 6393698170893083641303687)
          ·
            refine ⟨9590547256339625461955531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6393698170893083641303687 9590547256339625461955531)
            ·
              refine ⟨14385820884509438192933297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9590547256339625461955531 14385820884509438192933297)
              ·
                refine ⟨10789365663382078644699973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14385820884509438192933297 10789365663382078644699973)
                ·
                  refine ⟨2023006061884139745881245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10789365663382078644699973 2023006061884139745881245)
                  ·
                    refine ⟨758627273206552404705467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2023006061884139745881245 758627273206552404705467)
                    ·
                      rfl

theorem cell22_2216132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_2216132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216132 prefixEnd_2216132 := by exact prefixLift 2216132
  have htrace : WordTrace (prefixWord ++ tailWord_2216132) baseStart_2216132 baseEnd_2216132 := by
    simpa [prefixWord, tailWord_2216132, baseEnd_2216132] using wordTrace_append hprefix tailTrace_2216132
  have hstable : (prefixWord ++ tailWord_2216132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216132).length < 2 ^ (prefixWord ++ tailWord_2216132).sum := by decide
  have hdescent : baseEnd_2216132 < baseStart_2216132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216254 : List Nat := [4, 2, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_2216254 : Nat := 118140960795 + 2216254 * 2 ^ 59
def prefixEnd_2216254 : Nat := 4983230072969 + 3 ^ 40 * 2216254 * 2
def baseEnd_2216254 : Nat := 758669036299784753155093

theorem tailTrace_2216254 : CollatzResearch.WordTrace tailWord_2216254 prefixEnd_2216254 758669036299784753155093 := by
  unfold tailWord_2216254
  simp only [CollatzResearch.WordTrace]
  refine ⟨10104178014112217361737977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53888949408598492595935877 10104178014112217361737977)
  ·
    refine ⟨7578133510584163021303483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10104178014112217361737977 7578133510584163021303483)
    ·
      refine ⟨11367200265876244531955225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7578133510584163021303483 11367200265876244531955225)
      ·
        refine ⟨8525400199407183398966419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11367200265876244531955225 8525400199407183398966419)
        ·
          refine ⟨12788100299110775098449629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8525400199407183398966419 12788100299110775098449629)
          ·
            refine ⟨4795537612166540661918611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12788100299110775098449629 4795537612166540661918611)
            ·
              refine ⟨7193306418249810992877917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4795537612166540661918611 7193306418249810992877917)
              ·
                refine ⟨2697489906843679122329219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7193306418249810992877917 2697489906843679122329219)
                ·
                  refine ⟨4046234860265518683493829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2697489906843679122329219 4046234860265518683493829)
                  ·
                    refine ⟨758669036299784753155093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4046234860265518683493829 758669036299784753155093)
                    ·
                      rfl

theorem cell22_2216254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_2216254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216254 prefixEnd_2216254 := by exact prefixLift 2216254
  have htrace : WordTrace (prefixWord ++ tailWord_2216254) baseStart_2216254 baseEnd_2216254 := by
    simpa [prefixWord, tailWord_2216254, baseEnd_2216254] using wordTrace_append hprefix tailTrace_2216254
  have hstable : (prefixWord ++ tailWord_2216254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216254).length < 2 ^ (prefixWord ++ tailWord_2216254).sum := by decide
  have hdescent : baseEnd_2216254 < baseStart_2216254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216265 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 4, 4]
def baseStart_2216265 : Nat := 118140960795 + 2216265 * 2 ^ 59
def prefixEnd_2216265 : Nat := 4983230072969 + 3 ^ 40 * 2216265 * 2
def baseEnd_2216265 : Nat := 758672801824584391130059

theorem tailTrace_2216265 : CollatzResearch.WordTrace tailWord_2216265 prefixEnd_2216265 758672801824584391130059 := by
  unfold tailWord_2216265
  simp only [CollatzResearch.WordTrace]
  refine ⟨80833825315857887772554249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53889216877238591848369499 80833825315857887772554249)
  ·
    refine ⟨60625368986893415829415687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80833825315857887772554249 60625368986893415829415687)
    ·
      refine ⟨90938053480340123744123531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60625368986893415829415687 90938053480340123744123531)
      ·
        refine ⟨136407080220510185616185297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90938053480340123744123531 136407080220510185616185297)
        ·
          refine ⟨102305310165382639212138973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136407080220510185616185297 102305310165382639212138973)
          ·
            refine ⟨38364491312018489704552115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102305310165382639212138973 38364491312018489704552115)
            ·
              refine ⟨57546736968027734556828173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38364491312018489704552115 57546736968027734556828173)
              ·
                refine ⟨21580026363010400458810565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57546736968027734556828173 21580026363010400458810565)
                ·
                  refine ⟨4046254943064450086026981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21580026363010400458810565 4046254943064450086026981)
                  ·
                    refine ⟨758672801824584391130059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4046254943064450086026981 758672801824584391130059)
                    ·
                      rfl

theorem cell22_2216265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 4].length) (baseStart_2216265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216265 prefixEnd_2216265 := by exact prefixLift 2216265
  have htrace : WordTrace (prefixWord ++ tailWord_2216265) baseStart_2216265 baseEnd_2216265 := by
    simpa [prefixWord, tailWord_2216265, baseEnd_2216265] using wordTrace_append hprefix tailTrace_2216265
  have hstable : (prefixWord ++ tailWord_2216265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216265).length < 2 ^ (prefixWord ++ tailWord_2216265).sum := by decide
  have hdescent : baseEnd_2216265 < baseStart_2216265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216267 : List Nat := [1, 1, 1, 1, 3, 1, 1, 8, 2, 3]
def baseStart_2216267 : Nat := 118140960795 + 2216267 * 2 ^ 59
def prefixEnd_2216267 : Nat := 4983230072969 + 3 ^ 40 * 2216267 * 2
def baseEnd_2216267 : Nat := 758673486465457052580053

theorem tailTrace_2216267 : CollatzResearch.WordTrace tailWord_2216267 prefixEnd_2216267 758673486465457052580053 := by
  unfold tailWord_2216267
  simp only [CollatzResearch.WordTrace]
  refine ⟨80833898261850642114127055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53889265507900428076084703 80833898261850642114127055)
  ·
    refine ⟨121250847392775963171190583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80833898261850642114127055 121250847392775963171190583)
    ·
      refine ⟨181876271089163944756785875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121250847392775963171190583 181876271089163944756785875)
      ·
        refine ⟨272814406633745917135178813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181876271089163944756785875 272814406633745917135178813)
        ·
          refine ⟨102305402487654718925692055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 272814406633745917135178813 102305402487654718925692055)
          ·
            refine ⟨153458103731482078388538083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102305402487654718925692055 153458103731482078388538083)
            ·
              refine ⟨230187155597223117582807125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153458103731482078388538083 230187155597223117582807125)
              ·
                refine ⟨2697505729654958409173521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 230187155597223117582807125 2697505729654958409173521)
                ·
                  refine ⟨2023129297241218806880141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2697505729654958409173521 2023129297241218806880141)
                  ·
                    refine ⟨758673486465457052580053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2023129297241218806880141 758673486465457052580053)
                    ·
                      rfl

theorem cell22_2216267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 3].length) (baseStart_2216267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216267 prefixEnd_2216267 := by exact prefixLift 2216267
  have htrace : WordTrace (prefixWord ++ tailWord_2216267) baseStart_2216267 baseEnd_2216267 := by
    simpa [prefixWord, tailWord_2216267, baseEnd_2216267] using wordTrace_append hprefix tailTrace_2216267
  have hstable : (prefixWord ++ tailWord_2216267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216267).length < 2 ^ (prefixWord ++ tailWord_2216267).sum := by decide
  have hdescent : baseEnd_2216267 < baseStart_2216267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216329 : List Nat := [1, 2, 1, 1, 6, 1, 3, 1, 3, 3]
def baseStart_2216329 : Nat := 118140960795 + 2216329 * 2 ^ 59
def prefixEnd_2216329 : Nat := 4983230072969 + 3 ^ 40 * 2216329 * 2
def baseEnd_2216329 : Nat := 758694710332509557529863

theorem tailTrace_2216329 : CollatzResearch.WordTrace tailWord_2216329 prefixEnd_2216329 758694710332509557529863 := by
  unfold tailWord_2216329
  simp only [CollatzResearch.WordTrace]
  refine ⟨80836159587626026702884041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53890773058417351135256027 80836159587626026702884041)
  ·
    refine ⟨60627119690719520027163031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80836159587626026702884041 60627119690719520027163031)
    ·
      refine ⟨90940679536079280040744547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60627119690719520027163031 90940679536079280040744547)
      ·
        refine ⟨136411019304118920061116821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90940679536079280040744547 136411019304118920061116821)
        ·
          refine ⟨6394266529880574377864851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 136411019304118920061116821 6394266529880574377864851)
          ·
            refine ⟨9591399794820861566797277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6394266529880574377864851 9591399794820861566797277)
            ·
              refine ⟨3596774923057823087548979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9591399794820861566797277 3596774923057823087548979)
              ·
                refine ⟨5395162384586734631323469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3596774923057823087548979 5395162384586734631323469)
                ·
                  refine ⟨2023185894220025486746301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5395162384586734631323469 2023185894220025486746301)
                  ·
                    refine ⟨758694710332509557529863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2023185894220025486746301 758694710332509557529863)
                    ·
                      rfl

theorem cell22_2216329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 3].length) (baseStart_2216329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216329 prefixEnd_2216329 := by exact prefixLift 2216329
  have htrace : WordTrace (prefixWord ++ tailWord_2216329) baseStart_2216329 baseEnd_2216329 := by
    simpa [prefixWord, tailWord_2216329, baseEnd_2216329] using wordTrace_append hprefix tailTrace_2216329
  have hstable : (prefixWord ++ tailWord_2216329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216329).length < 2 ^ (prefixWord ++ tailWord_2216329).sum := by decide
  have hdescent : baseEnd_2216329 < baseStart_2216329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216380 : List Nat := [2, 2, 2, 4, 1, 3, 2, 2, 1, 3]
def baseStart_2216380 : Nat := 118140960795 + 2216380 * 2 ^ 59
def prefixEnd_2216380 : Nat := 4983230072969 + 3 ^ 40 * 2216380 * 2
def baseEnd_2216380 : Nat := 758712168674762424504707

theorem tailTrace_2216380 : CollatzResearch.WordTrace tailWord_2216380 prefixEnd_2216380 758712168674762424504707 := by
  unfold tailWord_2216380
  simp only [CollatzResearch.WordTrace]
  refine ⟨40419009855220631206495297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53892013140294174941993729 40419009855220631206495297)
  ·
    refine ⟨30314257391415473404871473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40419009855220631206495297 30314257391415473404871473)
    ·
      refine ⟨22735693043561605053653605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30314257391415473404871473 22735693043561605053653605)
      ·
        refine ⟨4262942445667800947560051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22735693043561605053653605 4262942445667800947560051)
        ·
          refine ⟨6394413668501701421340077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4262942445667800947560051 6394413668501701421340077)
          ·
            refine ⟨2397905125688138033002529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6394413668501701421340077 2397905125688138033002529)
            ·
              refine ⟨1798428844266103524751897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2397905125688138033002529 1798428844266103524751897)
              ·
                refine ⟨1348821633199577643563923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1798428844266103524751897 1348821633199577643563923)
                ·
                  refine ⟨2023232449799366465345885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1348821633199577643563923 2023232449799366465345885)
                  ·
                    refine ⟨758712168674762424504707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2023232449799366465345885 758712168674762424504707)
                    ·
                      rfl

theorem cell22_2216380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_2216380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216380 prefixEnd_2216380 := by exact prefixLift 2216380
  have htrace : WordTrace (prefixWord ++ tailWord_2216380) baseStart_2216380 baseEnd_2216380 := by
    simpa [prefixWord, tailWord_2216380, baseEnd_2216380] using wordTrace_append hprefix tailTrace_2216380
  have hstable : (prefixWord ++ tailWord_2216380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216380).length < 2 ^ (prefixWord ++ tailWord_2216380).sum := by decide
  have hdescent : baseEnd_2216380 < baseStart_2216380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216404 : List Nat := [2, 4, 1, 2, 2, 2, 1, 2, 6]
def baseStart_2216404 : Nat := 118140960795 + 2216404 * 2 ^ 59
def prefixEnd_2216404 : Nat := 4983230072969 + 3 ^ 40 * 2216404 * 2
def baseEnd_2216404 : Nat := 252906794788411453968211

theorem tailTrace_2216404 : CollatzResearch.WordTrace tailWord_2216404 prefixEnd_2216404 252906794788411453968211 := by
  unfold tailWord_2216404
  simp only [CollatzResearch.WordTrace]
  refine ⟨40419447531177157255932133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53892596708236209674576177 40419447531177157255932133)
  ·
    refine ⟨7578646412095716985487275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40419447531177157255932133 7578646412095716985487275)
    ·
      refine ⟨11367969618143575478230913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7578646412095716985487275 11367969618143575478230913)
      ·
        refine ⟨8525977213607681608673185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11367969618143575478230913 8525977213607681608673185)
        ·
          refine ⟨6394482910205761206504889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8525977213607681608673185 6394482910205761206504889)
          ·
            refine ⟨4795862182654320904878667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6394482910205761206504889 4795862182654320904878667)
            ·
              refine ⟨7193793273981481357318001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4795862182654320904878667 7193793273981481357318001)
              ·
                refine ⟨5395344955486111017988501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7193793273981481357318001 5395344955486111017988501)
                ·
                  refine ⟨252906794788411453968211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5395344955486111017988501 252906794788411453968211)
                  ·
                    rfl

theorem cell22_2216404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_2216404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216404 prefixEnd_2216404 := by exact prefixLift 2216404
  have htrace : WordTrace (prefixWord ++ tailWord_2216404) baseStart_2216404 baseEnd_2216404 := by
    simpa [prefixWord, tailWord_2216404, baseEnd_2216404] using wordTrace_append hprefix tailTrace_2216404
  have hstable : (prefixWord ++ tailWord_2216404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216404).length < 2 ^ (prefixWord ++ tailWord_2216404).sum := by decide
  have hdescent : baseEnd_2216404 < baseStart_2216404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216406 : List Nat := [5, 2, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_2216406 : Nat := 118140960795 + 2216406 * 2 ^ 59
def prefixEnd_2216406 : Nat := 4983230072969 + 3 ^ 40 * 2216406 * 2
def baseEnd_2216406 : Nat := 758721069006107023354627

theorem tailTrace_2216406 : CollatzResearch.WordTrace tailWord_2216406 prefixEnd_2216406 758721069006107023354627 := by
  unfold tailWord_2216406
  simp only [CollatzResearch.WordTrace]
  refine ⟨5052435500521691803339817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53892645338898045902291381 5052435500521691803339817)
  ·
    refine ⟨3789326625391268852504863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5052435500521691803339817 3789326625391268852504863)
    ·
      refine ⟨5683989938086903278757295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3789326625391268852504863 5683989938086903278757295)
      ·
        refine ⟨8525984907130354918135943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5683989938086903278757295 8525984907130354918135943)
        ·
          refine ⟨12788977360695532377203915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8525984907130354918135943 12788977360695532377203915)
          ·
            refine ⟨19183466041043298565805873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12788977360695532377203915 19183466041043298565805873)
            ·
              refine ⟨14387599530782473924354405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19183466041043298565805873 14387599530782473924354405)
              ·
                refine ⟨2697674912021713860816451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14387599530782473924354405 2697674912021713860816451)
                ·
                  refine ⟨4046512368032570791224677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2697674912021713860816451 4046512368032570791224677)
                  ·
                    refine ⟨758721069006107023354627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4046512368032570791224677 758721069006107023354627)
                    ·
                      rfl

theorem cell22_2216406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_2216406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216406 prefixEnd_2216406 := by exact prefixLift 2216406
  have htrace : WordTrace (prefixWord ++ tailWord_2216406) baseStart_2216406 baseEnd_2216406 := by
    simpa [prefixWord, tailWord_2216406, baseEnd_2216406] using wordTrace_append hprefix tailTrace_2216406
  have hstable : (prefixWord ++ tailWord_2216406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216406).length < 2 ^ (prefixWord ++ tailWord_2216406).sum := by decide
  have hdescent : baseEnd_2216406 < baseStart_2216406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216417 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 1, 6]
def baseStart_2216417 : Nat := 118140960795 + 2216417 * 2 ^ 59
def prefixEnd_2216417 : Nat := 4983230072969 + 3 ^ 40 * 2216417 * 2
def baseEnd_2216417 : Nat := 758724834530906661329593

theorem tailTrace_2216417 : CollatzResearch.WordTrace tailWord_2216417 prefixEnd_2216417 758724834530906661329593 := by
  unfold tailWord_2216417
  simp only [CollatzResearch.WordTrace]
  refine ⟨80839369211307217732087505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53892912807538145154725003 80839369211307217732087505)
  ·
    refine ⟨60629526908480413299065629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80839369211307217732087505 60629526908480413299065629)
    ·
      refine ⟨22736072590680154987149611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60629526908480413299065629 22736072590680154987149611)
      ·
        refine ⟨34104108886020232480724417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22736072590680154987149611 34104108886020232480724417)
        ·
          refine ⟨25578081664515174360543313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34104108886020232480724417 25578081664515174360543313)
          ·
            refine ⟨19183561248386380770407485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25578081664515174360543313 19183561248386380770407485)
            ·
              refine ⟨7193835468144892788902807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19183561248386380770407485 7193835468144892788902807)
              ·
                refine ⟨10790753202217339183354211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7193835468144892788902807 10790753202217339183354211)
                ·
                  refine ⟨16186129803326008775031317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10790753202217339183354211 16186129803326008775031317)
                  ·
                    refine ⟨758724834530906661329593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16186129803326008775031317 758724834530906661329593)
                    ·
                      rfl

theorem cell22_2216417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_2216417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216417 prefixEnd_2216417 := by exact prefixLift 2216417
  have htrace : WordTrace (prefixWord ++ tailWord_2216417) baseStart_2216417 baseEnd_2216417 := by
    simpa [prefixWord, tailWord_2216417, baseEnd_2216417] using wordTrace_append hprefix tailTrace_2216417
  have hstable : (prefixWord ++ tailWord_2216417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216417).length < 2 ^ (prefixWord ++ tailWord_2216417).sum := by decide
  have hdescent : baseEnd_2216417 < baseStart_2216417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216492 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 4, 5]
def baseStart_2216492 : Nat := 118140960795 + 2216492 * 2 ^ 59
def prefixEnd_2216492 : Nat := 4983230072969 + 3 ^ 40 * 2216492 * 2
def baseEnd_2216492 : Nat := 758750508563631465704363

theorem tailTrace_2216492 : CollatzResearch.WordTrace tailWord_2216492 prefixEnd_2216492 758750508563631465704363 := by
  unfold tailWord_2216492
  simp only [CollatzResearch.WordTrace]
  refine ⟨40421052343017752770533865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53894736457357003694045153 40421052343017752770533865)
  ·
    refine ⟨30315789257263314577900399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40421052343017752770533865 30315789257263314577900399)
    ·
      refine ⟨45473683885894971866850599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30315789257263314577900399 45473683885894971866850599)
      ·
        refine ⟨68210525828842457800275899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45473683885894971866850599 68210525828842457800275899)
        ·
          refine ⟨102315788743263686700413849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68210525828842457800275899 102315788743263686700413849)
          ·
            refine ⟨76736841557447765025310387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102315788743263686700413849 76736841557447765025310387)
            ·
              refine ⟨115105262336171647537965581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76736841557447765025310387 115105262336171647537965581)
              ·
                refine ⟨43164473376064367826737093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115105262336171647537965581 43164473376064367826737093)
                ·
                  refine ⟨8093338758012068967513205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43164473376064367826737093 8093338758012068967513205)
                  ·
                    refine ⟨758750508563631465704363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8093338758012068967513205 758750508563631465704363)
                    ·
                      rfl

theorem cell22_2216492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_2216492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216492 prefixEnd_2216492 := by exact prefixLift 2216492
  have htrace : WordTrace (prefixWord ++ tailWord_2216492) baseStart_2216492 baseEnd_2216492 := by
    simpa [prefixWord, tailWord_2216492, baseEnd_2216492] using wordTrace_append hprefix tailTrace_2216492
  have hstable : (prefixWord ++ tailWord_2216492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216492).length < 2 ^ (prefixWord ++ tailWord_2216492).sum := by decide
  have hdescent : baseEnd_2216492 < baseStart_2216492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216524 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 3, 4]
def baseStart_2216524 : Nat := 118140960795 + 2216524 * 2 ^ 59
def prefixEnd_2216524 : Nat := 4983230072969 + 3 ^ 40 * 2216524 * 2
def baseEnd_2216524 : Nat := 758761462817594048904265

theorem tailTrace_2216524 : CollatzResearch.WordTrace tailWord_2216524 prefixEnd_2216524 758761462817594048904265 := by
  unfold tailWord_2216524
  simp only [CollatzResearch.WordTrace]
  refine ⟨40421635910959787503116313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53895514547946383337488417 40421635910959787503116313)
  ·
    refine ⟨30316226933219840627337235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40421635910959787503116313 30316226933219840627337235)
    ·
      refine ⟨45474340399829760941005853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30316226933219840627337235 45474340399829760941005853)
      ·
        refine ⟨17052877649936160352877195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45474340399829760941005853 17052877649936160352877195)
        ·
          refine ⟨25579316474904240529315793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17052877649936160352877195 25579316474904240529315793)
          ·
            refine ⟨19184487356178180396986845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25579316474904240529315793 19184487356178180396986845)
            ·
              refine ⟨7194182758566817648870067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19184487356178180396986845 7194182758566817648870067)
              ·
                refine ⟨10791274137850226473305101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7194182758566817648870067 10791274137850226473305101)
                ·
                  refine ⟨4046727801693834927489413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10791274137850226473305101 4046727801693834927489413)
                  ·
                    refine ⟨758761462817594048904265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4046727801693834927489413 758761462817594048904265)
                    ·
                      rfl

theorem cell22_2216524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_2216524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216524 prefixEnd_2216524 := by exact prefixLift 2216524
  have htrace : WordTrace (prefixWord ++ tailWord_2216524) baseStart_2216524 baseEnd_2216524 := by
    simpa [prefixWord, tailWord_2216524, baseEnd_2216524] using wordTrace_append hprefix tailTrace_2216524
  have hstable : (prefixWord ++ tailWord_2216524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216524).length < 2 ^ (prefixWord ++ tailWord_2216524).sum := by decide
  have hdescent : baseEnd_2216524 < baseStart_2216524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216554 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 3, 5]
def baseStart_2216554 : Nat := 118140960795 + 2216554 * 2 ^ 59
def prefixEnd_2216554 : Nat := 4983230072969 + 3 ^ 40 * 2216554 * 2
def baseEnd_2216554 : Nat := 758771732430683970654173

theorem tailTrace_2216554 : CollatzResearch.WordTrace tailWord_2216554 prefixEnd_2216554 758771732430683970654173 := by
  unfold tailWord_2216554
  simp only [CollatzResearch.WordTrace]
  refine ⟨20211091502952722532456179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53896244007873926753216477 20211091502952722532456179)
  ·
    refine ⟨30316637254429083798684269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20211091502952722532456179 30316637254429083798684269)
    ·
      refine ⟨11368738970410906424506601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30316637254429083798684269 11368738970410906424506601)
      ·
        refine ⟨8526554227808179818379951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11368738970410906424506601 8526554227808179818379951)
        ·
          refine ⟨12789831341712269727569927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8526554227808179818379951 12789831341712269727569927)
          ·
            refine ⟨19184747012568404591354891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12789831341712269727569927 19184747012568404591354891)
            ·
              refine ⟨28777120518852606887032337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19184747012568404591354891 28777120518852606887032337)
              ·
                refine ⟨21582840389139455165274253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28777120518852606887032337 21582840389139455165274253)
                ·
                  refine ⟨8093565145927295686977845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21582840389139455165274253 8093565145927295686977845)
                  ·
                    refine ⟨758771732430683970654173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8093565145927295686977845 758771732430683970654173)
                    ·
                      rfl

theorem cell22_2216554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_2216554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216554 prefixEnd_2216554 := by exact prefixLift 2216554
  have htrace : WordTrace (prefixWord ++ tailWord_2216554) baseStart_2216554 baseEnd_2216554 := by
    simpa [prefixWord, tailWord_2216554, baseEnd_2216554] using wordTrace_append hprefix tailTrace_2216554
  have hstable : (prefixWord ++ tailWord_2216554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216554).length < 2 ^ (prefixWord ++ tailWord_2216554).sum := by decide
  have hdescent : baseEnd_2216554 < baseStart_2216554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216586 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 1, 6]
def baseStart_2216586 : Nat := 118140960795 + 2216586 * 2 ^ 59
def prefixEnd_2216586 : Nat := 4983230072969 + 3 ^ 40 * 2216586 * 2
def baseEnd_2216586 : Nat := 758782686684646553854075

theorem tailTrace_2216586 : CollatzResearch.WordTrace tailWord_2216586 prefixEnd_2216586 758782686684646553854075 := by
  unfold tailWord_2216586
  simp only [CollatzResearch.WordTrace]
  refine ⟨20211383286923739898747403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53897022098463306396659741 20211383286923739898747403)
  ·
    refine ⟨30317074930385609848121105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20211383286923739898747403 30317074930385609848121105)
    ·
      refine ⟨22737806197789207386090829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30317074930385609848121105 22737806197789207386090829)
      ·
        refine ⟨8526677324170952769784061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22737806197789207386090829 8526677324170952769784061)
        ·
          refine ⟨3197503996564107288669023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8526677324170952769784061 3197503996564107288669023)
          ·
            refine ⟨4796255994846160933003535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3197503996564107288669023 4796255994846160933003535)
            ·
              refine ⟨7194383992269241399505303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4796255994846160933003535 7194383992269241399505303)
              ·
                refine ⟨10791575988403862099257955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7194383992269241399505303 10791575988403862099257955)
                ·
                  refine ⟨16187363982605793148886933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10791575988403862099257955 16187363982605793148886933)
                  ·
                    refine ⟨758782686684646553854075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16187363982605793148886933 758782686684646553854075)
                    ·
                      rfl

theorem cell22_2216586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_2216586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216586 prefixEnd_2216586 := by exact prefixLift 2216586
  have htrace : WordTrace (prefixWord ++ tailWord_2216586) baseStart_2216586 baseEnd_2216586 := by
    simpa [prefixWord, tailWord_2216586, baseEnd_2216586] using wordTrace_append hprefix tailTrace_2216586
  have hstable : (prefixWord ++ tailWord_2216586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216586).length < 2 ^ (prefixWord ++ tailWord_2216586).sum := by decide
  have hdescent : baseEnd_2216586 < baseStart_2216586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216622 : List Nat := [4, 1, 4, 1, 1, 2, 3, 1, 2, 3]
def baseStart_2216622 : Nat := 118140960795 + 2216622 * 2 ^ 59
def prefixEnd_2216622 : Nat := 4983230072969 + 3 ^ 40 * 2216622 * 2
def baseEnd_2216622 : Nat := 758795010220354459953965

theorem tailTrace_2216622 : CollatzResearch.WordTrace tailWord_2216622 prefixEnd_2216622 758795010220354459953965 := by
  unfold tailWord_2216622
  simp only [CollatzResearch.WordTrace]
  refine ⟨10105855771945567217912515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53897897450376358495533413 10105855771945567217912515)
  ·
    refine ⟨15158783657918350826868773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10105855771945567217912515 15158783657918350826868773)
    ·
      refine ⟨2842271935859690780037895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15158783657918350826868773 2842271935859690780037895)
      ·
        refine ⟨4263407903789536170056843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2842271935859690780037895 4263407903789536170056843)
        ·
          refine ⟨6395111855684304255085265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4263407903789536170056843 6395111855684304255085265)
          ·
            refine ⟨4796333891763228191313949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6395111855684304255085265 4796333891763228191313949)
            ·
              refine ⟨1798625209411210571742731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4796333891763228191313949 1798625209411210571742731)
              ·
                refine ⟨2697937814116815857614097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1798625209411210571742731 2697937814116815857614097)
                ·
                  refine ⟨2023453360587611893210573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2697937814116815857614097 2023453360587611893210573)
                  ·
                    refine ⟨758795010220354459953965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2023453360587611893210573 758795010220354459953965)
                    ·
                      rfl

theorem cell22_2216622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_2216622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216622 prefixEnd_2216622 := by exact prefixLift 2216622
  have htrace : WordTrace (prefixWord ++ tailWord_2216622) baseStart_2216622 baseEnd_2216622 := by
    simpa [prefixWord, tailWord_2216622, baseEnd_2216622] using wordTrace_append hprefix tailTrace_2216622
  have hstable : (prefixWord ++ tailWord_2216622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216622).length < 2 ^ (prefixWord ++ tailWord_2216622).sum := by decide
  have hdescent : baseEnd_2216622 < baseStart_2216622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216650 : List Nat := [3, 1, 2, 1, 4, 1, 3, 3, 1, 3]
def baseStart_2216650 : Nat := 118140960795 + 2216650 * 2 ^ 59
def prefixEnd_2216650 : Nat := 4983230072969 + 3 ^ 40 * 2216650 * 2
def baseEnd_2216650 : Nat := 758804595192571720253879

theorem tailTrace_2216650 : CollatzResearch.WordTrace tailWord_2216650 prefixEnd_2216650 758804595192571720253879 := by
  unfold tailWord_2216650
  simp only [CollatzResearch.WordTrace]
  refine ⟨20211966854865774631329851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53898578279642065683546269 20211966854865774631329851)
  ·
    refine ⟨30317950282298661946994777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20211966854865774631329851 30317950282298661946994777)
    ·
      refine ⟨22738462711723996460246083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30317950282298661946994777 22738462711723996460246083)
      ·
        refine ⟨34107694067585994690369125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22738462711723996460246083 34107694067585994690369125)
        ·
          refine ⟨6395192637672374004444211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34107694067585994690369125 6395192637672374004444211)
          ·
            refine ⟨9592788956508561006666317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6395192637672374004444211 9592788956508561006666317)
            ·
              refine ⟨3597295858690710377499869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9592788956508561006666317 3597295858690710377499869)
              ·
                refine ⟨1348985947009016391562451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3597295858690710377499869 1348985947009016391562451)
                ·
                  refine ⟨2023478920513524587343677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1348985947009016391562451 2023478920513524587343677)
                  ·
                    refine ⟨758804595192571720253879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2023478920513524587343677 758804595192571720253879)
                    ·
                      rfl

theorem cell22_2216650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_2216650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216650 prefixEnd_2216650 := by exact prefixLift 2216650
  have htrace : WordTrace (prefixWord ++ tailWord_2216650) baseStart_2216650 baseEnd_2216650 := by
    simpa [prefixWord, tailWord_2216650, baseEnd_2216650] using wordTrace_append hprefix tailTrace_2216650
  have hstable : (prefixWord ++ tailWord_2216650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216650).length < 2 ^ (prefixWord ++ tailWord_2216650).sum := by decide
  have hdescent : baseEnd_2216650 < baseStart_2216650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216680 : List Nat := [2, 1, 4, 1, 4, 2, 2, 1, 5]
def baseStart_2216680 : Nat := 118140960795 + 2216680 * 2 ^ 59
def prefixEnd_2216680 : Nat := 4983230072969 + 3 ^ 40 * 2216680 * 2
def baseEnd_2216680 : Nat := 252938288268553880667929

theorem tailTrace_2216680 : CollatzResearch.WordTrace tailWord_2216680 prefixEnd_2216680 252938288268553880667929 := by
  unfold tailWord_2216680
  simp only [CollatzResearch.WordTrace]
  refine ⟨40424480804677206824455747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53899307739569609099274329 40424480804677206824455747)
  ·
    refine ⟨60636721207015810236683621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40424480804677206824455747 60636721207015810236683621)
    ·
      refine ⟨11369385226315464419378179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60636721207015810236683621 11369385226315464419378179)
      ·
        refine ⟨17054077839473196629067269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11369385226315464419378179 17054077839473196629067269)
        ·
          refine ⟨3197639594901224367950113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17054077839473196629067269 3197639594901224367950113)
          ·
            refine ⟨2398229696175918275962585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3197639594901224367950113 2398229696175918275962585)
            ·
              refine ⟨1798672272131938706971939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2398229696175918275962585 1798672272131938706971939)
              ·
                refine ⟨2698008408197908060457909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1798672272131938706971939 2698008408197908060457909)
                ·
                  refine ⟨252938288268553880667929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2698008408197908060457909 252938288268553880667929)
                  ·
                    rfl

theorem cell22_2216680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 5].length) (baseStart_2216680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216680 prefixEnd_2216680 := by exact prefixLift 2216680
  have htrace : WordTrace (prefixWord ++ tailWord_2216680) baseStart_2216680 baseEnd_2216680 := by
    simpa [prefixWord, tailWord_2216680, baseEnd_2216680] using wordTrace_append hprefix tailTrace_2216680
  have hstable : (prefixWord ++ tailWord_2216680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216680).length < 2 ^ (prefixWord ++ tailWord_2216680).sum := by decide
  have hdescent : baseEnd_2216680 < baseStart_2216680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216708 : List Nat := [2, 3, 2, 2, 1, 1, 2, 5, 4]
def baseStart_2216708 : Nat := 118140960795 + 2216708 * 2 ^ 59
def prefixEnd_2216708 : Nat := 4983230072969 + 3 ^ 40 * 2216708 * 2
def baseEnd_2216708 : Nat := 252941483259292967434567

theorem tailTrace_2216708 : CollatzResearch.WordTrace tailWord_2216708 prefixEnd_2216708 252941483259292967434567 := by
  unfold tailWord_2216708
  simp only [CollatzResearch.WordTrace]
  refine ⟨40424991426626487215465389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53899988568835316287287185 40424991426626487215465389)
  ·
    refine ⟨15159371784984932705799521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40424991426626487215465389 15159371784984932705799521)
    ·
      refine ⟨11369528838738699529349641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15159371784984932705799521 11369528838738699529349641)
      ·
        refine ⟨8527146629054024647012231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11369528838738699529349641 8527146629054024647012231)
        ·
          refine ⟨12790719943581036970518347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8527146629054024647012231 12790719943581036970518347)
          ·
            refine ⟨19186079915371555455777521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12790719943581036970518347 19186079915371555455777521)
            ·
              refine ⟨14389559936528666591833141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19186079915371555455777521 14389559936528666591833141)
              ·
                refine ⟨1349021244049562492984357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14389559936528666591833141 1349021244049562492984357)
                ·
                  refine ⟨252941483259292967434567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1349021244049562492984357 252941483259292967434567)
                  ·
                    rfl

theorem cell22_2216708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_2216708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216708 prefixEnd_2216708 := by exact prefixLift 2216708
  have htrace : WordTrace (prefixWord ++ tailWord_2216708) baseStart_2216708 baseEnd_2216708 := by
    simpa [prefixWord, tailWord_2216708, baseEnd_2216708] using wordTrace_append hprefix tailTrace_2216708
  have hstable : (prefixWord ++ tailWord_2216708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216708).length < 2 ^ (prefixWord ++ tailWord_2216708).sum := by decide
  have hdescent : baseEnd_2216708 < baseStart_2216708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216721 : List Nat := [1, 2, 2, 1, 1, 3, 4, 2, 2, 4]
def baseStart_2216721 : Nat := 118140960795 + 2216721 * 2 ^ 59
def prefixEnd_2216721 : Nat := 4983230072969 + 3 ^ 40 * 2216721 * 2
def baseEnd_2216721 : Nat := 758828899943551201728661

theorem tailTrace_2216721 : CollatzResearch.WordTrace tailWord_2216721 prefixEnd_2216721 758828899943551201728661 := by
  unfold tailWord_2216721
  simp only [CollatzResearch.WordTrace]
  refine ⟨80850457002205877651154017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53900304668137251767436011 80850457002205877651154017)
  ·
    refine ⟨60637842751654408238365513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80850457002205877651154017 60637842751654408238365513)
    ·
      refine ⟨45478382063740806178774135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60637842751654408238365513 45478382063740806178774135)
      ·
        refine ⟨68217573095611209268161203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45478382063740806178774135 68217573095611209268161203)
        ·
          refine ⟨102326359643416813902241805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68217573095611209268161203 102326359643416813902241805)
          ·
            refine ⟨38372384866281305213340677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102326359643416813902241805 38372384866281305213340677)
            ·
              refine ⟨7194822162427744727501377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38372384866281305213340677 7194822162427744727501377)
              ·
                refine ⟨5396116621820808545626033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7194822162427744727501377 5396116621820808545626033)
                ·
                  refine ⟨4047087466365606409219525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5396116621820808545626033 4047087466365606409219525)
                  ·
                    refine ⟨758828899943551201728661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4047087466365606409219525 758828899943551201728661)
                    ·
                      rfl

theorem cell22_2216721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_2216721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216721 prefixEnd_2216721 := by exact prefixLift 2216721
  have htrace : WordTrace (prefixWord ++ tailWord_2216721) baseStart_2216721 baseEnd_2216721 := by
    simpa [prefixWord, tailWord_2216721, baseEnd_2216721] using wordTrace_append hprefix tailTrace_2216721
  have hstable : (prefixWord ++ tailWord_2216721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216721).length < 2 ^ (prefixWord ++ tailWord_2216721).sum := by decide
  have hdescent : baseEnd_2216721 < baseStart_2216721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216723 : List Nat := [1, 1, 1, 2, 1, 3, 6, 2, 2, 3]
def baseStart_2216723 : Nat := 118140960795 + 2216723 * 2 ^ 59
def prefixEnd_2216723 : Nat := 4983230072969 + 3 ^ 40 * 2216723 * 2
def baseEnd_2216723 : Nat := 758829584584423863178655

theorem tailTrace_2216723 : CollatzResearch.WordTrace tailWord_2216723 prefixEnd_2216723 758829584584423863178655 := by
  unfold tailWord_2216723
  simp only [CollatzResearch.WordTrace]
  refine ⟨80850529948198631992726823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53900353298799087995151215 80850529948198631992726823)
  ·
    refine ⟨121275794922297947989090235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80850529948198631992726823 121275794922297947989090235)
    ·
      refine ⟨181913692383446921983635353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121275794922297947989090235 181913692383446921983635353)
      ·
        refine ⟨136435269287585191487726515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181913692383446921983635353 136435269287585191487726515)
        ·
          refine ⟨204652903931377787231589773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136435269287585191487726515 204652903931377787231589773)
          ·
            refine ⟨76744838974266670211846165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 204652903931377787231589773 76744838974266670211846165)
            ·
              refine ⟨3597414326918750166180289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76744838974266670211846165 3597414326918750166180289)
              ·
                refine ⟨2698060745189062624635217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3597414326918750166180289 2698060745189062624635217)
                ·
                  refine ⟨2023545558891796968476413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2698060745189062624635217 2023545558891796968476413)
                  ·
                    refine ⟨758829584584423863178655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2023545558891796968476413 758829584584423863178655)
                    ·
                      rfl

theorem cell22_2216723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 3].length) (baseStart_2216723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216723 prefixEnd_2216723 := by exact prefixLift 2216723
  have htrace : WordTrace (prefixWord ++ tailWord_2216723) baseStart_2216723 baseEnd_2216723 := by
    simpa [prefixWord, tailWord_2216723, baseEnd_2216723] using wordTrace_append hprefix tailTrace_2216723
  have hstable : (prefixWord ++ tailWord_2216723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216723).length < 2 ^ (prefixWord ++ tailWord_2216723).sum := by decide
  have hdescent : baseEnd_2216723 < baseStart_2216723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216736 : List Nat := [2, 1, 1, 5, 1, 2, 3, 7]
def baseStart_2216736 : Nat := 118140960795 + 2216736 * 2 ^ 59
def prefixEnd_2216736 : Nat := 4983230072969 + 3 ^ 40 * 2216736 * 2
def baseEnd_2216736 : Nat := 84314892750010684733735

theorem tailTrace_2216736 : CollatzResearch.WordTrace tailWord_2216736 prefixEnd_2216736 84314892750010684733735 := by
  unfold tailWord_2216736
  simp only [CollatzResearch.WordTrace]
  refine ⟨40425502048575767606475031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53900669398101023475300041 40425502048575767606475031)
  ·
    refine ⟨60638253072863651409712547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40425502048575767606475031 60638253072863651409712547)
    ·
      refine ⟨90957379609295477114568821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60638253072863651409712547 90957379609295477114568821)
      ·
        refine ⟨8527254338371450979490827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90957379609295477114568821 8527254338371450979490827)
        ·
          refine ⟨12790881507557176469236241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8527254338371450979490827 12790881507557176469236241)
          ·
            refine ⟨9593161130667882351927181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12790881507557176469236241 9593161130667882351927181)
            ·
              refine ⟨3597435424000455881972693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9593161130667882351927181 3597435424000455881972693)
              ·
                refine ⟨84314892750010684733735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3597435424000455881972693 84314892750010684733735)
                ·
                  rfl

theorem cell22_2216736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 7].length) (baseStart_2216736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216736 prefixEnd_2216736 := by exact prefixLift 2216736
  have htrace : WordTrace (prefixWord ++ tailWord_2216736) baseStart_2216736 baseEnd_2216736 := by
    simpa [prefixWord, tailWord_2216736, baseEnd_2216736] using wordTrace_append hprefix tailTrace_2216736
  have hstable : (prefixWord ++ tailWord_2216736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216736).length < 2 ^ (prefixWord ++ tailWord_2216736).sum := by decide
  have hdescent : baseEnd_2216736 < baseStart_2216736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216785 : List Nat := [1, 2, 2, 1, 6, 1, 2, 1, 3, 3]
def baseStart_2216785 : Nat := 118140960795 + 2216785 * 2 ^ 59
def prefixEnd_2216785 : Nat := 4983230072969 + 3 ^ 40 * 2216785 * 2
def baseEnd_2216785 : Nat := 758850808451476368128465

theorem tailTrace_2216785 : CollatzResearch.WordTrace tailWord_2216785 prefixEnd_2216785 758850808451476368128465 := by
  unfold tailWord_2216785
  simp only [CollatzResearch.WordTrace]
  refine ⟨80852791273974016581483809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53901860849316011054322539 80852791273974016581483809)
  ·
    refine ⟨60639593455480512436112857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80852791273974016581483809 60639593455480512436112857)
    ·
      refine ⟨45479695091610384327084643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60639593455480512436112857 45479695091610384327084643)
      ·
        refine ⟨68219542637415576490626965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45479695091610384327084643 68219542637415576490626965)
        ·
          refine ⟨3197791061128855147998139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 68219542637415576490626965 3197791061128855147998139)
          ·
            refine ⟨4796686591693282721997209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3197791061128855147998139 4796686591693282721997209)
            ·
              refine ⟨3597514943769962041497907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4796686591693282721997209 3597514943769962041497907)
              ·
                refine ⟨5396272415654943062246861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3597514943769962041497907 5396272415654943062246861)
                ·
                  refine ⟨2023602155870603648342573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5396272415654943062246861 2023602155870603648342573)
                  ·
                    refine ⟨758850808451476368128465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2023602155870603648342573 758850808451476368128465)
                    ·
                      rfl

theorem cell22_2216785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 3].length) (baseStart_2216785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216785 prefixEnd_2216785 := by exact prefixLift 2216785
  have htrace : WordTrace (prefixWord ++ tailWord_2216785) baseStart_2216785 baseEnd_2216785 := by
    simpa [prefixWord, tailWord_2216785, baseEnd_2216785] using wordTrace_append hprefix tailTrace_2216785
  have hstable : (prefixWord ++ tailWord_2216785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216785).length < 2 ^ (prefixWord ++ tailWord_2216785).sum := by decide
  have hdescent : baseEnd_2216785 < baseStart_2216785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216811 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 3, 4]
def baseStart_2216811 : Nat := 118140960795 + 2216811 * 2 ^ 59
def prefixEnd_2216811 : Nat := 4983230072969 + 3 ^ 40 * 2216811 * 2
def baseEnd_2216811 : Nat := 758859708782820966978385

theorem tailTrace_2216811 : CollatzResearch.WordTrace tailWord_2216811 prefixEnd_2216811 758859708782820966978385 := by
  unfold tailWord_2216811
  simp only [CollatzResearch.WordTrace]
  refine ⟨80853739571879823021930287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53902493047919882014620191 80853739571879823021930287)
  ·
    refine ⟨121280609357819734532895431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80853739571879823021930287 121280609357819734532895431)
    ·
      refine ⟨181920914036729601799343147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121280609357819734532895431 181920914036729601799343147)
      ·
        refine ⟨272881371055094402699014721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181920914036729601799343147 272881371055094402699014721)
        ·
          refine ⟨204661028291320802024261041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272881371055094402699014721 204661028291320802024261041)
          ·
            refine ⟨153495771218490601518195781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204661028291320802024261041 153495771218490601518195781)
            ·
              refine ⟨28780457103466987784661709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153495771218490601518195781 28780457103466987784661709)
              ·
                refine ⟨10792671413800120419248141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28780457103466987784661709 10792671413800120419248141)
                ·
                  refine ⟨4047251780175045157218053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10792671413800120419248141 4047251780175045157218053)
                  ·
                    refine ⟨758859708782820966978385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4047251780175045157218053 758859708782820966978385)
                    ·
                      rfl

theorem cell22_2216811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 4].length) (baseStart_2216811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216811 prefixEnd_2216811 := by exact prefixLift 2216811
  have htrace : WordTrace (prefixWord ++ tailWord_2216811) baseStart_2216811 baseEnd_2216811 := by
    simpa [prefixWord, tailWord_2216811, baseEnd_2216811] using wordTrace_append hprefix tailTrace_2216811
  have hstable : (prefixWord ++ tailWord_2216811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216811).length < 2 ^ (prefixWord ++ tailWord_2216811).sum := by decide
  have hdescent : baseEnd_2216811 < baseStart_2216811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216843 : List Nat := [1, 1, 1, 1, 4, 2, 2, 6, 4]
def baseStart_2216843 : Nat := 118140960795 + 2216843 * 2 ^ 59
def prefixEnd_2216843 : Nat := 4983230072969 + 3 ^ 40 * 2216843 * 2
def baseEnd_2216843 : Nat := 252956887678927850059429

theorem tailTrace_2216843 : CollatzResearch.WordTrace tailWord_2216843 prefixEnd_2216843 252956887678927850059429 := by
  unfold tailWord_2216843
  simp only [CollatzResearch.WordTrace]
  refine ⟨80854906707763892487095183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53903271138509261658063455 80854906707763892487095183)
  ·
    refine ⟨121282360061645838730642775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80854906707763892487095183 121282360061645838730642775)
    ·
      refine ⟨181923540092468758095964163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121282360061645838730642775 181923540092468758095964163)
      ·
        refine ⟨272885310138703137143946245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181923540092468758095964163 272885310138703137143946245)
        ·
          refine ⟨51165995651006838214489921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 272885310138703137143946245 51165995651006838214489921)
          ·
            refine ⟨38374496738255128660867441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51165995651006838214489921 38374496738255128660867441)
            ·
              refine ⟨28780872553691346495650581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38374496738255128660867441 28780872553691346495650581)
              ·
                refine ⟨1349103400954281866983621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28780872553691346495650581 1349103400954281866983621)
                ·
                  refine ⟨252956887678927850059429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1349103400954281866983621 252956887678927850059429)
                  ·
                    rfl

theorem cell22_2216843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 4].length) (baseStart_2216843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216843 prefixEnd_2216843 := by exact prefixLift 2216843
  have htrace : WordTrace (prefixWord ++ tailWord_2216843) baseStart_2216843 baseEnd_2216843 := by
    simpa [prefixWord, tailWord_2216843, baseEnd_2216843] using wordTrace_append hprefix tailTrace_2216843
  have hstable : (prefixWord ++ tailWord_2216843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216843).length < 2 ^ (prefixWord ++ tailWord_2216843).sum := by decide
  have hdescent : baseEnd_2216843 < baseStart_2216843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216873 : List Nat := [1, 2, 1, 1, 1, 1, 8, 1, 2, 4]
def baseStart_2216873 : Nat := 118140960795 + 2216873 * 2 ^ 59
def prefixEnd_2216873 : Nat := 4983230072969 + 3 ^ 40 * 2216873 * 2
def baseEnd_2216873 : Nat := 758880932649873471928195

theorem tailTrace_2216873 : CollatzResearch.WordTrace tailWord_2216873 prefixEnd_2216873 758880932649873471928195 := by
  unfold tailWord_2216873
  simp only [CollatzResearch.WordTrace]
  refine ⟨80856000897655207610687273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53904000598436805073791515 80856000897655207610687273)
  ·
    refine ⟨60642000673241405708015455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80856000897655207610687273 60642000673241405708015455)
    ·
      refine ⟨90963001009862108562023183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60642000673241405708015455 90963001009862108562023183)
      ·
        refine ⟨136444501514793162843034775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90963001009862108562023183 136444501514793162843034775)
        ·
          refine ⟨204666752272189744264552163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136444501514793162843034775 204666752272189744264552163)
          ·
            refine ⟨307000128408284616396828245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204666752272189744264552163 307000128408284616396828245)
            ·
              refine ⟨3597657754784585348400331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 307000128408284616396828245 3597657754784585348400331)
              ·
                refine ⟨5396486632176878022600497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3597657754784585348400331 5396486632176878022600497)
                ·
                  refine ⟨4047364974132658516950373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5396486632176878022600497 4047364974132658516950373)
                  ·
                    refine ⟨758880932649873471928195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4047364974132658516950373 758880932649873471928195)
                    ·
                      rfl

theorem cell22_2216873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 4].length) (baseStart_2216873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216873 prefixEnd_2216873 := by exact prefixLift 2216873
  have htrace : WordTrace (prefixWord ++ tailWord_2216873) baseStart_2216873 baseEnd_2216873 := by
    simpa [prefixWord, tailWord_2216873, baseEnd_2216873] using wordTrace_append hprefix tailTrace_2216873
  have hstable : (prefixWord ++ tailWord_2216873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216873).length < 2 ^ (prefixWord ++ tailWord_2216873).sum := by decide
  have hdescent : baseEnd_2216873 < baseStart_2216873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216920 : List Nat := [2, 1, 2, 2, 2, 4, 1, 2, 3, 3]
def baseStart_2216920 : Nat := 118140960795 + 2216920 * 2 ^ 59
def prefixEnd_2216920 : Nat := 4983230072969 + 3 ^ 40 * 2216920 * 2
def baseEnd_2216920 : Nat := 758897021710381016003051

theorem tailTrace_2216920 : CollatzResearch.WordTrace tailWord_2216920 prefixEnd_2216920 758897021710381016003051 := by
  unfold tailWord_2216920
  simp only [CollatzResearch.WordTrace]
  refine ⟨40428857564242467318824107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53905143418989956425098809 40428857564242467318824107)
  ·
    refine ⟨60643286346363700978236161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40428857564242467318824107 60643286346363700978236161)
    ·
      refine ⟨45482464759772775733677121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60643286346363700978236161 45482464759772775733677121)
      ·
        refine ⟨34111848569829581800257841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45482464759772775733677121 34111848569829581800257841)
        ·
          refine ⟨25583886427372186350193381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34111848569829581800257841 25583886427372186350193381)
          ·
            refine ⟨4796978705132284940661259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25583886427372186350193381 4796978705132284940661259)
            ·
              refine ⟨7195468057698427410991889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4796978705132284940661259 7195468057698427410991889)
              ·
                refine ⟨5396601043273820558243917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7195468057698427410991889 5396601043273820558243917)
                ·
                  refine ⟨2023725391227682709341469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5396601043273820558243917 2023725391227682709341469)
                  ·
                    refine ⟨758897021710381016003051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2023725391227682709341469 758897021710381016003051)
                    ·
                      rfl

theorem cell22_2216920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 3, 3].length) (baseStart_2216920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216920 prefixEnd_2216920 := by exact prefixLift 2216920
  have htrace : WordTrace (prefixWord ++ tailWord_2216920) baseStart_2216920 baseEnd_2216920 := by
    simpa [prefixWord, tailWord_2216920, baseEnd_2216920] using wordTrace_append hprefix tailTrace_2216920
  have hstable : (prefixWord ++ tailWord_2216920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216920).length < 2 ^ (prefixWord ++ tailWord_2216920).sum := by decide
  have hdescent : baseEnd_2216920 < baseStart_2216920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216950 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 7]
def baseStart_2216950 : Nat := 118140960795 + 2216950 * 2 ^ 59
def prefixEnd_2216950 : Nat := 4983230072969 + 3 ^ 40 * 2216950 * 2
def baseEnd_2216950 : Nat := 252969097107823645917653

theorem tailTrace_2216950 : CollatzResearch.WordTrace tailWord_2216950 prefixEnd_2216950 252969097107823645917653 := by
  unfold tailWord_2216950
  simp only [CollatzResearch.WordTrace]
  refine ⟨5053675582398515610077519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53905872878917499840826869 5053675582398515610077519)
  ·
    refine ⟨7580513373597773415116279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5053675582398515610077519 7580513373597773415116279)
    ·
      refine ⟨11370770060396660122674419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7580513373597773415116279 11370770060396660122674419)
      ·
        refine ⟨17056155090594990184011629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11370770060396660122674419 17056155090594990184011629)
        ·
          refine ⟨6396058158973121319004361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17056155090594990184011629 6396058158973121319004361)
          ·
            refine ⟨4797043619229840989253271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6396058158973121319004361 4797043619229840989253271)
            ·
              refine ⟨7195565428844761483879907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4797043619229840989253271 7195565428844761483879907)
              ·
                refine ⟨10793348143267142225819861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7195565428844761483879907 10793348143267142225819861)
                ·
                  refine ⟨252969097107823645917653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10793348143267142225819861 252969097107823645917653)
                  ·
                    rfl

theorem cell22_2216950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_2216950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2216950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2216950 prefixEnd_2216950 := by exact prefixLift 2216950
  have htrace : WordTrace (prefixWord ++ tailWord_2216950) baseStart_2216950 baseEnd_2216950 := by
    simpa [prefixWord, tailWord_2216950, baseEnd_2216950] using wordTrace_append hprefix tailTrace_2216950
  have hstable : (prefixWord ++ tailWord_2216950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216950).length < 2 ^ (prefixWord ++ tailWord_2216950).sum := by decide
  have hdescent : baseEnd_2216950 < baseStart_2216950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217010 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 4, 3]
def baseStart_2217010 : Nat := 118140960795 + 2217010 * 2 ^ 59
def prefixEnd_2217010 : Nat := 4983230072969 + 3 ^ 40 * 2217010 * 2
def baseEnd_2217010 : Nat := 758927830549650781252775

theorem tailTrace_2217010 : CollatzResearch.WordTrace tailWord_2217010 prefixEnd_2217010 758927830549650781252775 := by
  unfold tailWord_2217010
  simp only [CollatzResearch.WordTrace]
  refine ⟨20215249424539720002106121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53907331798772586672282989 20215249424539720002106121)
  ·
    refine ⟨15161437068404790001579591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20215249424539720002106121 15161437068404790001579591)
    ·
      refine ⟨22742155602607185002369387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15161437068404790001579591 22742155602607185002369387)
      ·
        refine ⟨34113233403910777503554081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22742155602607185002369387 34113233403910777503554081)
        ·
          refine ⟨25584925052933083127665561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34113233403910777503554081 25584925052933083127665561)
          ·
            refine ⟨19188693789699812345749171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25584925052933083127665561 19188693789699812345749171)
            ·
              refine ⟨28783040684549718518623757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19188693789699812345749171 28783040684549718518623757)
              ·
                refine ⟨10793640256706144444483909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28783040684549718518623757 10793640256706144444483909)
                ·
                  refine ⟨2023807548132402083340733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10793640256706144444483909 2023807548132402083340733)
                  ·
                    refine ⟨758927830549650781252775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2023807548132402083340733 758927830549650781252775)
                    ·
                      rfl

theorem cell22_2217010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_2217010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217010 prefixEnd_2217010 := by exact prefixLift 2217010
  have htrace : WordTrace (prefixWord ++ tailWord_2217010) baseStart_2217010 baseEnd_2217010 := by
    simpa [prefixWord, tailWord_2217010, baseEnd_2217010] using wordTrace_append hprefix tailTrace_2217010
  have hstable : (prefixWord ++ tailWord_2217010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217010).length < 2 ^ (prefixWord ++ tailWord_2217010).sum := by decide
  have hdescent : baseEnd_2217010 < baseStart_2217010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217012 : List Nat := [2, 5, 1, 2, 1, 1, 3, 1, 6]
def baseStart_2217012 : Nat := 118140960795 + 2217012 * 2 ^ 59
def prefixEnd_2217012 : Nat := 4983230072969 + 3 ^ 40 * 2217012 * 2
def baseEnd_2217012 : Nat := 252976171730174480900923

theorem tailTrace_2217012 : CollatzResearch.WordTrace tailWord_2217012 prefixEnd_2217012 252976171730174480900923 := by
  unfold tailWord_2217012
  simp only [CollatzResearch.WordTrace]
  refine ⟨40430535322075817174998645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53907380429434422899998193 40430535322075817174998645)
  ·
    refine ⟨3790362686444607860156123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40430535322075817174998645 3790362686444607860156123)
    ·
      refine ⟨5685544029666911790234185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3790362686444607860156123 5685544029666911790234185)
      ·
        refine ⟨4264158022250183842675639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5685544029666911790234185 4264158022250183842675639)
        ·
          refine ⟨6396237033375275764013459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4264158022250183842675639 6396237033375275764013459)
          ·
            refine ⟨9594355550062913646020189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6396237033375275764013459 9594355550062913646020189)
            ·
              refine ⟨3597883331273592617257571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9594355550062913646020189 3597883331273592617257571)
              ·
                refine ⟨5396824996910388925886357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3597883331273592617257571 5396824996910388925886357)
                ·
                  refine ⟨252976171730174480900923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5396824996910388925886357 252976171730174480900923)
                  ·
                    rfl

theorem cell22_2217012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_2217012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217012 prefixEnd_2217012 := by exact prefixLift 2217012
  have htrace : WordTrace (prefixWord ++ tailWord_2217012) baseStart_2217012 baseEnd_2217012 := by
    simpa [prefixWord, tailWord_2217012, baseEnd_2217012] using wordTrace_append hprefix tailTrace_2217012
  have hstable : (prefixWord ++ tailWord_2217012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217012).length < 2 ^ (prefixWord ++ tailWord_2217012).sum := by decide
  have hdescent : baseEnd_2217012 < baseStart_2217012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217042 : List Nat := [3, 2, 2, 1, 3, 2, 2, 1, 2, 4]
def baseStart_2217042 : Nat := 118140960795 + 2217042 * 2 ^ 59
def prefixEnd_2217042 : Nat := 4983230072969 + 3 ^ 40 * 2217042 * 2
def baseEnd_2217042 : Nat := 758938784803613364452677

theorem tailTrace_2217042 : CollatzResearch.WordTrace tailWord_2217042 prefixEnd_2217042 758938784803613364452677 := by
  unfold tailWord_2217042
  simp only [CollatzResearch.WordTrace]
  refine ⟨20215541208510737368397345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53908109889361966315726253 20215541208510737368397345)
  ·
    refine ⟨15161655906383053026298009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20215541208510737368397345 15161655906383053026298009)
    ·
      refine ⟨11371241929787289769723507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15161655906383053026298009 11371241929787289769723507)
      ·
        refine ⟨17056862894680934654585261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11371241929787289769723507 17056862894680934654585261)
        ·
          refine ⟨6396323585505350495469473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17056862894680934654585261 6396323585505350495469473)
          ·
            refine ⟨4797242689129012871602105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6396323585505350495469473 4797242689129012871602105)
            ·
              refine ⟨3597932016846759653701579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4797242689129012871602105 3597932016846759653701579)
              ·
                refine ⟨5396898025270139480552369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3597932016846759653701579 5396898025270139480552369)
                ·
                  refine ⟨4047673518952604610414277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5396898025270139480552369 4047673518952604610414277)
                  ·
                    refine ⟨758938784803613364452677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4047673518952604610414277 758938784803613364452677)
                    ·
                      rfl

theorem cell22_2217042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_2217042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217042 prefixEnd_2217042 := by exact prefixLift 2217042
  have htrace : WordTrace (prefixWord ++ tailWord_2217042) baseStart_2217042 baseEnd_2217042 := by
    simpa [prefixWord, tailWord_2217042, baseEnd_2217042] using wordTrace_append hprefix tailTrace_2217042
  have hstable : (prefixWord ++ tailWord_2217042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217042).length < 2 ^ (prefixWord ++ tailWord_2217042).sum := by decide
  have hdescent : baseEnd_2217042 < baseStart_2217042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217070 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 2, 6]
def baseStart_2217070 : Nat := 118140960795 + 2217070 * 2 ^ 59
def prefixEnd_2217070 : Nat := 4983230072969 + 3 ^ 40 * 2217070 * 2
def baseEnd_2217070 : Nat := 758948369775830624752591

theorem tailTrace_2217070 : CollatzResearch.WordTrace tailWord_2217070 prefixEnd_2217070 758948369775830624752591 := by
  unfold tailWord_2217070
  simp only [CollatzResearch.WordTrace]
  refine ⟨10107898259742688781951083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53908790718627673503739109 10107898259742688781951083)
  ·
    refine ⟨15161847389614033172926625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10107898259742688781951083 15161847389614033172926625)
    ·
      refine ⟨11371385542210524879694969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15161847389614033172926625 11371385542210524879694969)
      ·
        refine ⟨8528539156657893659771227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11371385542210524879694969 8528539156657893659771227)
        ·
          refine ⟨12792808734986840489656841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8528539156657893659771227 12792808734986840489656841)
          ·
            refine ⟨9594606551240130367242631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12792808734986840489656841 9594606551240130367242631)
            ·
              refine ⟨14391909826860195550863947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9594606551240130367242631 14391909826860195550863947)
              ·
                refine ⟨21587864740290293326295921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14391909826860195550863947 21587864740290293326295921)
                ·
                  refine ⟨16190898555217719994721941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21587864740290293326295921 16190898555217719994721941)
                  ·
                    refine ⟨758948369775830624752591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16190898555217719994721941 758948369775830624752591)
                    ·
                      rfl

theorem cell22_2217070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_2217070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217070 prefixEnd_2217070 := by exact prefixLift 2217070
  have htrace : WordTrace (prefixWord ++ tailWord_2217070) baseStart_2217070 baseEnd_2217070 := by
    simpa [prefixWord, tailWord_2217070, baseEnd_2217070] using wordTrace_append hprefix tailTrace_2217070
  have hstable : (prefixWord ++ tailWord_2217070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217070).length < 2 ^ (prefixWord ++ tailWord_2217070).sum := by decide
  have hdescent : baseEnd_2217070 < baseStart_2217070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217085 : List Nat := [1, 4, 1, 1, 3, 1, 1, 5, 5]
def baseStart_2217085 : Nat := 118140960795 + 2217085 * 2 ^ 59
def prefixEnd_2217085 : Nat := 4983230072969 + 3 ^ 40 * 2217085 * 2
def baseEnd_2217085 : Nat := 252984501527458528542515

theorem tailTrace_2217085 : CollatzResearch.WordTrace tailWord_2217085 prefixEnd_2217085 252984501527458528542515 := by
  unfold tailWord_2217085
  simp only [CollatzResearch.WordTrace]
  refine ⟨80863733172887167817404709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53909155448591445211603139 80863733172887167817404709)
  ·
    refine ⟨15161949969916343965763383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80863733172887167817404709 15161949969916343965763383)
    ·
      refine ⟨22742924954874515948645075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15161949969916343965763383 22742924954874515948645075)
      ·
        refine ⟨34114387432311773922967613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22742924954874515948645075 34114387432311773922967613)
        ·
          refine ⟨12792895287116915221112855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34114387432311773922967613 12792895287116915221112855)
          ·
            refine ⟨19189342930675372831669283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12792895287116915221112855 19189342930675372831669283)
            ·
              refine ⟨28784014396013059247503925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19189342930675372831669283 28784014396013059247503925)
              ·
                refine ⟨2698501349626224304453493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28784014396013059247503925 2698501349626224304453493)
                ·
                  refine ⟨252984501527458528542515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2698501349626224304453493 252984501527458528542515)
                  ·
                    rfl

theorem cell22_2217085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_2217085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217085 prefixEnd_2217085 := by exact prefixLift 2217085
  have htrace : WordTrace (prefixWord ++ tailWord_2217085) baseStart_2217085 baseEnd_2217085 := by
    simpa [prefixWord, tailWord_2217085, baseEnd_2217085] using wordTrace_append hprefix tailTrace_2217085
  have hstable : (prefixWord ++ tailWord_2217085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217085).length < 2 ^ (prefixWord ++ tailWord_2217085).sum := by decide
  have hdescent : baseEnd_2217085 < baseStart_2217085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217106 : List Nat := [3, 2, 3, 1, 1, 3, 2, 3, 1, 3]
def baseStart_2217106 : Nat := 118140960795 + 2217106 * 2 ^ 59
def prefixEnd_2217106 : Nat := 4983230072969 + 3 ^ 40 * 2217106 * 2
def baseEnd_2217106 : Nat := 758960693311538530852481

theorem tailTrace_2217106 : CollatzResearch.WordTrace tailWord_2217106 prefixEnd_2217106 758960693311538530852481 := by
  unfold tailWord_2217106
  simp only [CollatzResearch.WordTrace]
  refine ⟨20216124776452772100979793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53909666070540725602612781 20216124776452772100979793)
  ·
    refine ⟨15162093582339579075734845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20216124776452772100979793 15162093582339579075734845)
    ·
      refine ⟨5685785093377342153400567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15162093582339579075734845 5685785093377342153400567)
      ·
        refine ⟨8528677640066013230100851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5685785093377342153400567 8528677640066013230100851)
        ·
          refine ⟨12793016460099019845151277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8528677640066013230100851 12793016460099019845151277)
          ·
            refine ⟨4797381172537132441931729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12793016460099019845151277 4797381172537132441931729)
            ·
              refine ⟨3598035879402849331448797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4797381172537132441931729 3598035879402849331448797)
              ·
                refine ⟨1349263454776068499293299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3598035879402849331448797 1349263454776068499293299)
                ·
                  refine ⟨2023895182164102748939949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1349263454776068499293299 2023895182164102748939949)
                  ·
                    refine ⟨758960693311538530852481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2023895182164102748939949 758960693311538530852481)
                    ·
                      rfl

theorem cell22_2217106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_2217106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217106 prefixEnd_2217106 := by exact prefixLift 2217106
  have htrace : WordTrace (prefixWord ++ tailWord_2217106) baseStart_2217106 baseEnd_2217106 := by
    simpa [prefixWord, tailWord_2217106, baseEnd_2217106] using wordTrace_append hprefix tailTrace_2217106
  have hstable : (prefixWord ++ tailWord_2217106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217106).length < 2 ^ (prefixWord ++ tailWord_2217106).sum := by decide
  have hdescent : baseEnd_2217106 < baseStart_2217106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217119 : List Nat := [1, 1, 2, 6, 2, 2, 1, 2, 5]
def baseStart_2217119 : Nat := 118140960795 + 2217119 * 2 ^ 59
def prefixEnd_2217119 : Nat := 4983230072969 + 3 ^ 40 * 2217119 * 2
def baseEnd_2217119 : Nat := 252988381159070276759147

theorem tailTrace_2217119 : CollatzResearch.WordTrace tailWord_2217119 prefixEnd_2217119 252988381159070276759147 := by
  unfold tailWord_2217119
  simp only [CollatzResearch.WordTrace]
  refine ⟨80864973254763991624142411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53909982169842661082761607 80864973254763991624142411)
  ·
    refine ⟨121297459882145987436213617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80864973254763991624142411 121297459882145987436213617)
    ·
      refine ⟨90973094911609490577160213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121297459882145987436213617 90973094911609490577160213)
      ·
        refine ⟨4264363823981694870804385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 90973094911609490577160213 4264363823981694870804385)
        ·
          refine ⟨3198272867986271153103289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4264363823981694870804385 3198272867986271153103289)
          ·
            refine ⟨2398704650989703364827467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3198272867986271153103289 2398704650989703364827467)
            ·
              refine ⟨3598056976484555047241201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2398704650989703364827467 3598056976484555047241201)
              ·
                refine ⟨2698542732363416285430901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3598056976484555047241201 2698542732363416285430901)
                ·
                  refine ⟨252988381159070276759147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2698542732363416285430901 252988381159070276759147)
                  ·
                    rfl

theorem cell22_2217119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 5].length) (baseStart_2217119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217119 prefixEnd_2217119 := by exact prefixLift 2217119
  have htrace : WordTrace (prefixWord ++ tailWord_2217119) baseStart_2217119 baseEnd_2217119 := by
    simpa [prefixWord, tailWord_2217119, baseEnd_2217119] using wordTrace_append hprefix tailTrace_2217119
  have hstable : (prefixWord ++ tailWord_2217119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217119).length < 2 ^ (prefixWord ++ tailWord_2217119).sum := by decide
  have hdescent : baseEnd_2217119 < baseStart_2217119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217160 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 1, 6]
def baseStart_2217160 : Nat := 118140960795 + 2217160 * 2 ^ 59
def prefixEnd_2217160 : Nat := 4983230072969 + 3 ^ 40 * 2217160 * 2
def baseEnd_2217160 : Nat := 758979178615100390002315

theorem tailTrace_2217160 : CollatzResearch.WordTrace tailWord_2217160 prefixEnd_2217160 758979178615100390002315 := by
  unfold tailWord_2217160
  simp only [CollatzResearch.WordTrace]
  refine ⟨40433234323807727813192467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53910979098410303750923289 40433234323807727813192467)
  ·
    refine ⟨60649851485711591719788701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40433234323807727813192467 60649851485711591719788701)
    ·
      refine ⟨22743694307141846894920763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60649851485711591719788701 22743694307141846894920763)
      ·
        refine ⟨34115541460712770342381145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22743694307141846894920763 34115541460712770342381145)
        ·
          refine ⟨25586656095534577756785859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34115541460712770342381145 25586656095534577756785859)
          ·
            refine ⟨38379984143301866635178789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25586656095534577756785859 38379984143301866635178789)
            ·
              refine ⟨7196247026869099994096023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38379984143301866635178789 7196247026869099994096023)
              ·
                refine ⟨10794370540303649991144035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7196247026869099994096023 10794370540303649991144035)
                ·
                  refine ⟨16191555810455474986716053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10794370540303649991144035 16191555810455474986716053)
                  ·
                    refine ⟨758979178615100390002315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16191555810455474986716053 758979178615100390002315)
                    ·
                      rfl

theorem cell22_2217160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_2217160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217160 prefixEnd_2217160 := by exact prefixLift 2217160
  have htrace : WordTrace (prefixWord ++ tailWord_2217160) baseStart_2217160 baseEnd_2217160 := by
    simpa [prefixWord, tailWord_2217160, baseEnd_2217160] using wordTrace_append hprefix tailTrace_2217160
  have hstable : (prefixWord ++ tailWord_2217160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217160).length < 2 ^ (prefixWord ++ tailWord_2217160).sum := by decide
  have hdescent : baseEnd_2217160 < baseStart_2217160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217162 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 4, 3]
def baseStart_2217162 : Nat := 118140960795 + 2217162 * 2 ^ 59
def prefixEnd_2217162 : Nat := 4983230072969 + 3 ^ 40 * 2217162 * 2
def baseEnd_2217162 : Nat := 758979863255973051452309

theorem tailTrace_2217162 : CollatzResearch.WordTrace tailWord_2217162 prefixEnd_2217162 758979863255973051452309 := by
  unfold tailWord_2217162
  simp only [CollatzResearch.WordTrace]
  refine ⟨20216635398402052491989435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53911027729072139978638493 20216635398402052491989435)
  ·
    refine ⟨30324953097603078737984153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20216635398402052491989435 30324953097603078737984153)
    ·
      refine ⟨22743714823202309053488115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30324953097603078737984153 22743714823202309053488115)
      ·
        refine ⟨34115572234803463580232173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22743714823202309053488115 34115572234803463580232173)
        ·
          refine ⟨12793339588051298842587065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34115572234803463580232173 12793339588051298842587065)
          ·
            refine ⟨9595004691038474131940299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12793339588051298842587065 9595004691038474131940299)
            ·
              refine ⟨14392507036557711197910449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9595004691038474131940299 14392507036557711197910449)
              ·
                refine ⟨10794380277418283398432837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14392507036557711197910449 10794380277418283398432837)
                ·
                  refine ⟨2023946302015928137206157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10794380277418283398432837 2023946302015928137206157)
                  ·
                    refine ⟨758979863255973051452309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2023946302015928137206157 758979863255973051452309)
                    ·
                      rfl

theorem cell22_2217162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_2217162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217162 prefixEnd_2217162 := by exact prefixLift 2217162
  have htrace : WordTrace (prefixWord ++ tailWord_2217162) baseStart_2217162 baseEnd_2217162 := by
    simpa [prefixWord, tailWord_2217162, baseEnd_2217162] using wordTrace_append hprefix tailTrace_2217162
  have hstable : (prefixWord ++ tailWord_2217162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217162).length < 2 ^ (prefixWord ++ tailWord_2217162).sum := by decide
  have hdescent : baseEnd_2217162 < baseStart_2217162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217181 : List Nat := [1, 4, 3, 2, 3, 1, 1, 1, 6]
def baseStart_2217181 : Nat := 118140960795 + 2217181 * 2 ^ 59
def prefixEnd_2217181 : Nat := 4983230072969 + 3 ^ 40 * 2217181 * 2
def baseEnd_2217181 : Nat := 252995455781421111742417

theorem tailTrace_2217181 : CollatzResearch.WordTrace tailWord_2217181 prefixEnd_2217181 252995455781421111742417 := by
  unfold tailWord_2217181
  simp only [CollatzResearch.WordTrace]
  refine ⟨80867234580539376212899397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53911489720359584141932931 80867234580539376212899397)
  ·
    refine ⟨15162606483851133039918637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80867234580539376212899397 15162606483851133039918637)
    ·
      refine ⟨5685977431444174889969489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15162606483851133039918637 5685977431444174889969489)
      ·
        refine ⟨4264483073583131167477117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5685977431444174889969489 4264483073583131167477117)
        ·
          refine ⟨1599181152593674187803919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4264483073583131167477117 1599181152593674187803919)
          ·
            refine ⟨2398771728890511281705879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1599181152593674187803919 2398771728890511281705879)
            ·
              refine ⟨3598157593335766922558819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2398771728890511281705879 3598157593335766922558819)
              ·
                refine ⟨5397236390003650383838229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3598157593335766922558819 5397236390003650383838229)
                ·
                  refine ⟨252995455781421111742417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5397236390003650383838229 252995455781421111742417)
                  ·
                    rfl

theorem cell22_2217181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_2217181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217181 prefixEnd_2217181 := by exact prefixLift 2217181
  have htrace : WordTrace (prefixWord ++ tailWord_2217181) baseStart_2217181 baseEnd_2217181 := by
    simpa [prefixWord, tailWord_2217181, baseEnd_2217181] using wordTrace_append hprefix tailTrace_2217181
  have hstable : (prefixWord ++ tailWord_2217181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217181).length < 2 ^ (prefixWord ++ tailWord_2217181).sum := by decide
  have hdescent : baseEnd_2217181 < baseStart_2217181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217196 : List Nat := [2, 2, 1, 1, 2, 6, 2, 1, 2, 3]
def baseStart_2217196 : Nat := 118140960795 + 2217196 * 2 ^ 59
def prefixEnd_2217196 : Nat := 4983230072969 + 3 ^ 40 * 2217196 * 2
def baseEnd_2217196 : Nat := 758991502150808296102205

theorem tailTrace_2217196 : CollatzResearch.WordTrace tailWord_2217196 prefixEnd_2217196 758991502150808296102205 := by
  unfold tailWord_2217196
  simp only [CollatzResearch.WordTrace]
  refine ⟨40433890837742516887347721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53911854450323355849796961 40433890837742516887347721)
  ·
    refine ⟨30325418128306887665510791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40433890837742516887347721 30325418128306887665510791)
    ·
      refine ⟨45488127192460331498266187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30325418128306887665510791 45488127192460331498266187)
      ·
        refine ⟨68232190788690497247399281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45488127192460331498266187 68232190788690497247399281)
        ·
          refine ⟨51174143091517872935549461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68232190788690497247399281 51174143091517872935549461)
          ·
            refine ⟨2398787957414900293853881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 51174143091517872935549461 2398787957414900293853881)
            ·
              refine ⟨1799090968061175220390411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2398787957414900293853881 1799090968061175220390411)
              ·
                refine ⟨2698636452091762830585617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1799090968061175220390411 2698636452091762830585617)
                ·
                  refine ⟨2023977339068822122939213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2698636452091762830585617 2023977339068822122939213)
                  ·
                    refine ⟨758991502150808296102205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2023977339068822122939213 758991502150808296102205)
                    ·
                      rfl

theorem cell22_2217196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 3].length) (baseStart_2217196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217196 prefixEnd_2217196 := by exact prefixLift 2217196
  have htrace : WordTrace (prefixWord ++ tailWord_2217196) baseStart_2217196 baseEnd_2217196 := by
    simpa [prefixWord, tailWord_2217196, baseEnd_2217196] using wordTrace_append hprefix tailTrace_2217196
  have hstable : (prefixWord ++ tailWord_2217196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217196).length < 2 ^ (prefixWord ++ tailWord_2217196).sum := by decide
  have hdescent : baseEnd_2217196 < baseStart_2217196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217252 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 2, 5]
def baseStart_2217252 : Nat := 118140960795 + 2217252 * 2 ^ 59
def prefixEnd_2217252 : Nat := 4983230072969 + 3 ^ 40 * 2217252 * 2
def baseEnd_2217252 : Nat := 759010672095242816702033

theorem tailTrace_2217252 : CollatzResearch.WordTrace tailWord_2217252 prefixEnd_2217252 759010672095242816702033 := by
  unfold tailWord_2217252
  simp only [CollatzResearch.WordTrace]
  refine ⟨40434912081641077669367005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53913216108854770225822673 40434912081641077669367005)
  ·
    refine ⟨15163092030615404126012627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40434912081641077669367005 15163092030615404126012627)
    ·
      refine ⟨22744638045923106189018941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15163092030615404126012627 22744638045923106189018941)
      ·
        refine ⟨8529239267221164820882103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22744638045923106189018941 8529239267221164820882103)
        ·
          refine ⟨12793858900831747231323155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8529239267221164820882103 12793858900831747231323155)
          ·
            refine ⟨19190788351247620846984733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12793858900831747231323155 19190788351247620846984733)
            ·
              refine ⟨7196545631717857817619275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19190788351247620846984733 7196545631717857817619275)
              ·
                refine ⟨10794818447576786726428913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7196545631717857817619275 10794818447576786726428913)
                ·
                  refine ⟨8096113835682590044821685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10794818447576786726428913 8096113835682590044821685)
                  ·
                    refine ⟨759010672095242816702033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8096113835682590044821685 759010672095242816702033)
                    ·
                      rfl

theorem cell22_2217252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_2217252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217252 prefixEnd_2217252 := by exact prefixLift 2217252
  have htrace : WordTrace (prefixWord ++ tailWord_2217252) baseStart_2217252 baseEnd_2217252 := by
    simpa [prefixWord, tailWord_2217252, baseEnd_2217252] using wordTrace_append hprefix tailTrace_2217252
  have hstable : (prefixWord ++ tailWord_2217252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217252).length < 2 ^ (prefixWord ++ tailWord_2217252).sum := by decide
  have hdescent : baseEnd_2217252 < baseStart_2217252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217267 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 3, 4]
def baseStart_2217267 : Nat := 118140960795 + 2217267 * 2 ^ 59
def prefixEnd_2217267 : Nat := 4983230072969 + 3 ^ 40 * 2217267 * 2
def baseEnd_2217267 : Nat := 759015806901787777576987

theorem tailTrace_2217267 : CollatzResearch.WordTrace tailWord_2217267 prefixEnd_2217267 759015806901787777576987 := by
  unfold tailWord_2217267
  simp only [CollatzResearch.WordTrace]
  refine ⟨80870371258227812900530055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53913580838818541933686703 80870371258227812900530055)
  ·
    refine ⟨121305556887341719350795083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80870371258227812900530055 121305556887341719350795083)
    ·
      refine ⟨181958335331012579026192625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121305556887341719350795083 181958335331012579026192625)
      ·
        refine ⟨136468751498259434269644469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181958335331012579026192625 136468751498259434269644469)
        ·
          refine ⟨12793945452961821962779169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 136468751498259434269644469 12793945452961821962779169)
          ·
            refine ⟨9595459089721366472084377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12793945452961821962779169 9595459089721366472084377)
            ·
              refine ⟨7196594317291024854063283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9595459089721366472084377 7196594317291024854063283)
              ·
                refine ⟨10794891475936537281094925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7196594317291024854063283 10794891475936537281094925)
                ·
                  refine ⟨4048084303476201480410597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10794891475936537281094925 4048084303476201480410597)
                  ·
                    refine ⟨759015806901787777576987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4048084303476201480410597 759015806901787777576987)
                    ·
                      rfl

theorem cell22_2217267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 4].length) (baseStart_2217267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217267 prefixEnd_2217267 := by exact prefixLift 2217267
  have htrace : WordTrace (prefixWord ++ tailWord_2217267) baseStart_2217267 baseEnd_2217267 := by
    simpa [prefixWord, tailWord_2217267, baseEnd_2217267] using wordTrace_append hprefix tailTrace_2217267
  have hstable : (prefixWord ++ tailWord_2217267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217267).length < 2 ^ (prefixWord ++ tailWord_2217267).sum := by decide
  have hdescent : baseEnd_2217267 < baseStart_2217267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217312 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 1, 6]
def baseStart_2217312 : Nat := 118140960795 + 2217312 * 2 ^ 59
def prefixEnd_2217312 : Nat := 4983230072969 + 3 ^ 40 * 2217312 * 2
def baseEnd_2217312 : Nat := 759031211321422660201849

theorem tailTrace_2217312 : CollatzResearch.WordTrace tailWord_2217312 prefixEnd_2217312 759031211321422660201849 := by
  unfold tailWord_2217312
  simp only [CollatzResearch.WordTrace]
  refine ⟨40436006271532392792959095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53914675028709857057278793 40436006271532392792959095)
  ·
    refine ⟨60654009407298589189438643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40436006271532392792959095 60654009407298589189438643)
    ·
      refine ⟨90981014110947883784157965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60654009407298589189438643 90981014110947883784157965)
      ·
        refine ⟨34117880291605456419059237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90981014110947883784157965 34117880291605456419059237)
        ·
          refine ⟨6397102554676023078573607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34117880291605456419059237 6397102554676023078573607)
          ·
            refine ⟨9595653832014034617860411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6397102554676023078573607 9595653832014034617860411)
            ·
              refine ⟨14393480748021051926790617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9595653832014034617860411 14393480748021051926790617)
              ·
                refine ⟨10795110561015788945092963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14393480748021051926790617 10795110561015788945092963)
                ·
                  refine ⟨16192665841523683417639445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10795110561015788945092963 16192665841523683417639445)
                  ·
                    refine ⟨759031211321422660201849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16192665841523683417639445 759031211321422660201849)
                    ·
                      rfl

theorem cell22_2217312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 1, 6].length) (baseStart_2217312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217312 prefixEnd_2217312 := by exact prefixLift 2217312
  have htrace : WordTrace (prefixWord ++ tailWord_2217312) baseStart_2217312 baseEnd_2217312 := by
    simpa [prefixWord, tailWord_2217312, baseEnd_2217312] using wordTrace_append hprefix tailTrace_2217312
  have hstable : (prefixWord ++ tailWord_2217312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217312).length < 2 ^ (prefixWord ++ tailWord_2217312).sum := by decide
  have hdescent : baseEnd_2217312 < baseStart_2217312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217333 : List Nat := [1, 3, 4, 1, 3, 2, 1, 3, 4]
def baseStart_2217333 : Nat := 118140960795 + 2217333 * 2 ^ 59
def prefixEnd_2217333 : Nat := 4983230072969 + 3 ^ 40 * 2217333 * 2
def baseEnd_2217333 : Nat := 253012800016861868475595

theorem tailTrace_2217333 : CollatzResearch.WordTrace tailWord_2217333 prefixEnd_2217333 253012800016861868475595 := by
  unfold tailWord_2217333
  simp only [CollatzResearch.WordTrace]
  refine ⟨80872778475988706172432653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53915185650659137448288435 80872778475988706172432653)
  ·
    refine ⟨30327291928495764814662245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80872778475988706172432653 30327291928495764814662245)
    ·
      refine ⟨5686367236592955902749171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30327291928495764814662245 5686367236592955902749171)
      ·
        refine ⟨8529550854889433854123757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5686367236592955902749171 8529550854889433854123757)
        ·
          refine ⟨3198581570583537695296409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8529550854889433854123757 3198581570583537695296409)
          ·
            refine ⟨2398936177937653271472307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3198581570583537695296409 2398936177937653271472307)
            ·
              refine ⟨3598404266906479907208461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2398936177937653271472307 3598404266906479907208461)
              ·
                refine ⟨1349401600089929965203173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3598404266906479907208461 1349401600089929965203173)
                ·
                  refine ⟨253012800016861868475595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1349401600089929965203173 253012800016861868475595)
                  ·
                    rfl

theorem cell22_2217333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 4].length) (baseStart_2217333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217333 prefixEnd_2217333 := by exact prefixLift 2217333
  have htrace : WordTrace (prefixWord ++ tailWord_2217333) baseStart_2217333 baseEnd_2217333 := by
    simpa [prefixWord, tailWord_2217333, baseEnd_2217333] using wordTrace_append hprefix tailTrace_2217333
  have hstable : (prefixWord ++ tailWord_2217333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217333).length < 2 ^ (prefixWord ++ tailWord_2217333).sum := by decide
  have hdescent : baseEnd_2217333 < baseStart_2217333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217346 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_2217346 : Nat := 118140960795 + 2217346 * 2 ^ 59
def prefixEnd_2217346 : Nat := 4983230072969 + 3 ^ 40 * 2217346 * 2
def baseEnd_2217346 : Nat := 759042850216257904851745

theorem tailTrace_2217346 : CollatzResearch.WordTrace tailWord_2217346 prefixEnd_2217346 759042850216257904851745 := by
  unfold tailWord_2217346
  simp only [CollatzResearch.WordTrace]
  refine ⟨20218313156235402348163973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53915501749961072928437261 20218313156235402348163973)
  ·
    refine ⟨3790933716794137940280745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20218313156235402348163973 3790933716794137940280745)
    ·
      refine ⟨2843200287595603455210559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3790933716794137940280745 2843200287595603455210559)
      ·
        refine ⟨4264800431393405182815839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2843200287595603455210559 4264800431393405182815839)
        ·
          refine ⟨6397200647090107774223759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4264800431393405182815839 6397200647090107774223759)
          ·
            refine ⟨9595800970635161661335639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6397200647090107774223759 9595800970635161661335639)
            ·
              refine ⟨14393701455952742492003459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9595800970635161661335639 14393701455952742492003459)
              ·
                refine ⟨21590552183929113738005189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14393701455952742492003459 21590552183929113738005189)
                ·
                  refine ⟨4048228534486708825875973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21590552183929113738005189 4048228534486708825875973)
                  ·
                    refine ⟨759042850216257904851745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4048228534486708825875973 759042850216257904851745)
                    ·
                      rfl

theorem cell22_2217346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_2217346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217346 prefixEnd_2217346 := by exact prefixLift 2217346
  have htrace : WordTrace (prefixWord ++ tailWord_2217346) baseStart_2217346 baseEnd_2217346 := by
    simpa [prefixWord, tailWord_2217346, baseEnd_2217346] using wordTrace_append hprefix tailTrace_2217346
  have hstable : (prefixWord ++ tailWord_2217346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217346).length < 2 ^ (prefixWord ++ tailWord_2217346).sum := by decide
  have hdescent : baseEnd_2217346 < baseStart_2217346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217417 : List Nat := [1, 2, 1, 1, 2, 1, 3, 5, 6]
def baseStart_2217417 : Nat := 118140960795 + 2217417 * 2 ^ 59
def prefixEnd_2217417 : Nat := 4983230072969 + 3 ^ 40 * 2217417 * 2
def baseEnd_2217417 : Nat := 253022384989079128775509

theorem tailTrace_2217417 : CollatzResearch.WordTrace tailWord_2217417 prefixEnd_2217417 253022384989079128775509 := by
  unfold tailWord_2217417
  simp only [CollatzResearch.WordTrace]
  refine ⟨80875842207684388518490505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53917228138456259012327003 80875842207684388518490505)
  ·
    refine ⟨60656881655763291388867879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80875842207684388518490505 60656881655763291388867879)
    ·
      refine ⟨90985322483644937083301819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60656881655763291388867879 90985322483644937083301819)
      ·
        refine ⟨136477983725467405624952729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90985322483644937083301819 136477983725467405624952729)
        ·
          refine ⟨102358487794100554218714547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136477983725467405624952729 102358487794100554218714547)
          ·
            refine ⟨153537731691150831328071821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102358487794100554218714547 153537731691150831328071821)
            ·
              refine ⟨57576649384181561748026933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153537731691150831328071821 57576649384181561748026933)
              ·
                refine ⟨5397810879767021413877525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57576649384181561748026933 5397810879767021413877525)
                ·
                  refine ⟨253022384989079128775509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5397810879767021413877525 253022384989079128775509)
                  ·
                    rfl

theorem cell22_2217417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 6].length) (baseStart_2217417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217417 prefixEnd_2217417 := by exact prefixLift 2217417
  have htrace : WordTrace (prefixWord ++ tailWord_2217417) baseStart_2217417 baseEnd_2217417 := by
    simpa [prefixWord, tailWord_2217417, baseEnd_2217417] using wordTrace_append hprefix tailTrace_2217417
  have hstable : (prefixWord ++ tailWord_2217417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217417).length < 2 ^ (prefixWord ++ tailWord_2217417).sum := by decide
  have hdescent : baseEnd_2217417 < baseStart_2217417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217434 : List Nat := [3, 1, 1, 2, 3, 3, 1, 2, 6]
def baseStart_2217434 : Nat := 118140960795 + 2217434 * 2 ^ 59
def prefixEnd_2217434 : Nat := 4983230072969 + 3 ^ 40 * 2217434 * 2
def baseEnd_2217434 : Nat := 253024324804885002883825

theorem tailTrace_2217434 : CollatzResearch.WordTrace tailWord_2217434 prefixEnd_2217434 253024324804885002883825 := by
  unfold tailWord_2217434
  simp only [CollatzResearch.WordTrace]
  refine ⟨20219115562155700105464839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53917641499081866947906237 20219115562155700105464839)
  ·
    refine ⟨30328673343233550158197259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20219115562155700105464839 30328673343233550158197259)
    ·
      refine ⟨45493010014850325237295889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30328673343233550158197259 45493010014850325237295889)
      ·
        refine ⟨34119757511137743927971917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45493010014850325237295889 34119757511137743927971917)
        ·
          refine ⟨12794909066676653972989469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34119757511137743927971917 12794909066676653972989469)
          ·
            refine ⟨4798090900003745239871051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12794909066676653972989469 4798090900003745239871051)
            ·
              refine ⟨7197136350005617859806577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4798090900003745239871051 7197136350005617859806577)
              ·
                refine ⟨5397852262504213394854933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7197136350005617859806577 5397852262504213394854933)
                ·
                  refine ⟨253024324804885002883825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5397852262504213394854933 253024324804885002883825)
                  ·
                    rfl

theorem cell22_2217434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_2217434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217434 prefixEnd_2217434 := by exact prefixLift 2217434
  have htrace : WordTrace (prefixWord ++ tailWord_2217434) baseStart_2217434 baseEnd_2217434 := by
    simpa [prefixWord, tailWord_2217434, baseEnd_2217434] using wordTrace_append hprefix tailTrace_2217434
  have hstable : (prefixWord ++ tailWord_2217434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217434).length < 2 ^ (prefixWord ++ tailWord_2217434).sum := by decide
  have hdescent : baseEnd_2217434 < baseStart_2217434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217453 : List Nat := [1, 5, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_2217453 : Nat := 118140960795 + 2217453 * 2 ^ 59
def prefixEnd_2217453 : Nat := 4983230072969 + 3 ^ 40 * 2217453 * 2
def baseEnd_2217453 : Nat := 759079478502945292426417

theorem tailTrace_2217453 : CollatzResearch.WordTrace tailWord_2217453 prefixEnd_2217453 759079478502945292426417 := by
  unfold tailWord_2217453
  simp only [CollatzResearch.WordTrace]
  refine ⟨80877155235553966666801013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53918103490369311111200675 80877155235553966666801013)
  ·
    refine ⟨7582233303333184375012595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80877155235553966666801013 7582233303333184375012595)
    ·
      refine ⟨11373349954999776562518893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7582233303333184375012595 11373349954999776562518893)
      ·
        refine ⟨4265006233124916210944585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11373349954999776562518893 4265006233124916210944585)
        ·
          refine ⟨3198754674843687158208439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4265006233124916210944585 3198754674843687158208439)
          ·
            refine ⟨4798132012265530737312659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3198754674843687158208439 4798132012265530737312659)
            ·
              refine ⟨7197198018398296105968989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4798132012265530737312659 7197198018398296105968989)
              ·
                refine ⟨2698949256899361039738371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7197198018398296105968989 2698949256899361039738371)
                ·
                  refine ⟨4048423885349041559607557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2698949256899361039738371 4048423885349041559607557)
                  ·
                    refine ⟨759079478502945292426417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4048423885349041559607557 759079478502945292426417)
                    ·
                      rfl

theorem cell22_2217453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_2217453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217453 prefixEnd_2217453 := by exact prefixLift 2217453
  have htrace : WordTrace (prefixWord ++ tailWord_2217453) baseStart_2217453 baseEnd_2217453 := by
    simpa [prefixWord, tailWord_2217453, baseEnd_2217453] using wordTrace_append hprefix tailTrace_2217453
  have hstable : (prefixWord ++ tailWord_2217453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217453).length < 2 ^ (prefixWord ++ tailWord_2217453).sum := by decide
  have hdescent : baseEnd_2217453 < baseStart_2217453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217483 : List Nat := [1, 1, 1, 1, 9, 1, 1, 1, 1, 5]
def baseStart_2217483 : Nat := 118140960795 + 2217483 * 2 ^ 59
def prefixEnd_2217483 : Nat := 4983230072969 + 3 ^ 40 * 2217483 * 2
def baseEnd_2217483 : Nat := 759089748116035214176325

theorem tailTrace_2217483 : CollatzResearch.WordTrace tailWord_2217483 prefixEnd_2217483 759089748116035214176325 := by
  unfold tailWord_2217483
  simp only [CollatzResearch.WordTrace]
  refine ⟨80878249425445281790393103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53918832950296854526928735 80878249425445281790393103)
  ·
    refine ⟨121317374138167922685589655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80878249425445281790393103 121317374138167922685589655)
    ·
      refine ⟨181976061207251884028384483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121317374138167922685589655 181976061207251884028384483)
      ·
        refine ⟨272964091810877826042576725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181976061207251884028384483 272964091810877826042576725)
        ·
          refine ⟨1599398975454362261968223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 272964091810877826042576725 1599398975454362261968223)
          ·
            refine ⟨2399098463181543392952335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1599398975454362261968223 2399098463181543392952335)
            ·
              refine ⟨3598647694772315089428503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2399098463181543392952335 3598647694772315089428503)
              ·
                refine ⟨5397971542158472634142755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3598647694772315089428503 5397971542158472634142755)
                ·
                  refine ⟨8096957313237708951214133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5397971542158472634142755 8096957313237708951214133)
                  ·
                    refine ⟨759089748116035214176325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8096957313237708951214133 759089748116035214176325)
                    ·
                      rfl

theorem cell22_2217483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 1, 5].length) (baseStart_2217483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217483 prefixEnd_2217483 := by exact prefixLift 2217483
  have htrace : WordTrace (prefixWord ++ tailWord_2217483) baseStart_2217483 baseEnd_2217483 := by
    simpa [prefixWord, tailWord_2217483, baseEnd_2217483] using wordTrace_append hprefix tailTrace_2217483
  have hstable : (prefixWord ++ tailWord_2217483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217483).length < 2 ^ (prefixWord ++ tailWord_2217483).sum := by decide
  have hdescent : baseEnd_2217483 < baseStart_2217483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217528 : List Nat := [2, 1, 2, 1, 4, 4, 1, 1, 3, 3]
def baseStart_2217528 : Nat := 118140960795 + 2217528 * 2 ^ 59
def prefixEnd_2217528 : Nat := 4983230072969 + 3 ^ 40 * 2217528 * 2
def baseEnd_2217528 : Nat := 759105152535670096801187

theorem tailTrace_2217528 : CollatzResearch.WordTrace tailWord_2217528 prefixEnd_2217528 759105152535670096801187 := by
  unfold tailWord_2217528
  simp only [CollatzResearch.WordTrace]
  refine ⟨40439945355141127237890619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53919927140188169650520825 40439945355141127237890619)
  ·
    refine ⟨60659918032711690856835929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40439945355141127237890619 60659918032711690856835929)
    ·
      refine ⟨45494938524533768142626947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60659918032711690856835929 45494938524533768142626947)
      ·
        refine ⟨68242407786800652213940421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45494938524533768142626947 68242407786800652213940421)
        ·
          refine ⟨12795451460025122290113829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68242407786800652213940421 12795451460025122290113829)
          ·
            refine ⟨2399147148754710429396343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12795451460025122290113829 2399147148754710429396343)
            ·
              refine ⟨3598720723132065644094515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2399147148754710429396343 3598720723132065644094515)
              ·
                refine ⟨5398081084698098466141773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3598720723132065644094515 5398081084698098466141773)
                ·
                  refine ⟨2024280406761786924803165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5398081084698098466141773 2024280406761786924803165)
                  ·
                    refine ⟨759105152535670096801187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2024280406761786924803165 759105152535670096801187)
                    ·
                      rfl

theorem cell22_2217528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 3, 3].length) (baseStart_2217528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217528 prefixEnd_2217528 := by exact prefixLift 2217528
  have htrace : WordTrace (prefixWord ++ tailWord_2217528) baseStart_2217528 baseEnd_2217528 := by
    simpa [prefixWord, tailWord_2217528, baseEnd_2217528] using wordTrace_append hprefix tailTrace_2217528
  have hstable : (prefixWord ++ tailWord_2217528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217528).length < 2 ^ (prefixWord ++ tailWord_2217528).sum := by decide
  have hdescent : baseEnd_2217528 < baseStart_2217528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217601 : List Nat := [1, 2, 4, 2, 1, 2, 1, 3, 1, 5]
def baseStart_2217601 : Nat := 118140960795 + 2217601 * 2 ^ 59
def prefixEnd_2217601 : Nat := 4983230072969 + 3 ^ 40 * 2217601 * 2
def baseEnd_2217601 : Nat := 759130141927522239725963

theorem tailTrace_2217601 : CollatzResearch.WordTrace tailWord_2217601 prefixEnd_2217601 759130141927522239725963 := by
  unfold tailWord_2217601
  simp only [CollatzResearch.WordTrace]
  refine ⟨80882553239017787943188657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53921702159345191962125771 80882553239017787943188657)
  ·
    refine ⟨60661914929263340957391493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80882553239017787943188657 60661914929263340957391493)
    ·
      refine ⟨11374109049236876429510905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60661914929263340957391493 11374109049236876429510905)
      ·
        refine ⟨8530581786927657322133179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11374109049236876429510905 8530581786927657322133179)
        ·
          refine ⟨12795872680391485983199769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8530581786927657322133179 12795872680391485983199769)
          ·
            refine ⟨9596904510293614487399827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12795872680391485983199769 9596904510293614487399827)
            ·
              refine ⟨14395356765440421731099741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9596904510293614487399827 14395356765440421731099741)
              ·
                refine ⟨5398258787040158149162403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14395356765440421731099741 5398258787040158149162403)
                ·
                  refine ⟨8097388180560237223743605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5398258787040158149162403 8097388180560237223743605)
                  ·
                    refine ⟨759130141927522239725963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8097388180560237223743605 759130141927522239725963)
                    ·
                      rfl

theorem cell22_2217601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_2217601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217601 prefixEnd_2217601 := by exact prefixLift 2217601
  have htrace : WordTrace (prefixWord ++ tailWord_2217601) baseStart_2217601 baseEnd_2217601 := by
    simpa [prefixWord, tailWord_2217601, baseEnd_2217601] using wordTrace_append hprefix tailTrace_2217601
  have hstable : (prefixWord ++ tailWord_2217601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217601).length < 2 ^ (prefixWord ++ tailWord_2217601).sum := by decide
  have hdescent : baseEnd_2217601 < baseStart_2217601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217697 : List Nat := [1, 2, 3, 1, 6, 1, 1, 1, 3, 3]
def baseStart_2217697 : Nat := 118140960795 + 2217697 * 2 ^ 59
def prefixEnd_2217697 : Nat := 4983230072969 + 3 ^ 40 * 2217697 * 2
def baseEnd_2217697 : Nat := 759163004689409989325669

theorem tailTrace_2217697 : CollatzResearch.WordTrace tailWord_2217697 prefixEnd_2217697 759163004689409989325669 := by
  unfold tailWord_2217697
  simp only [CollatzResearch.WordTrace]
  refine ⟨80886054646669996338683345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53924036431113330892455563 80886054646669996338683345)
  ·
    refine ⟨60664540985002497254012509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80886054646669996338683345 60664540985002497254012509)
    ·
      refine ⟨22749202869375936470254691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60664540985002497254012509 22749202869375936470254691)
      ·
        refine ⟨34123804304063904705382037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22749202869375936470254691 34123804304063904705382037)
        ·
          refine ⟨1599553326752995533064783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34123804304063904705382037 1599553326752995533064783)
          ·
            refine ⟨2399329990129493299597175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1599553326752995533064783 2399329990129493299597175)
            ·
              refine ⟨3598994985194239949395763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2399329990129493299597175 3598994985194239949395763)
              ·
                refine ⟨5398492477791359924093645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3598994985194239949395763 5398492477791359924093645)
                ·
                  refine ⟨2024434679171759971535117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5398492477791359924093645 2024434679171759971535117)
                  ·
                    refine ⟨759163004689409989325669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2024434679171759971535117 759163004689409989325669)
                    ·
                      rfl

theorem cell22_2217697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_2217697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217697 prefixEnd_2217697 := by exact prefixLift 2217697
  have htrace : WordTrace (prefixWord ++ tailWord_2217697) baseStart_2217697 baseEnd_2217697 := by
    simpa [prefixWord, tailWord_2217697, baseEnd_2217697] using wordTrace_append hprefix tailTrace_2217697
  have hstable : (prefixWord ++ tailWord_2217697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217697).length < 2 ^ (prefixWord ++ tailWord_2217697).sum := by decide
  have hdescent : baseEnd_2217697 < baseStart_2217697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217785 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 1, 6]
def baseStart_2217785 : Nat := 118140960795 + 2217785 * 2 ^ 59
def prefixEnd_2217785 : Nat := 4983230072969 + 3 ^ 40 * 2217785 * 2
def baseEnd_2217785 : Nat := 759193128887807093125399

theorem tailTrace_2217785 : CollatzResearch.WordTrace tailWord_2217785 prefixEnd_2217785 759193128887807093125399 := by
  unfold tailWord_2217785
  simp only [CollatzResearch.WordTrace]
  refine ⟨80889264270351187367886809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53926176180234124911924539 80889264270351187367886809)
  ·
    refine ⟨60666948202763390525915107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80889264270351187367886809 60666948202763390525915107)
    ·
      refine ⟨91000422304145085788872661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60666948202763390525915107 91000422304145085788872661)
      ·
        refine ⟨2132822397753400448176703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 91000422304145085788872661 2132822397753400448176703)
        ·
          refine ⟨3199233596630100672265055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2132822397753400448176703 3199233596630100672265055)
          ·
            refine ⟨4798850394945151008397583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3199233596630100672265055 4798850394945151008397583)
            ·
              refine ⟨7198275592417726512596375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4798850394945151008397583 7198275592417726512596375)
              ·
                refine ⟨10797413388626589768894563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7198275592417726512596375 10797413388626589768894563)
                ·
                  refine ⟨16196120082939884653341845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10797413388626589768894563 16196120082939884653341845)
                  ·
                    refine ⟨759193128887807093125399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16196120082939884653341845 759193128887807093125399)
                    ·
                      rfl

theorem cell22_2217785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 6].length) (baseStart_2217785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217785 prefixEnd_2217785 := by exact prefixLift 2217785
  have htrace : WordTrace (prefixWord ++ tailWord_2217785) baseStart_2217785 baseEnd_2217785 := by
    simpa [prefixWord, tailWord_2217785, baseEnd_2217785] using wordTrace_append hprefix tailTrace_2217785
  have hstable : (prefixWord ++ tailWord_2217785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217785).length < 2 ^ (prefixWord ++ tailWord_2217785).sum := by decide
  have hdescent : baseEnd_2217785 < baseStart_2217785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217804 : List Nat := [2, 2, 1, 3, 5, 1, 1, 2, 2, 3]
def baseStart_2217804 : Nat := 118140960795 + 2217804 * 2 ^ 59
def prefixEnd_2217804 : Nat := 4983230072969 + 3 ^ 40 * 2217804 * 2
def baseEnd_2217804 : Nat := 759199632976097376900341

theorem tailTrace_2217804 : CollatzResearch.WordTrace tailWord_2217804 prefixEnd_2217804 759199632976097376900341 := by
  unfold tailWord_2217804
  simp only [CollatzResearch.WordTrace]
  refine ⟨40444978628641176806414233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53926638171521569075218977 40444978628641176806414233)
  ·
    refine ⟨30333733971480882604810675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40444978628641176806414233 30333733971480882604810675)
    ·
      refine ⟨45500600957221323907216013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30333733971480882604810675 45500600957221323907216013)
      ·
        refine ⟨17062725358957996465206005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45500600957221323907216013 17062725358957996465206005)
        ·
          refine ⟨1599630502402312168613063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17062725358957996465206005 1599630502402312168613063)
          ·
            refine ⟨2399445753603468252919595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1599630502402312168613063 2399445753603468252919595)
            ·
              refine ⟨3599168630405202379379393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2399445753603468252919595 3599168630405202379379393)
              ·
                refine ⟨2699376472803901784534545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3599168630405202379379393 2699376472803901784534545)
                ·
                  refine ⟨2024532354602926338400909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2699376472803901784534545 2024532354602926338400909)
                  ·
                    refine ⟨759199632976097376900341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2024532354602926338400909 759199632976097376900341)
                    ·
                      rfl

theorem cell22_2217804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 2, 3].length) (baseStart_2217804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217804 prefixEnd_2217804 := by exact prefixLift 2217804
  have htrace : WordTrace (prefixWord ++ tailWord_2217804) baseStart_2217804 baseEnd_2217804 := by
    simpa [prefixWord, tailWord_2217804, baseEnd_2217804] using wordTrace_append hprefix tailTrace_2217804
  have hstable : (prefixWord ++ tailWord_2217804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217804).length < 2 ^ (prefixWord ++ tailWord_2217804).sum := by decide
  have hdescent : baseEnd_2217804 < baseStart_2217804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217834 : List Nat := [3, 1, 3, 4, 2, 1, 2, 6]
def baseStart_2217834 : Nat := 118140960795 + 2217834 * 2 ^ 59
def prefixEnd_2217834 : Nat := 4983230072969 + 3 ^ 40 * 2217834 * 2
def baseEnd_2217834 : Nat := 84356655843243033183361

theorem tailTrace_2217834 : CollatzResearch.WordTrace tailWord_2217834 prefixEnd_2217834 84356655843243033183361 := by
  unfold tailWord_2217834
  simp only [CollatzResearch.WordTrace]
  refine ⟨20222762861793417184105139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53927367631449112490947037 20222762861793417184105139)
  ·
    refine ⟨30334144292690125776157709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20222762861793417184105139 30334144292690125776157709)
    ·
      refine ⟨11375304109758797166059141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30334144292690125776157709 11375304109758797166059141)
      ·
        refine ⟨2132869520579774468636089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11375304109758797166059141 2132869520579774468636089)
        ·
          refine ⟨1599652140434830851477067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2132869520579774468636089 1599652140434830851477067)
          ·
            refine ⟨2399478210652246277215601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1599652140434830851477067 2399478210652246277215601)
            ·
              refine ⟨1799608657989184707911701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2399478210652246277215601 1799608657989184707911701)
              ·
                refine ⟨84356655843243033183361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1799608657989184707911701 84356655843243033183361)
                ·
                  rfl

theorem cell22_2217834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 6].length) (baseStart_2217834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217834 prefixEnd_2217834 := by exact prefixLift 2217834
  have htrace : WordTrace (prefixWord ++ tailWord_2217834) baseStart_2217834 baseEnd_2217834 := by
    simpa [prefixWord, tailWord_2217834, baseEnd_2217834] using wordTrace_append hprefix tailTrace_2217834
  have hstable : (prefixWord ++ tailWord_2217834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217834).length < 2 ^ (prefixWord ++ tailWord_2217834).sum := by decide
  have hdescent : baseEnd_2217834 < baseStart_2217834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217866 : List Nat := [3, 1, 2, 4, 2, 1, 3, 2, 1, 3]
def baseStart_2217866 : Nat := 118140960795 + 2217866 * 2 ^ 59
def prefixEnd_2217866 : Nat := 4983230072969 + 3 ^ 40 * 2217866 * 2
def baseEnd_2217866 : Nat := 759220856843149881850151

theorem tailTrace_2217866 : CollatzResearch.WordTrace tailWord_2217866 prefixEnd_2217866 759220856843149881850151 := by
  unfold tailWord_2217866
  simp only [CollatzResearch.WordTrace]
  refine ⟨20223054645764434550396363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53928145722038492134390301 20223054645764434550396363)
  ·
    refine ⟨30334581968646651825594545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20223054645764434550396363 30334581968646651825594545)
    ·
      refine ⟨22750936476484988869195909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30334581968646651825594545 22750936476484988869195909)
      ·
        refine ⟨4265800589340935412974233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22750936476484988869195909 4265800589340935412974233)
        ·
          refine ⟨3199350442005701559730675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4265800589340935412974233 3199350442005701559730675)
          ·
            refine ⟨4799025663008552339596013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3199350442005701559730675 4799025663008552339596013)
            ·
              refine ⟨1799634623628207127348505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4799025663008552339596013 1799634623628207127348505)
              ·
                refine ⟨1349725967721155345511379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1799634623628207127348505 1349725967721155345511379)
                ·
                  refine ⟨2024588951581733018267069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1349725967721155345511379 2024588951581733018267069)
                  ·
                    refine ⟨759220856843149881850151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2024588951581733018267069 759220856843149881850151)
                    ·
                      rfl

theorem cell22_2217866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_2217866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217866 prefixEnd_2217866 := by exact prefixLift 2217866
  have htrace : WordTrace (prefixWord ++ tailWord_2217866) baseStart_2217866 baseEnd_2217866 := by
    simpa [prefixWord, tailWord_2217866, baseEnd_2217866] using wordTrace_append hprefix tailTrace_2217866
  have hstable : (prefixWord ++ tailWord_2217866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217866).length < 2 ^ (prefixWord ++ tailWord_2217866).sum := by decide
  have hdescent : baseEnd_2217866 < baseStart_2217866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217873 : List Nat := [1, 2, 2, 1, 1, 1, 7, 1, 6]
def baseStart_2217873 : Nat := 118140960795 + 2217873 * 2 ^ 59
def prefixEnd_2217873 : Nat := 4983230072969 + 3 ^ 40 * 2217873 * 2
def baseEnd_2217873 : Nat := 253074417695401398975043

theorem tailTrace_2217873 : CollatzResearch.WordTrace tailWord_2217873 prefixEnd_2217873 253074417695401398975043 := by
  unfold tailWord_2217873
  simp only [CollatzResearch.WordTrace]
  refine ⟨80892473894032378397090273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53928315929354918931393515 80892473894032378397090273)
  ·
    refine ⟨60669355420524283797817705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80892473894032378397090273 60669355420524283797817705)
    ·
      refine ⟨45502016565393212848363279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60669355420524283797817705 45502016565393212848363279)
      ·
        refine ⟨68253024848089819272544919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45502016565393212848363279 68253024848089819272544919)
        ·
          refine ⟨102379537272134728908817379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68253024848089819272544919 102379537272134728908817379)
          ·
            refine ⟨153569305908202093363226069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102379537272134728908817379 153569305908202093363226069)
            ·
              refine ⟨3599280607223486563200611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 153569305908202093363226069 3599280607223486563200611)
              ·
                refine ⟨5398920910835229844800917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3599280607223486563200611 5398920910835229844800917)
                ·
                  refine ⟨253074417695401398975043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5398920910835229844800917 253074417695401398975043)
                  ·
                    rfl

theorem cell22_2217873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 6].length) (baseStart_2217873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217873 prefixEnd_2217873 := by exact prefixLift 2217873
  have htrace : WordTrace (prefixWord ++ tailWord_2217873) baseStart_2217873 baseEnd_2217873 := by
    simpa [prefixWord, tailWord_2217873, baseEnd_2217873] using wordTrace_append hprefix tailTrace_2217873
  have hstable : (prefixWord ++ tailWord_2217873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217873).length < 2 ^ (prefixWord ++ tailWord_2217873).sum := by decide
  have hdescent : baseEnd_2217873 < baseStart_2217873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217888 : List Nat := [2, 1, 1, 4, 1, 1, 1, 5, 1, 5]
def baseStart_2217888 : Nat := 118140960795 + 2217888 * 2 ^ 59
def prefixEnd_2217888 : Nat := 4983230072969 + 3 ^ 40 * 2217888 * 2
def baseEnd_2217888 : Nat := 759228387892749157800083

theorem tailTrace_2217888 : CollatzResearch.WordTrace tailWord_2217888 prefixEnd_2217888 759228387892749157800083 := by
  unfold tailWord_2217888
  simp only [CollatzResearch.WordTrace]
  refine ⟨40446510494489017979443159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53928680659318690639257545 40446510494489017979443159)
  ·
    refine ⟨60669765741733526969164739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40446510494489017979443159 60669765741733526969164739)
    ·
      refine ⟨91004648612600290453747109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60669765741733526969164739 91004648612600290453747109)
      ·
        refine ⟨17063371614862554460077583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91004648612600290453747109 17063371614862554460077583)
        ·
          refine ⟨25595057422293831690116375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17063371614862554460077583 25595057422293831690116375)
          ·
            refine ⟨38392586133440747535174563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25595057422293831690116375 38392586133440747535174563)
            ·
              refine ⟨57588879200161121302761845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38392586133440747535174563 57588879200161121302761845)
              ·
                refine ⟨5398957425015105122133923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57588879200161121302761845 5398957425015105122133923)
                ·
                  refine ⟨8098436137522657683200885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5398957425015105122133923 8098436137522657683200885)
                  ·
                    refine ⟨759228387892749157800083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8098436137522657683200885 759228387892749157800083)
                    ·
                      rfl

theorem cell22_2217888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 1, 5].length) (baseStart_2217888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217888 prefixEnd_2217888 := by exact prefixLift 2217888
  have htrace : WordTrace (prefixWord ++ tailWord_2217888) baseStart_2217888 baseEnd_2217888 := by
    simpa [prefixWord, tailWord_2217888, baseEnd_2217888] using wordTrace_append hprefix tailTrace_2217888
  have hstable : (prefixWord ++ tailWord_2217888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217888).length < 2 ^ (prefixWord ++ tailWord_2217888).sum := by decide
  have hdescent : baseEnd_2217888 < baseStart_2217888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217892 : List Nat := [2, 3, 1, 2, 1, 5, 1, 2, 1, 4]
def baseStart_2217892 : Nat := 118140960795 + 2217892 * 2 ^ 59
def prefixEnd_2217892 : Nat := 4983230072969 + 3 ^ 40 * 2217892 * 2
def baseEnd_2217892 : Nat := 759229757174494480700071

theorem tailTrace_2217892 : CollatzResearch.WordTrace tailWord_2217892 prefixEnd_2217892 759229757174494480700071 := by
  unfold tailWord_2217892
  simp only [CollatzResearch.WordTrace]
  refine ⟨40446583440481772321015965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53928777920642363094687953 40446583440481772321015965)
  ·
    refine ⟨15167468790180664620380987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40446583440481772321015965 15167468790180664620380987)
    ·
      refine ⟨22751203185270996930571481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15167468790180664620380987 22751203185270996930571481)
      ·
        refine ⟨17063402388953247697928611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22751203185270996930571481 17063402388953247697928611)
        ·
          refine ⟨25595103583429871546892917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17063402388953247697928611 25595103583429871546892917)
          ·
            refine ⟨2399540960946550457521211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25595103583429871546892917 2399540960946550457521211)
            ·
              refine ⟨3599311441419825686281817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2399540960946550457521211 3599311441419825686281817)
              ·
                refine ⟨2699483581064869264711363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3599311441419825686281817 2699483581064869264711363)
                ·
                  refine ⟨4049225371597303897067045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2699483581064869264711363 4049225371597303897067045)
                  ·
                    refine ⟨759229757174494480700071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4049225371597303897067045 759229757174494480700071)
                    ·
                      rfl

theorem cell22_2217892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_2217892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217892 prefixEnd_2217892 := by exact prefixLift 2217892
  have htrace : WordTrace (prefixWord ++ tailWord_2217892) baseStart_2217892 baseEnd_2217892 := by
    simpa [prefixWord, tailWord_2217892, baseEnd_2217892] using wordTrace_append hprefix tailTrace_2217892
  have hstable : (prefixWord ++ tailWord_2217892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217892).length < 2 ^ (prefixWord ++ tailWord_2217892).sum := by decide
  have hdescent : baseEnd_2217892 < baseStart_2217892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217905 : List Nat := [1, 2, 2, 4, 2, 2, 1, 2, 1, 5]
def baseStart_2217905 : Nat := 118140960795 + 2217905 * 2 ^ 59
def prefixEnd_2217905 : Nat := 4983230072969 + 3 ^ 40 * 2217905 * 2
def baseEnd_2217905 : Nat := 759234207340166780125031

theorem tailTrace_2217905 : CollatzResearch.WordTrace tailWord_2217905 prefixEnd_2217905 759234207340166780125031 := by
  unfold tailWord_2217905
  simp only [CollatzResearch.WordTrace]
  refine ⟨80893641029916447862255169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53929094019944298574836779 80893641029916447862255169)
  ·
    refine ⟨60670230772437335896691377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80893641029916447862255169 60670230772437335896691377)
    ·
      refine ⟨45502673079328001922518533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60670230772437335896691377 45502673079328001922518533)
      ·
        refine ⟨8531751202374000360472225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45502673079328001922518533 8531751202374000360472225)
        ·
          refine ⟨6398813401780500270354169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8531751202374000360472225 6398813401780500270354169)
          ·
            refine ⟨4799110051335375202765627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6398813401780500270354169 4799110051335375202765627)
            ·
              refine ⟨7198665077003062804148441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4799110051335375202765627 7198665077003062804148441)
              ·
                refine ⟨5398998807752297103111331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7198665077003062804148441 5398998807752297103111331)
                ·
                  refine ⟨8098498211628445654666997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5398998807752297103111331 8098498211628445654666997)
                  ·
                    refine ⟨759234207340166780125031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8098498211628445654666997 759234207340166780125031)
                    ·
                      rfl

theorem cell22_2217905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_2217905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217905 prefixEnd_2217905 := by exact prefixLift 2217905
  have htrace : WordTrace (prefixWord ++ tailWord_2217905) baseStart_2217905 baseEnd_2217905 := by
    simpa [prefixWord, tailWord_2217905, baseEnd_2217905] using wordTrace_append hprefix tailTrace_2217905
  have hstable : (prefixWord ++ tailWord_2217905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217905).length < 2 ^ (prefixWord ++ tailWord_2217905).sum := by decide
  have hdescent : baseEnd_2217905 < baseStart_2217905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217918 : List Nat := [4, 2, 1, 1, 1, 13]
def baseStart_2217918 : Nat := 118140960795 + 2217918 * 2 ^ 59
def prefixEnd_2217918 : Nat := 4983230072969 + 3 ^ 40 * 2217918 * 2
def baseEnd_2217918 : Nat := 9373316759331346661111

theorem tailTrace_2217918 : CollatzResearch.WordTrace tailWord_2217918 prefixEnd_2217918 9373316759331346661111 := by
  unfold tailWord_2217918
  simp only [CollatzResearch.WordTrace]
  refine ⟨10111764397358668885309801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53929410119246234054985605 10111764397358668885309801)
  ·
    refine ⟨7583823298019001663982351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10111764397358668885309801 7583823298019001663982351)
    ·
      refine ⟨11375734947028502495973527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7583823298019001663982351 11375734947028502495973527)
      ·
        refine ⟨17063602420542753743960291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11375734947028502495973527 17063602420542753743960291)
        ·
          refine ⟨25595403630814130615940437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17063602420542753743960291 25595403630814130615940437)
          ·
            refine ⟨9373316759331346661111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 25595403630814130615940437 9373316759331346661111)
            ·
              rfl

theorem cell22_2217918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 13].length) (baseStart_2217918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217918 prefixEnd_2217918 := by exact prefixLift 2217918
  have htrace : WordTrace (prefixWord ++ tailWord_2217918) baseStart_2217918 baseEnd_2217918 := by
    simpa [prefixWord, tailWord_2217918, baseEnd_2217918] using wordTrace_append hprefix tailTrace_2217918
  have hstable : (prefixWord ++ tailWord_2217918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217918).length < 2 ^ (prefixWord ++ tailWord_2217918).sum := by decide
  have hdescent : baseEnd_2217918 < baseStart_2217918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217990 : List Nat := [6, 2, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_2217990 : Nat := 118140960795 + 2217990 * 2 ^ 59
def prefixEnd_2217990 : Nat := 4983230072969 + 3 ^ 40 * 2217990 * 2
def baseEnd_2217990 : Nat := 759263304577254891749771

theorem tailTrace_2217990 : CollatzResearch.WordTrace tailWord_2217990 prefixEnd_2217990 759263304577254891749771 := by
  unfold tailWord_2217990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2528023163581515855596857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53931160823072338252732949 2528023163581515855596857)
  ·
    refine ⟨1896017372686136891697643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2528023163581515855596857 1896017372686136891697643)
    ·
      refine ⟨2844026059029205337546465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1896017372686136891697643 2844026059029205337546465)
      ·
        refine ⟨2133019544271904003159849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2844026059029205337546465 2133019544271904003159849)
        ·
          refine ⟨1599764658203928002369887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2133019544271904003159849 1599764658203928002369887)
          ·
            refine ⟨2399646987305892003554831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1599764658203928002369887 2399646987305892003554831)
            ·
              refine ⟨3599470480958838005332247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2399646987305892003554831 3599470480958838005332247)
              ·
                refine ⟨5399205721438257007998371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3599470480958838005332247 5399205721438257007998371)
                ·
                  refine ⟨8098808582157385511997557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5399205721438257007998371 8098808582157385511997557)
                  ·
                    refine ⟨759263304577254891749771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8098808582157385511997557 759263304577254891749771)
                    ·
                      rfl

theorem cell22_2217990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_2217990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2217990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2217990 prefixEnd_2217990 := by exact prefixLift 2217990
  have htrace : WordTrace (prefixWord ++ tailWord_2217990) baseStart_2217990 baseEnd_2217990 := by
    simpa [prefixWord, tailWord_2217990, baseEnd_2217990] using wordTrace_append hprefix tailTrace_2217990
  have hstable : (prefixWord ++ tailWord_2217990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217990).length < 2 ^ (prefixWord ++ tailWord_2217990).sum := by decide
  have hdescent : baseEnd_2217990 < baseStart_2217990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218055 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 4, 4]
def baseStart_2218055 : Nat := 118140960795 + 2218055 * 2 ^ 59
def prefixEnd_2218055 : Nat := 4983230072969 + 3 ^ 40 * 2218055 * 2
def baseEnd_2218055 : Nat := 759285555405616388874571

theorem tailTrace_2218055 : CollatzResearch.WordTrace tailWord_2218055 prefixEnd_2218055 759285555405616388874571 := by
  unfold tailWord_2218055
  simp only [CollatzResearch.WordTrace]
  refine ⟨80899111979373023480215619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53932741319582015653477079 80899111979373023480215619)
  ·
    refine ⟨121348667969059535220323429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80899111979373023480215619 121348667969059535220323429)
    ·
      refine ⟨22752875244198662853810643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121348667969059535220323429 22752875244198662853810643)
      ·
        refine ⟨34129312866297994280715965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22752875244198662853810643 34129312866297994280715965)
        ·
          refine ⟨12798492324861747855268487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34129312866297994280715965 12798492324861747855268487)
          ·
            refine ⟨19197738487292621782902731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12798492324861747855268487 19197738487292621782902731)
            ·
              refine ⟨28796607730938932674354097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19197738487292621782902731 28796607730938932674354097)
              ·
                refine ⟨21597455798204199505765573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28796607730938932674354097 21597455798204199505765573)
                ·
                  refine ⟨4049522962163287407331045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21597455798204199505765573 4049522962163287407331045)
                  ·
                    refine ⟨759285555405616388874571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4049522962163287407331045 759285555405616388874571)
                    ·
                      rfl

theorem cell22_2218055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_2218055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2218055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2218055 prefixEnd_2218055 := by exact prefixLift 2218055
  have htrace : WordTrace (prefixWord ++ tailWord_2218055) baseStart_2218055 baseEnd_2218055 := by
    simpa [prefixWord, tailWord_2218055, baseEnd_2218055] using wordTrace_append hprefix tailTrace_2218055
  have hstable : (prefixWord ++ tailWord_2218055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218055).length < 2 ^ (prefixWord ++ tailWord_2218055).sum := by decide
  have hdescent : baseEnd_2218055 < baseStart_2218055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218057 : List Nat := [1, 2, 1, 1, 2, 2, 5, 3, 2, 3]
def baseStart_2218057 : Nat := 118140960795 + 2218057 * 2 ^ 59
def prefixEnd_2218057 : Nat := 4983230072969 + 3 ^ 40 * 2218057 * 2
def baseEnd_2218057 : Nat := 759286240046489050324565

theorem tailTrace_2218057 : CollatzResearch.WordTrace tailWord_2218057 prefixEnd_2218057 759286240046489050324565 := by
  unfold tailWord_2218057
  simp only [CollatzResearch.WordTrace]
  refine ⟨80899184925365777821788425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53932789950243851881192283 80899184925365777821788425)
  ·
    refine ⟨60674388694024333366341319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80899184925365777821788425 60674388694024333366341319)
    ·
      refine ⟨91011583041036500049511979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60674388694024333366341319 91011583041036500049511979)
      ·
        refine ⟨136517374561554750074267969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91011583041036500049511979 136517374561554750074267969)
        ·
          refine ⟨102388030921166062555700977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136517374561554750074267969 102388030921166062555700977)
          ·
            refine ⟨76791023190874546916775733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102388030921166062555700977 76791023190874546916775733)
            ·
              refine ⟨7199158424144488773447725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76791023190874546916775733 7199158424144488773447725)
              ·
                refine ⟨2699684409054183290042897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7199158424144488773447725 2699684409054183290042897)
                ·
                  refine ⟨2024763306790637467532173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2699684409054183290042897 2024763306790637467532173)
                  ·
                    refine ⟨759286240046489050324565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2024763306790637467532173 759286240046489050324565)
                    ·
                      rfl

theorem cell22_2218057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 3].length) (baseStart_2218057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2218057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2218057 prefixEnd_2218057 := by exact prefixLift 2218057
  have htrace : WordTrace (prefixWord ++ tailWord_2218057) baseStart_2218057 baseEnd_2218057 := by
    simpa [prefixWord, tailWord_2218057, baseEnd_2218057] using wordTrace_append hprefix tailTrace_2218057
  have hstable : (prefixWord ++ tailWord_2218057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218057).length < 2 ^ (prefixWord ++ tailWord_2218057).sum := by decide
  have hdescent : baseEnd_2218057 < baseStart_2218057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218072 : List Nat := [2, 1, 2, 2, 1, 5, 2, 1, 2, 4]
def baseStart_2218072 : Nat := 118140960795 + 2218072 * 2 ^ 59
def prefixEnd_2218072 : Nat := 4983230072969 + 3 ^ 40 * 2218072 * 2
def baseEnd_2218072 : Nat := 759291374853034011199519

theorem tailTrace_2218072 : CollatzResearch.WordTrace tailWord_2218072 prefixEnd_2218072 759291374853034011199519 := by
  unfold tailWord_2218072
  simp only [CollatzResearch.WordTrace]
  refine ⟨40449866010155717691792235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53933154680207623589056313 40449866010155717691792235)
  ·
    refine ⟨60674799015233576537688353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40449866010155717691792235 60674799015233576537688353)
    ·
      refine ⟨45506099261425182403266265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60674799015233576537688353 45506099261425182403266265)
      ·
        refine ⟨34129574446068886802449699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45506099261425182403266265 34129574446068886802449699)
        ·
          refine ⟨51194361669103330203674549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34129574446068886802449699 51194361669103330203674549)
          ·
            refine ⟨4799471406478437206594489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51194361669103330203674549 4799471406478437206594489)
            ·
              refine ⟨3599603554858827904945867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4799471406478437206594489 3599603554858827904945867)
              ·
                refine ⟨5399405332288241857418801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3599603554858827904945867 5399405332288241857418801)
                ·
                  refine ⟨4049553999216181393064101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5399405332288241857418801 4049553999216181393064101)
                  ·
                    refine ⟨759291374853034011199519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4049553999216181393064101 759291374853034011199519)
                    ·
                      rfl

theorem cell22_2218072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_2218072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2218072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2218072 prefixEnd_2218072 := by exact prefixLift 2218072
  have htrace : WordTrace (prefixWord ++ tailWord_2218072) baseStart_2218072 baseEnd_2218072 := by
    simpa [prefixWord, tailWord_2218072, baseEnd_2218072] using wordTrace_append hprefix tailTrace_2218072
  have hstable : (prefixWord ++ tailWord_2218072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218072).length < 2 ^ (prefixWord ++ tailWord_2218072).sum := by decide
  have hdescent : baseEnd_2218072 < baseStart_2218072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218209 : List Nat := [1, 2, 3, 1, 3, 1, 2, 4, 2, 3]
def baseStart_2218209 : Nat := 118140960795 + 2218209 * 2 ^ 59
def prefixEnd_2218209 : Nat := 4983230072969 + 3 ^ 40 * 2218209 * 2
def baseEnd_2218209 : Nat := 759338272752811320524099

theorem tailTrace_2218209 : CollatzResearch.WordTrace tailWord_2218209 prefixEnd_2218209 759338272752811320524099 := by
  unfold tailWord_2218209
  simp only [CollatzResearch.WordTrace]
  refine ⟨80904728820815107781321681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53936485880543405187547787 80904728820815107781321681)
  ·
    refine ⟨60678546615611330835991261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80904728820815107781321681 60678546615611330835991261)
    ·
      refine ⟨22754454980854249063496723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60678546615611330835991261 22754454980854249063496723)
      ·
        refine ⟨34131682471281373595245085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22754454980854249063496723 34131682471281373595245085)
        ·
          refine ⟨12799380926730515098216907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34131682471281373595245085 12799380926730515098216907)
          ·
            refine ⟨19199071390095772647325361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12799380926730515098216907 19199071390095772647325361)
            ·
              refine ⟨14399303542571829485494021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19199071390095772647325361 14399303542571829485494021)
              ·
                refine ⟨2699869414232218028530129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14399303542571829485494021 2699869414232218028530129)
                ·
                  refine ⟨2024902060674163521397597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2699869414232218028530129 2024902060674163521397597)
                  ·
                    refine ⟨759338272752811320524099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2024902060674163521397597 759338272752811320524099)
                    ·
                      rfl

theorem cell22_2218209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_2218209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2218209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2218209 prefixEnd_2218209 := by exact prefixLift 2218209
  have htrace : WordTrace (prefixWord ++ tailWord_2218209) baseStart_2218209 baseEnd_2218209 := by
    simpa [prefixWord, tailWord_2218209, baseEnd_2218209] using wordTrace_append hprefix tailTrace_2218209
  have hstable : (prefixWord ++ tailWord_2218209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218209).length < 2 ^ (prefixWord ++ tailWord_2218209).sum := by decide
  have hdescent : baseEnd_2218209 < baseStart_2218209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218211 : List Nat := [1, 1, 1, 8, 1, 2, 1, 1, 6]
def baseStart_2218211 : Nat := 118140960795 + 2218211 * 2 ^ 59
def prefixEnd_2218211 : Nat := 4983230072969 + 3 ^ 40 * 2218211 * 2
def baseEnd_2218211 : Nat := 253112985797894660658031

theorem tailTrace_2218211 : CollatzResearch.WordTrace tailWord_2218211 prefixEnd_2218211 253112985797894660658031 := by
  unfold tailWord_2218211
  simp only [CollatzResearch.WordTrace]
  refine ⟨80904801766807862122894487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53936534511205241415262991 80904801766807862122894487)
  ·
    refine ⟨121357202650211793184341731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80904801766807862122894487 121357202650211793184341731)
    ·
      refine ⟨182035803975317689776512597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121357202650211793184341731 182035803975317689776512597)
      ·
        refine ⟨2133232077835754177068507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 182035803975317689776512597 2133232077835754177068507)
        ·
          refine ⟨3199848116753631265602761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2133232077835754177068507 3199848116753631265602761)
          ·
            refine ⟨2399886087565223449202071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3199848116753631265602761 2399886087565223449202071)
            ·
              refine ⟨3599829131347835173803107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2399886087565223449202071 3599829131347835173803107)
              ·
                refine ⟨5399743697021752760704661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3599829131347835173803107 5399743697021752760704661)
                ·
                  refine ⟨253112985797894660658031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5399743697021752760704661 253112985797894660658031)
                  ·
                    rfl

theorem cell22_2218211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 6].length) (baseStart_2218211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2218211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2218211 prefixEnd_2218211 := by exact prefixLift 2218211
  have htrace : WordTrace (prefixWord ++ tailWord_2218211) baseStart_2218211 baseEnd_2218211 := by
    simpa [prefixWord, tailWord_2218211, baseEnd_2218211] using wordTrace_append hprefix tailTrace_2218211
  have hstable : (prefixWord ++ tailWord_2218211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218211).length < 2 ^ (prefixWord ++ tailWord_2218211).sum := by decide
  have hdescent : baseEnd_2218211 < baseStart_2218211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218226 : List Nat := [3, 2, 1, 3, 2, 2, 1, 3, 2, 3]
def baseStart_2218226 : Nat := 118140960795 + 2218226 * 2 ^ 59
def prefixEnd_2218226 : Nat := 4983230072969 + 3 ^ 40 * 2218226 * 2
def baseEnd_2218226 : Nat := 759344092200228942849047

theorem tailTrace_2218226 : CollatzResearch.WordTrace tailWord_2218226 prefixEnd_2218226 759344092200228942849047 := by
  unfold tailWord_2218226
  simp only [CollatzResearch.WordTrace]
  refine ⟨20226337215438379921172633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53936899241169013123127021 20226337215438379921172633)
  ·
    refine ⟨15169752911578784940879475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20226337215438379921172633 15169752911578784940879475)
    ·
      refine ⟨22754629367368177411319213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15169752911578784940879475 22754629367368177411319213)
      ·
        refine ⟨8532986012763066529244705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22754629367368177411319213 8532986012763066529244705)
        ·
          refine ⟨6399739509572299896933529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8532986012763066529244705 6399739509572299896933529)
          ·
            refine ⟨4799804632179224922700147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6399739509572299896933529 4799804632179224922700147)
            ·
              refine ⟨7199706948268837384050221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4799804632179224922700147 7199706948268837384050221)
              ·
                refine ⟨2699890105600814019018833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7199706948268837384050221 2699890105600814019018833)
                ·
                  refine ⟨2024917579200610514264125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2699890105600814019018833 2024917579200610514264125)
                  ·
                    refine ⟨759344092200228942849047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2024917579200610514264125 759344092200228942849047)
                    ·
                      rfl

theorem cell22_2218226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_2218226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2218226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2218226 prefixEnd_2218226 := by exact prefixLift 2218226
  have htrace : WordTrace (prefixWord ++ tailWord_2218226) baseStart_2218226 baseEnd_2218226 := by
    simpa [prefixWord, tailWord_2218226, baseEnd_2218226] using wordTrace_append hprefix tailTrace_2218226
  have hstable : (prefixWord ++ tailWord_2218226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218226).length < 2 ^ (prefixWord ++ tailWord_2218226).sum := by decide
  have hdescent : baseEnd_2218226 < baseStart_2218226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218267 : List Nat := [1, 1, 1, 1, 1, 1, 7, 4, 5]
def baseStart_2218267 : Nat := 118140960795 + 2218267 * 2 ^ 59
def prefixEnd_2218267 : Nat := 4983230072969 + 3 ^ 40 * 2218267 * 2
def baseEnd_2218267 : Nat := 253119375779372834191307

theorem tailTrace_2218267 : CollatzResearch.WordTrace tailWord_2218267 prefixEnd_2218267 253119375779372834191307 := by
  unfold tailWord_2218267
  simp only [CollatzResearch.WordTrace]
  refine ⟨80906844254604983686933055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53937896169736655791288703 80906844254604983686933055)
  ·
    refine ⟨121360266381907475530399583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80906844254604983686933055 121360266381907475530399583)
    ·
      refine ⟨182040399572861213295599375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121360266381907475530399583 182040399572861213295599375)
      ·
        refine ⟨273060599359291819943399063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182040399572861213295599375 273060599359291819943399063)
        ·
          refine ⟨409590899038937729915098595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273060599359291819943399063 409590899038937729915098595)
          ·
            refine ⟨614386348558406594872647893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409590899038937729915098595 614386348558406594872647893)
            ·
              refine ⟨14399680044337654567327685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 614386348558406594872647893 14399680044337654567327685)
              ·
                refine ⟨2699940008313310231373941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14399680044337654567327685 2699940008313310231373941)
                ·
                  refine ⟨253119375779372834191307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2699940008313310231373941 253119375779372834191307)
                  ·
                    rfl

theorem cell22_2218267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 5].length) (baseStart_2218267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2218267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2218267 prefixEnd_2218267 := by exact prefixLift 2218267
  have htrace : WordTrace (prefixWord ++ tailWord_2218267) baseStart_2218267 baseEnd_2218267 := by
    simpa [prefixWord, tailWord_2218267, baseEnd_2218267] using wordTrace_append hprefix tailTrace_2218267
  have hstable : (prefixWord ++ tailWord_2218267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218267).length < 2 ^ (prefixWord ++ tailWord_2218267).sum := by decide
  have hdescent : baseEnd_2218267 < baseStart_2218267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218305 : List Nat := [1, 2, 5, 2, 2, 1, 2, 3, 1, 3]
def baseStart_2218305 : Nat := 118140960795 + 2218305 * 2 ^ 59
def prefixEnd_2218305 : Nat := 4983230072969 + 3 ^ 40 * 2218305 * 2
def baseEnd_2218305 : Nat := 759371135514699070123805

theorem tailTrace_2218305 : CollatzResearch.WordTrace tailWord_2218305 prefixEnd_2218305 759371135514699070123805 := by
  unfold tailWord_2218305
  simp only [CollatzResearch.WordTrace]
  refine ⟨80908230228467316176816369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53938820152311544117877579 80908230228467316176816369)
  ·
    refine ⟨60681172671350487132612277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80908230228467316176816369 60681172671350487132612277)
    ·
      refine ⟨5688859937939108168682401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60681172671350487132612277 5688859937939108168682401)
      ·
        refine ⟨4266644953454331126511801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5688859937939108168682401 4266644953454331126511801)
        ·
          refine ⟨3199983715090748344883851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4266644953454331126511801 3199983715090748344883851)
          ·
            refine ⟨4799975572636122517325777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3199983715090748344883851 4799975572636122517325777)
            ·
              refine ⟨3599981679477091887994333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4799975572636122517325777 3599981679477091887994333)
              ·
                refine ⟨1349993129803909457997875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3599981679477091887994333 1349993129803909457997875)
                ·
                  refine ⟨2024989694705864186996813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1349993129803909457997875 2024989694705864186996813)
                  ·
                    refine ⟨759371135514699070123805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2024989694705864186996813 759371135514699070123805)
                    ·
                      rfl

theorem cell22_2218305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_2218305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2218305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2218305 prefixEnd_2218305 := by exact prefixLift 2218305
  have htrace : WordTrace (prefixWord ++ tailWord_2218305) baseStart_2218305 baseEnd_2218305 := by
    simpa [prefixWord, tailWord_2218305, baseEnd_2218305] using wordTrace_append hprefix tailTrace_2218305
  have hstable : (prefixWord ++ tailWord_2218305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218305).length < 2 ^ (prefixWord ++ tailWord_2218305).sum := by decide
  have hdescent : baseEnd_2218305 < baseStart_2218305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218440 : List Nat := [2, 1, 3, 1, 3, 2, 4, 2, 1, 3]
def baseStart_2218440 : Nat := 118140960795 + 2218440 * 2 ^ 59
def prefixEnd_2218440 : Nat := 4983230072969 + 3 ^ 40 * 2218440 * 2
def baseEnd_2218440 : Nat := 759417348773603717998391

theorem tailTrace_2218440 : CollatzResearch.WordTrace tailWord_2218440 prefixEnd_2218440 759417348773603717998391 := by
  unfold tailWord_2218440
  simp only [CollatzResearch.WordTrace]
  refine ⟨40456577041489117116490387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53942102721985489488653849 40456577041489117116490387)
  ·
    refine ⟨60684865562233675674735581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40456577041489117116490387 60684865562233675674735581)
    ·
      refine ⟨22756824585837628378025843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60684865562233675674735581 22756824585837628378025843)
      ·
        refine ⟨34135236878756442567038765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22756824585837628378025843 34135236878756442567038765)
        ·
          refine ⟨12800713829533665962639537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34135236878756442567038765 12800713829533665962639537)
          ·
            refine ⟨9600535372150249471979653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12800713829533665962639537 9600535372150249471979653)
            ·
              refine ⟨1800100382278171775996185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9600535372150249471979653 1800100382278171775996185)
              ·
                refine ⟨1350075286708628831997139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1800100382278171775996185 1350075286708628831997139)
                ·
                  refine ⟨2025112930062943247995709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1350075286708628831997139 2025112930062943247995709)
                  ·
                    refine ⟨759417348773603717998391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2025112930062943247995709 759417348773603717998391)
                    ·
                      rfl

theorem cell22_2218440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_2218440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2218440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2218440 prefixEnd_2218440 := by exact prefixLift 2218440
  have htrace : WordTrace (prefixWord ++ tailWord_2218440) baseStart_2218440 baseEnd_2218440 := by
    simpa [prefixWord, tailWord_2218440, baseEnd_2218440] using wordTrace_append hprefix tailTrace_2218440
  have hstable : (prefixWord ++ tailWord_2218440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218440).length < 2 ^ (prefixWord ++ tailWord_2218440).sum := by decide
  have hdescent : baseEnd_2218440 < baseStart_2218440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218464 : List Nat := [2, 1, 1, 3, 1, 1, 5, 2, 6]
def baseStart_2218464 : Nat := 118140960795 + 2218464 * 2 ^ 59
def prefixEnd_2218464 : Nat := 4983230072969 + 3 ^ 40 * 2218464 * 2
def baseEnd_2218464 : Nat := 253141854821358551799439

theorem tailTrace_2218464 : CollatzResearch.WordTrace tailWord_2218464 prefixEnd_2218464 253141854821358551799439 := by
  unfold tailWord_2218464
  simp only [CollatzResearch.WordTrace]
  refine ⟨40457014717445643165927223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53942686289927524221236297 40457014717445643165927223)
  ·
    refine ⟨60685522076168464748890835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40457014717445643165927223 60685522076168464748890835)
    ·
      refine ⟨91028283114252697123336253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60685522076168464748890835 91028283114252697123336253)
      ·
        refine ⟨34135606167844761421251095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91028283114252697123336253 34135606167844761421251095)
        ·
          refine ⟨51203409251767142131876643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34135606167844761421251095 51203409251767142131876643)
          ·
            refine ⟨76805113877650713197814965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51203409251767142131876643 76805113877650713197814965)
            ·
              refine ⟨7200479426029754362295153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76805113877650713197814965 7200479426029754362295153)
              ·
                refine ⟨5400359569522315771721365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7200479426029754362295153 5400359569522315771721365)
                ·
                  refine ⟨253141854821358551799439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5400359569522315771721365 253141854821358551799439)
                  ·
                    rfl

theorem cell22_2218464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 6].length) (baseStart_2218464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2218464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2218464 prefixEnd_2218464 := by exact prefixLift 2218464
  have htrace : WordTrace (prefixWord ++ tailWord_2218464) baseStart_2218464 baseEnd_2218464 := by
    simpa [prefixWord, tailWord_2218464, baseEnd_2218464] using wordTrace_append hprefix tailTrace_2218464
  have hstable : (prefixWord ++ tailWord_2218464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218464).length < 2 ^ (prefixWord ++ tailWord_2218464).sum := by decide
  have hdescent : baseEnd_2218464 < baseStart_2218464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218532 : List Nat := [2, 3, 1, 5, 1, 2, 1, 3, 4]
def baseStart_2218532 : Nat := 118140960795 + 2218532 * 2 ^ 59
def prefixEnd_2218532 : Nat := 4983230072969 + 3 ^ 40 * 2218532 * 2
def baseEnd_2218532 : Nat := 253149614084582048232703

theorem tailTrace_2218532 : CollatzResearch.WordTrace tailWord_2218532 prefixEnd_2218532 253149614084582048232703 := by
  unfold tailWord_2218532
  simp only [CollatzResearch.WordTrace]
  refine ⟨40458254799322466972664925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53944339732429955963553233 40458254799322466972664925)
  ·
    refine ⟨15171845549745925114749347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40458254799322466972664925 15171845549745925114749347)
    ·
      refine ⟨22757768324618887672124021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15171845549745925114749347 22757768324618887672124021)
      ·
        refine ⟨2133540780433020719261627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22757768324618887672124021 2133540780433020719261627)
        ·
          refine ⟨3200311170649531078892441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2133540780433020719261627 3200311170649531078892441)
          ·
            refine ⟨2400233377987148309169331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3200311170649531078892441 2400233377987148309169331)
            ·
              refine ⟨3600350066980722463753997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2400233377987148309169331 3600350066980722463753997)
              ·
                refine ⟨1350131275117770923907749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3600350066980722463753997 1350131275117770923907749)
                ·
                  refine ⟨253149614084582048232703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1350131275117770923907749 253149614084582048232703)
                  ·
                    rfl

theorem cell22_2218532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_2218532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2218532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2218532 prefixEnd_2218532 := by exact prefixLift 2218532
  have htrace : WordTrace (prefixWord ++ tailWord_2218532) baseStart_2218532 baseEnd_2218532 := by
    simpa [prefixWord, tailWord_2218532, baseEnd_2218532] using wordTrace_append hprefix tailTrace_2218532
  have hstable : (prefixWord ++ tailWord_2218532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218532).length < 2 ^ (prefixWord ++ tailWord_2218532).sum := by decide
  have hdescent : baseEnd_2218532 < baseStart_2218532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218564 : List Nat := [2, 3, 5, 1, 1, 1, 1, 3, 2, 3]
def baseStart_2218564 : Nat := 118140960795 + 2218564 * 2 ^ 59
def prefixEnd_2218564 : Nat := 4983230072969 + 3 ^ 40 * 2218564 * 2
def baseEnd_2218564 : Nat := 759459796507708727898011

theorem tailTrace_2218564 : CollatzResearch.WordTrace tailWord_2218564 prefixEnd_2218564 759459796507708727898011 := by
  unfold tailWord_2218564
  simp only [CollatzResearch.WordTrace]
  refine ⟨40458838367264501705247373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53945117823019335606996497 40458838367264501705247373)
  ·
    refine ⟨15172064387724188139467765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40458838367264501705247373 15172064387724188139467765)
    ·
      refine ⟨1422381036349142638075103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15172064387724188139467765 1422381036349142638075103)
      ·
        refine ⟨2133571554523713957112655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1422381036349142638075103 2133571554523713957112655)
        ·
          refine ⟨3200357331785570935668983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2133571554523713957112655 3200357331785570935668983)
          ·
            refine ⟨4800535997678356403503475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3200357331785570935668983 4800535997678356403503475)
            ·
              refine ⟨7200803996517534605255213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4800535997678356403503475 7200803996517534605255213)
              ·
                refine ⟨2700301498694075476970705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7200803996517534605255213 2700301498694075476970705)
                ·
                  refine ⟨2025226124020556607728029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2700301498694075476970705 2025226124020556607728029)
                  ·
                    refine ⟨759459796507708727898011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2025226124020556607728029 759459796507708727898011)
                    ·
                      rfl

theorem cell22_2218564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_2218564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2218564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2218564 prefixEnd_2218564 := by exact prefixLift 2218564
  have htrace : WordTrace (prefixWord ++ tailWord_2218564) baseStart_2218564 baseEnd_2218564 := by
    simpa [prefixWord, tailWord_2218564, baseEnd_2218564] using wordTrace_append hprefix tailTrace_2218564
  have hstable : (prefixWord ++ tailWord_2218564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218564).length < 2 ^ (prefixWord ++ tailWord_2218564).sum := by decide
  have hdescent : baseEnd_2218564 < baseStart_2218564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218648 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 4, 3]
def baseStart_2218648 : Nat := 118140960795 + 2218648 * 2 ^ 59
def prefixEnd_2218648 : Nat := 4983230072969 + 3 ^ 40 * 2218648 * 2
def baseEnd_2218648 : Nat := 759488551424360508797753

theorem tailTrace_2218648 : CollatzResearch.WordTrace tailWord_2218648 prefixEnd_2218648 759488551424360508797753 := by
  unfold tailWord_2218648
  simp only [CollatzResearch.WordTrace]
  refine ⟨40460370233112342878276299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53947160310816457171035065 40460370233112342878276299)
  ·
    refine ⟨60690555349668514317414449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40460370233112342878276299 60690555349668514317414449)
    ·
      refine ⟨45517916512251385738060837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60690555349668514317414449 45517916512251385738060837)
      ·
        refine ⟨8534609346047134825886407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45517916512251385738060837 8534609346047134825886407)
        ·
          refine ⟨12801914019070702238829611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8534609346047134825886407 12801914019070702238829611)
          ·
            refine ⟨19202871028606053358244417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12801914019070702238829611 19202871028606053358244417)
            ·
              refine ⟨14402153271454540018683313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19202871028606053358244417 14402153271454540018683313)
              ·
                refine ⟨10801614953590905014012485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14402153271454540018683313 10801614953590905014012485)
                ·
                  refine ⟨2025302803798294690127341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10801614953590905014012485 2025302803798294690127341)
                  ·
                    refine ⟨759488551424360508797753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2025302803798294690127341 759488551424360508797753)
                    ·
                      rfl

theorem cell22_2218648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 4, 3].length) (baseStart_2218648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2218648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2218648 prefixEnd_2218648 := by exact prefixLift 2218648
  have htrace : WordTrace (prefixWord ++ tailWord_2218648) baseStart_2218648 baseEnd_2218648 := by
    simpa [prefixWord, tailWord_2218648, baseEnd_2218648] using wordTrace_append hprefix tailTrace_2218648
  have hstable : (prefixWord ++ tailWord_2218648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218648).length < 2 ^ (prefixWord ++ tailWord_2218648).sum := by decide
  have hdescent : baseEnd_2218648 < baseStart_2218648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218652 : List Nat := [2, 2, 3, 2, 2, 3, 2, 1, 1, 4]
def baseStart_2218652 : Nat := 118140960795 + 2218652 * 2 ^ 59
def prefixEnd_2218652 : Nat := 4983230072969 + 3 ^ 40 * 2218652 * 2
def baseEnd_2218652 : Nat := 759489920706105831697741

theorem tailTrace_2218652 : CollatzResearch.WordTrace tailWord_2218652 prefixEnd_2218652 759489920706105831697741 := by
  unfold tailWord_2218652
  simp only [CollatzResearch.WordTrace]
  refine ⟨40460443179105097219849105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53947257572140129626465473 40460443179105097219849105)
  ·
    refine ⟨30345332384328822914886829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40460443179105097219849105 30345332384328822914886829)
    ·
      refine ⟨11379499644123308593082561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30345332384328822914886829 11379499644123308593082561)
      ·
        refine ⟨8534624733092481444811921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11379499644123308593082561 8534624733092481444811921)
        ·
          refine ⟨6400968549819361083608941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8534624733092481444811921 6400968549819361083608941)
          ·
            refine ⟨2400363206182260406353353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6400968549819361083608941 2400363206182260406353353)
            ·
              refine ⟨1800272404636695304765015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2400363206182260406353353 1800272404636695304765015)
              ·
                refine ⟨2700408606955042957147523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1800272404636695304765015 2700408606955042957147523)
                ·
                  refine ⟨4050612910432564435721285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2700408606955042957147523 4050612910432564435721285)
                  ·
                    refine ⟨759489920706105831697741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4050612910432564435721285 759489920706105831697741)
                    ·
                      rfl

theorem cell22_2218652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_2218652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2218652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2218652 prefixEnd_2218652 := by exact prefixLift 2218652
  have htrace : WordTrace (prefixWord ++ tailWord_2218652) baseStart_2218652 baseEnd_2218652 := by
    simpa [prefixWord, tailWord_2218652, baseEnd_2218652] using wordTrace_append hprefix tailTrace_2218652
  have hstable : (prefixWord ++ tailWord_2218652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218652).length < 2 ^ (prefixWord ++ tailWord_2218652).sum := by decide
  have hdescent : baseEnd_2218652 < baseStart_2218652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218701 : List Nat := [1, 6, 2, 1, 3, 1, 1, 3, 4]
def baseStart_2218701 : Nat := 118140960795 + 2218701 * 2 ^ 59
def prefixEnd_2218701 : Nat := 4983230072969 + 3 ^ 40 * 2218701 * 2
def baseEnd_2218701 : Nat := 253168898135828679074197

theorem tailTrace_2218701 : CollatzResearch.WordTrace tailWord_2218701 prefixEnd_2218701 253168898135828679074197 := by
  unfold tailWord_2218701
  simp only [CollatzResearch.WordTrace]
  refine ⟨80922673535032675808231957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53948449023355117205487971 80922673535032675808231957)
  ·
    refine ⟨3793250321954656678510873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 80922673535032675808231957 3793250321954656678510873)
    ·
      refine ⟨2844937741465992508883155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3793250321954656678510873 2844937741465992508883155)
      ·
        refine ⟨4267406612198988763324733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2844937741465992508883155 4267406612198988763324733)
        ·
          refine ⟨1600277479574620786246775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4267406612198988763324733 1600277479574620786246775)
          ·
            refine ⟨2400416219361931179370163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1600277479574620786246775 2400416219361931179370163)
            ·
              refine ⟨3600624329042896769055245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2400416219361931179370163 3600624329042896769055245)
              ·
                refine ⟨1350234123391086288395717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3600624329042896769055245 1350234123391086288395717)
                ·
                  refine ⟨253168898135828679074197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1350234123391086288395717 253168898135828679074197)
                  ·
                    rfl

theorem cell22_2218701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_2218701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2218701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2218701 prefixEnd_2218701 := by exact prefixLift 2218701
  have htrace : WordTrace (prefixWord ++ tailWord_2218701) baseStart_2218701 baseEnd_2218701 := by
    simpa [prefixWord, tailWord_2218701, baseEnd_2218701] using wordTrace_append hprefix tailTrace_2218701
  have hstable : (prefixWord ++ tailWord_2218701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218701).length < 2 ^ (prefixWord ++ tailWord_2218701).sum := by decide
  have hdescent : baseEnd_2218701 < baseStart_2218701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218723 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 7]
def baseStart_2218723 : Nat := 118140960795 + 2218723 * 2 ^ 59
def prefixEnd_2218723 : Nat := 4983230072969 + 3 ^ 40 * 2218723 * 2
def baseEnd_2218723 : Nat := 253171408485695104390841

theorem tailTrace_2218723 : CollatzResearch.WordTrace tailWord_2218723 prefixEnd_2218723 253171408485695104390841 := by
  unfold tailWord_2218723
  simp only [CollatzResearch.WordTrace]
  refine ⟨80923475940952973565532823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53948983960635315710355215 80923475940952973565532823)
  ·
    refine ⟨121385213911429460348299235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80923475940952973565532823 121385213911429460348299235)
    ·
      refine ⟨182077820867144190522448853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121385213911429460348299235 182077820867144190522448853)
      ·
        refine ⟨4267448926573691965369895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 182077820867144190522448853 4267448926573691965369895)
        ·
          refine ⟨6401173389860537948054843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4267448926573691965369895 6401173389860537948054843)
          ·
            refine ⟨9601760084790806922082265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6401173389860537948054843 9601760084790806922082265)
            ·
              refine ⟨7201320063593105191561699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9601760084790806922082265 7201320063593105191561699)
              ·
                refine ⟨10801980095389657787342549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7201320063593105191561699 10801980095389657787342549)
                ·
                  refine ⟨253171408485695104390841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10801980095389657787342549 253171408485695104390841)
                  ·
                    rfl

theorem cell22_2218723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 7].length) (baseStart_2218723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2218723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2218723 prefixEnd_2218723 := by exact prefixLift 2218723
  have htrace : WordTrace (prefixWord ++ tailWord_2218723) baseStart_2218723 baseEnd_2218723 := by
    simpa [prefixWord, tailWord_2218723, baseEnd_2218723] using wordTrace_append hprefix tailTrace_2218723
  have hstable : (prefixWord ++ tailWord_2218723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218723).length < 2 ^ (prefixWord ++ tailWord_2218723).sum := by decide
  have hdescent : baseEnd_2218723 < baseStart_2218723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218751 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 8]
def baseStart_2218751 : Nat := 118140960795 + 2218751 * 2 ^ 59
def prefixEnd_2218751 : Nat := 4983230072969 + 3 ^ 40 * 2218751 * 2
def baseEnd_2218751 : Nat := 253174603476434191157479

theorem tailTrace_2218751 : CollatzResearch.WordTrace tailWord_2218751 prefixEnd_2218751 253174603476434191157479 := by
  unfold tailWord_2218751
  simp only [CollatzResearch.WordTrace]
  refine ⟨80924497184851534347552107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53949664789901022898368071 80924497184851534347552107)
  ·
    refine ⟨121386745777277301521328161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80924497184851534347552107 121386745777277301521328161)
    ·
      refine ⟨91040059332957976140996121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121386745777277301521328161 91040059332957976140996121)
      ·
        refine ⟨68280044499718482105747091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91040059332957976140996121 68280044499718482105747091)
        ·
          refine ⟨102420066749577723158620637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68280044499718482105747091 102420066749577723158620637)
          ·
            refine ⟨38407525031091646184482739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102420066749577723158620637 38407525031091646184482739)
            ·
              refine ⟨57611287546637469276724109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38407525031091646184482739 57611287546637469276724109)
              ·
                refine ⟨21604232829989050978771541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57611287546637469276724109 21604232829989050978771541)
                ·
                  refine ⟨253174603476434191157479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21604232829989050978771541 253174603476434191157479)
                  ·
                    rfl

theorem cell22_2218751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 8].length) (baseStart_2218751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2218751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2218751 prefixEnd_2218751 := by exact prefixLift 2218751
  have htrace : WordTrace (prefixWord ++ tailWord_2218751) baseStart_2218751 baseEnd_2218751 := by
    simpa [prefixWord, tailWord_2218751, baseEnd_2218751] using wordTrace_append hprefix tailTrace_2218751
  have hstable : (prefixWord ++ tailWord_2218751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218751).length < 2 ^ (prefixWord ++ tailWord_2218751).sum := by decide
  have hdescent : baseEnd_2218751 < baseStart_2218751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218785 : List Nat := [1, 2, 3, 2, 1, 2, 3, 4, 4]
def baseStart_2218785 : Nat := 118140960795 + 2218785 * 2 ^ 59
def prefixEnd_2218785 : Nat := 4983230072969 + 3 ^ 40 * 2218785 * 2
def baseEnd_2218785 : Nat := 253178483108045939374111

theorem tailTrace_2218785 : CollatzResearch.WordTrace tailWord_2218785 prefixEnd_2218785 253178483108045939374111 := by
  unfold tailWord_2218785
  simp only [CollatzResearch.WordTrace]
  refine ⟨80925737266728358154289809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53950491511152238769526539 80925737266728358154289809)
  ·
    refine ⟨60694302950046268615717357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80925737266728358154289809 60694302950046268615717357)
    ·
      refine ⟨22760363606267350730894009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60694302950046268615717357 22760363606267350730894009)
      ·
        refine ⟨17070272704700513048170507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22760363606267350730894009 17070272704700513048170507)
        ·
          refine ⟨25605409057050769572255761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17070272704700513048170507 25605409057050769572255761)
          ·
            refine ⟨19204056792788077179191821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25605409057050769572255761 19204056792788077179191821)
            ·
              refine ⟨7201521297295528942196933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19204056792788077179191821 7201521297295528942196933)
              ·
                refine ⟨1350285243242911676661925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7201521297295528942196933 1350285243242911676661925)
                ·
                  refine ⟨253178483108045939374111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1350285243242911676661925 253178483108045939374111)
                  ·
                    rfl

theorem cell22_2218785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 4].length) (baseStart_2218785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2218785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2218785 prefixEnd_2218785 := by exact prefixLift 2218785
  have htrace : WordTrace (prefixWord ++ tailWord_2218785) baseStart_2218785 baseEnd_2218785 := by
    simpa [prefixWord, tailWord_2218785, baseEnd_2218785] using wordTrace_append hprefix tailTrace_2218785
  have hstable : (prefixWord ++ tailWord_2218785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218785).length < 2 ^ (prefixWord ++ tailWord_2218785).sum := by decide
  have hdescent : baseEnd_2218785 < baseStart_2218785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218815 : List Nat := [1, 1, 2, 2, 5, 1, 3, 1, 2, 4]
def baseStart_2218815 : Nat := 118140960795 + 2218815 * 2 ^ 59
def prefixEnd_2218815 : Nat := 4983230072969 + 3 ^ 40 * 2218815 * 2
def baseEnd_2218815 : Nat := 759545718937227739872241

theorem tailTrace_2218815 : CollatzResearch.WordTrace tailWord_2218815 prefixEnd_2218815 759545718937227739872241 := by
  unfold tailWord_2218815
  simp only [CollatzResearch.WordTrace]
  refine ⟨80926831456619673277881899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53951220971079782185254599 80926831456619673277881899)
  ·
    refine ⟨121390247184929509916822849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80926831456619673277881899 121390247184929509916822849)
    ·
      refine ⟨91042685388697132437617137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121390247184929509916822849 91042685388697132437617137)
      ·
        refine ⟨68282014041522849328212853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91042685388697132437617137 68282014041522849328212853)
        ·
          refine ⟨6401438816392767124519955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68282014041522849328212853 6401438816392767124519955)
          ·
            refine ⟨9602158224589150686779933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6401438816392767124519955 9602158224589150686779933)
            ·
              refine ⟨3600809334220931507542475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9602158224589150686779933 3600809334220931507542475)
              ·
                refine ⟨5401214001331397261313713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3600809334220931507542475 5401214001331397261313713)
                ·
                  refine ⟨4050910500998547945985285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5401214001331397261313713 4050910500998547945985285)
                  ·
                    refine ⟨759545718937227739872241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4050910500998547945985285 759545718937227739872241)
                    ·
                      rfl

theorem cell22_2218815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 4].length) (baseStart_2218815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2218815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2218815 prefixEnd_2218815 := by exact prefixLift 2218815
  have htrace : WordTrace (prefixWord ++ tailWord_2218815) baseStart_2218815 baseEnd_2218815 := by
    simpa [prefixWord, tailWord_2218815, baseEnd_2218815] using wordTrace_append hprefix tailTrace_2218815
  have hstable : (prefixWord ++ tailWord_2218815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218815).length < 2 ^ (prefixWord ++ tailWord_2218815).sum := by decide
  have hdescent : baseEnd_2218815 < baseStart_2218815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218935 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 6, 3]
def baseStart_2218935 : Nat := 118140960795 + 2218935 * 2 ^ 59
def prefixEnd_2218935 : Nat := 4983230072969 + 3 ^ 40 * 2218935 * 2
def baseEnd_2218935 : Nat := 759586797389587426871873

theorem tailTrace_2218935 : CollatzResearch.WordTrace tailWord_2218935 prefixEnd_2218935 759586797389587426871873 := by
  unfold tailWord_2218935
  simp only [CollatzResearch.WordTrace]
  refine ⟨80931208216184933772250259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53954138810789955848166839 80931208216184933772250259)
  ·
    refine ⟨121396812324277400658375389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80931208216184933772250259 121396812324277400658375389)
    ·
      refine ⟨45523804621604025246890771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121396812324277400658375389 45523804621604025246890771)
      ·
        refine ⟨68285706932406037870336157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45523804621604025246890771 68285706932406037870336157)
        ·
          refine ⟨25607140099652264201376059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68285706932406037870336157 25607140099652264201376059)
          ·
            refine ⟨38410710149478396302064089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25607140099652264201376059 38410710149478396302064089)
            ·
              refine ⟨28808032612108797226548067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38410710149478396302064089 28808032612108797226548067)
              ·
                refine ⟨43212048918163195839822101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28808032612108797226548067 43212048918163195839822101)
                ·
                  refine ⟨2025564793038899804991661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43212048918163195839822101 2025564793038899804991661)
                  ·
                    refine ⟨759586797389587426871873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2025564793038899804991661 759586797389587426871873)
                    ·
                      rfl

theorem cell22_2218935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 3].length) (baseStart_2218935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2218935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2218935 prefixEnd_2218935 := by exact prefixLift 2218935
  have htrace : WordTrace (prefixWord ++ tailWord_2218935) baseStart_2218935 baseEnd_2218935 := by
    simpa [prefixWord, tailWord_2218935, baseEnd_2218935] using wordTrace_append hprefix tailTrace_2218935
  have hstable : (prefixWord ++ tailWord_2218935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218935).length < 2 ^ (prefixWord ++ tailWord_2218935).sum := by decide
  have hdescent : baseEnd_2218935 < baseStart_2218935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219057 : List Nat := [1, 2, 2, 3, 1, 2, 1, 5, 1, 4]
def baseStart_2219057 : Nat := 118140960795 + 2219057 * 2 ^ 59
def prefixEnd_2219057 : Nat := 4983230072969 + 3 ^ 40 * 2219057 * 2
def baseEnd_2219057 : Nat := 759628560482819775321499

theorem tailTrace_2219057 : CollatzResearch.WordTrace tailWord_2219057 prefixEnd_2219057 759628560482819775321499 := by
  unfold tailWord_2219057
  simp only [CollatzResearch.WordTrace]
  refine ⟨80935657921742948608191425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53957105281161965738794283 80935657921742948608191425)
  ·
    refine ⟨60701743441307211456143569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80935657921742948608191425 60701743441307211456143569)
    ·
      refine ⟨45526307580980408592107677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60701743441307211456143569 45526307580980408592107677)
      ·
        refine ⟨17072365342867653222040379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45526307580980408592107677 17072365342867653222040379)
        ·
          refine ⟨25608548014301479833060569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17072365342867653222040379 25608548014301479833060569)
          ·
            refine ⟨19206411010726109874795427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25608548014301479833060569 19206411010726109874795427)
            ·
              refine ⟨28809616516089164812193141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19206411010726109874795427 28809616516089164812193141)
              ·
                refine ⟨2700901548383359201143107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28809616516089164812193141 2700901548383359201143107)
                ·
                  refine ⟨4051352322575038801714661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2700901548383359201143107 4051352322575038801714661)
                  ·
                    refine ⟨759628560482819775321499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4051352322575038801714661 759628560482819775321499)
                    ·
                      rfl

theorem cell22_2219057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_2219057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219057 prefixEnd_2219057 := by exact prefixLift 2219057
  have htrace : WordTrace (prefixWord ++ tailWord_2219057) baseStart_2219057 baseEnd_2219057 := by
    simpa [prefixWord, tailWord_2219057, baseEnd_2219057] using wordTrace_append hprefix tailTrace_2219057
  have hstable : (prefixWord ++ tailWord_2219057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219057).length < 2 ^ (prefixWord ++ tailWord_2219057).sum := by decide
  have hdescent : baseEnd_2219057 < baseStart_2219057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219078 : List Nat := [6, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_2219078 : Nat := 118140960795 + 2219078 * 2 ^ 59
def prefixEnd_2219078 : Nat := 4983230072969 + 3 ^ 40 * 2219078 * 2
def baseEnd_2219078 : Nat := 253211916403994240182145

theorem tailTrace_2219078 : CollatzResearch.WordTrace tailWord_2219078 prefixEnd_2219078 253211916403994240182145 := by
  unfold tailWord_2219078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2529263245458339662334559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53957615903111246129803925 2529263245458339662334559)
  ·
    refine ⟨3793894868187509493501839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2529263245458339662334559 3793894868187509493501839)
    ·
      refine ⟨5690842302281264240252759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3793894868187509493501839 5690842302281264240252759)
      ·
        refine ⟨8536263453421896360379139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5690842302281264240252759 8536263453421896360379139)
        ·
          refine ⟨12804395180132844540568709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8536263453421896360379139 12804395180132844540568709)
          ·
            refine ⟨2400824096274908351356633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12804395180132844540568709 2400824096274908351356633)
            ·
              refine ⟨1800618072206181263517475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2400824096274908351356633 1800618072206181263517475)
              ·
                refine ⟨2700927108309271895276213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1800618072206181263517475 2700927108309271895276213)
                ·
                  refine ⟨253211916403994240182145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2700927108309271895276213 253211916403994240182145)
                  ·
                    rfl

theorem cell22_2219078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_2219078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219078 prefixEnd_2219078 := by exact prefixLift 2219078
  have htrace : WordTrace (prefixWord ++ tailWord_2219078) baseStart_2219078 baseEnd_2219078 := by
    simpa [prefixWord, tailWord_2219078, baseEnd_2219078] using wordTrace_append hprefix tailTrace_2219078
  have hstable : (prefixWord ++ tailWord_2219078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219078).length < 2 ^ (prefixWord ++ tailWord_2219078).sum := by decide
  have hdescent : baseEnd_2219078 < baseStart_2219078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219192 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 3, 4]
def baseStart_2219192 : Nat := 118140960795 + 2219192 * 2 ^ 59
def prefixEnd_2219192 : Nat := 4983230072969 + 3 ^ 40 * 2219192 * 2
def baseEnd_2219192 : Nat := 759674773741724423196085

theorem tailTrace_2219192 : CollatzResearch.WordTrace tailWord_2219192 prefixEnd_2219192 759674773741724423196085 := by
  unfold tailWord_2219192
  simp only [CollatzResearch.WordTrace]
  refine ⟨40470290888126933332177915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53960387850835911109570553 40470290888126933332177915)
  ·
    refine ⟨60705436332190399998266873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40470290888126933332177915 60705436332190399998266873)
    ·
      refine ⟨45529077249142799998700155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60705436332190399998266873 45529077249142799998700155)
      ·
        refine ⟨68293615873714199998050233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45529077249142799998700155 68293615873714199998050233)
        ·
          refine ⟨51220211905285649998537675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68293615873714199998050233 51220211905285649998537675)
          ·
            refine ⟨76830317857928474997806513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51220211905285649998537675 76830317857928474997806513)
            ·
              refine ⟨57622738393446356248354885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76830317857928474997806513 57622738393446356248354885)
              ·
                refine ⟨10804263448771191796566541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57622738393446356248354885 10804263448771191796566541)
                ·
                  refine ⟨4051598793289196923712453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10804263448771191796566541 4051598793289196923712453)
                  ·
                    refine ⟨759674773741724423196085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4051598793289196923712453 759674773741724423196085)
                    ·
                      rfl

theorem cell22_2219192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_2219192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219192 prefixEnd_2219192 := by exact prefixLift 2219192
  have htrace : WordTrace (prefixWord ++ tailWord_2219192) baseStart_2219192 baseEnd_2219192 := by
    simpa [prefixWord, tailWord_2219192, baseEnd_2219192] using wordTrace_append hprefix tailTrace_2219192
  have hstable : (prefixWord ++ tailWord_2219192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219192).length < 2 ^ (prefixWord ++ tailWord_2219192).sum := by decide
  have hdescent : baseEnd_2219192 < baseStart_2219192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219196 : List Nat := [2, 2, 2, 3, 2, 2, 3, 1, 5]
def baseStart_2219196 : Nat := 118140960795 + 2219196 * 2 ^ 59
def prefixEnd_2219196 : Nat := 4983230072969 + 3 ^ 40 * 2219196 * 2
def baseEnd_2219196 : Nat := 253225381007823248698691

theorem tailTrace_2219196 : CollatzResearch.WordTrace tailWord_2219196 prefixEnd_2219196 253225381007823248698691 := by
  unfold tailWord_2219196
  simp only [CollatzResearch.WordTrace]
  refine ⟨40470363834119687673750721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53960485112159583565000961 40470363834119687673750721)
  ·
    refine ⟨30352772875589765755313041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40470363834119687673750721 30352772875589765755313041)
    ·
      refine ⟨22764579656692324316484781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30352772875589765755313041 22764579656692324316484781)
      ·
        refine ⟨8536717371259621618681793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22764579656692324316484781 8536717371259621618681793)
        ·
          refine ⟨6402538028444716214011345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8536717371259621618681793 6402538028444716214011345)
          ·
            refine ⟨4801903521333537160508509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6402538028444716214011345 4801903521333537160508509)
            ·
              refine ⟨1800713820500076435190691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4801903521333537160508509 1800713820500076435190691)
              ·
                refine ⟨2701070730750114652786037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1800713820500076435190691 2701070730750114652786037)
                ·
                  refine ⟨253225381007823248698691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2701070730750114652786037 253225381007823248698691)
                  ·
                    rfl

theorem cell22_2219196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 5].length) (baseStart_2219196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219196 prefixEnd_2219196 := by exact prefixLift 2219196
  have htrace : WordTrace (prefixWord ++ tailWord_2219196) baseStart_2219196 baseEnd_2219196 := by
    simpa [prefixWord, tailWord_2219196, baseEnd_2219196] using wordTrace_append hprefix tailTrace_2219196
  have hstable : (prefixWord ++ tailWord_2219196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219196).length < 2 ^ (prefixWord ++ tailWord_2219196).sum := by decide
  have hdescent : baseEnd_2219196 < baseStart_2219196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219254 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_2219254 : Nat := 118140960795 + 2219254 * 2 ^ 59
def prefixEnd_2219254 : Nat := 4983230072969 + 3 ^ 40 * 2219254 * 2
def baseEnd_2219254 : Nat := 759695997608776928145895

theorem tailTrace_2219254 : CollatzResearch.WordTrace tailWord_2219254 prefixEnd_2219254 759695997608776928145895 := by
  unfold tailWord_2219254
  simp only [CollatzResearch.WordTrace]
  refine ⟨5058927693876828203319551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53961895401352834168741877 5058927693876828203319551)
  ·
    refine ⟨7588391540815242304979327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5058927693876828203319551 7588391540815242304979327)
    ·
      refine ⟨11382587311222863457468991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7588391540815242304979327 11382587311222863457468991)
      ·
        refine ⟨17073880966834295186203487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11382587311222863457468991 17073880966834295186203487)
        ·
          refine ⟨25610821450251442779305231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17073880966834295186203487 25610821450251442779305231)
          ·
            refine ⟨38416232175377164168957847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25610821450251442779305231 38416232175377164168957847)
            ·
              refine ⟨57624348263065746253436771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38416232175377164168957847 57624348263065746253436771)
              ·
                refine ⟨86436522394598619380155157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57624348263065746253436771 86436522394598619380155157)
                ·
                  refine ⟨4051711987246810283444773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86436522394598619380155157 4051711987246810283444773)
                  ·
                    refine ⟨759695997608776928145895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4051711987246810283444773 759695997608776928145895)
                    ·
                      rfl

theorem cell22_2219254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_2219254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219254 prefixEnd_2219254 := by exact prefixLift 2219254
  have htrace : WordTrace (prefixWord ++ tailWord_2219254) baseStart_2219254 baseEnd_2219254 := by
    simpa [prefixWord, tailWord_2219254, baseEnd_2219254] using wordTrace_append hprefix tailTrace_2219254
  have hstable : (prefixWord ++ tailWord_2219254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219254).length < 2 ^ (prefixWord ++ tailWord_2219254).sum := by decide
  have hdescent : baseEnd_2219254 < baseStart_2219254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219389 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 1, 6]
def baseStart_2219389 : Nat := 118140960795 + 2219389 * 2 ^ 59
def prefixEnd_2219389 : Nat := 4983230072969 + 3 ^ 40 * 2219389 * 2
def baseEnd_2219389 : Nat := 759742210867681576020481

theorem tailTrace_2219389 : CollatzResearch.WordTrace tailWord_2219389 prefixEnd_2219389 759742210867681576020481 := by
  unfold tailWord_2219389
  simp only [CollatzResearch.WordTrace]
  refine ⟨80947766956540169309277221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53965177971026779539518147 80947766956540169309277221)
  ·
    refine ⟨15177706304351281745489479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80947766956540169309277221 15177706304351281745489479)
    ·
      refine ⟨22766559456526922618234219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15177706304351281745489479 22766559456526922618234219)
      ·
        refine ⟨34149839184790383927351329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22766559456526922618234219 34149839184790383927351329)
        ·
          refine ⟨25612379388592787945513497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34149839184790383927351329 25612379388592787945513497)
          ·
            refine ⟨19209284541444590959135123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25612379388592787945513497 19209284541444590959135123)
            ·
              refine ⟨28813926812166886438702685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19209284541444590959135123 28813926812166886438702685)
              ·
                refine ⟨10805222554562582414513507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28813926812166886438702685 10805222554562582414513507)
                ·
                  refine ⟨16207833831843873621770261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10805222554562582414513507 16207833831843873621770261)
                  ·
                    refine ⟨759742210867681576020481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16207833831843873621770261 759742210867681576020481)
                    ·
                      rfl

theorem cell22_2219389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_2219389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219389 prefixEnd_2219389 := by exact prefixLift 2219389
  have htrace : WordTrace (prefixWord ++ tailWord_2219389) baseStart_2219389 baseEnd_2219389 := by
    simpa [prefixWord, tailWord_2219389, baseEnd_2219389] using wordTrace_append hprefix tailTrace_2219389
  have hstable : (prefixWord ++ tailWord_2219389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219389).length < 2 ^ (prefixWord ++ tailWord_2219389).sum := by decide
  have hdescent : baseEnd_2219389 < baseStart_2219389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219410 : List Nat := [3, 2, 3, 3, 1, 2, 1, 1, 6]
def baseStart_2219410 : Nat := 118140960795 + 2219410 * 2 ^ 59
def prefixEnd_2219410 : Nat := 4983230072969 + 3 ^ 40 * 2219410 * 2
def baseEnd_2219410 : Nat := 253249799865614840415139

theorem tailTrace_2219410 : CollatzResearch.WordTrace tailWord_2219410 prefixEnd_2219410 253249799865614840415139 := by
  unfold tailWord_2219410
  simp only [CollatzResearch.WordTrace]
  refine ⟨20237133222366022473947921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53965688592976059930527789 20237133222366022473947921)
  ·
    refine ⟨15177849916774516855460941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20237133222366022473947921 15177849916774516855460941)
    ·
      refine ⟨5691693718790443820797853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15177849916774516855460941 5691693718790443820797853)
      ·
        refine ⟨2134385144546416432799195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5691693718790443820797853 2134385144546416432799195)
        ·
          refine ⟨3201577716819624649198793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2134385144546416432799195 3201577716819624649198793)
          ·
            refine ⟨2401183287614718486899095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3201577716819624649198793 2401183287614718486899095)
            ·
              refine ⟨3601774931422077730348643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2401183287614718486899095 3601774931422077730348643)
              ·
                refine ⟨5402662397133116595522965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3601774931422077730348643 5402662397133116595522965)
                ·
                  refine ⟨253249799865614840415139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5402662397133116595522965 253249799865614840415139)
                  ·
                    rfl

theorem cell22_2219410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_2219410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219410 prefixEnd_2219410 := by exact prefixLift 2219410
  have htrace : WordTrace (prefixWord ++ tailWord_2219410) baseStart_2219410 baseEnd_2219410 := by
    simpa [prefixWord, tailWord_2219410, baseEnd_2219410] using wordTrace_append hprefix tailTrace_2219410
  have hstable : (prefixWord ++ tailWord_2219410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219410).length < 2 ^ (prefixWord ++ tailWord_2219410).sum := by decide
  have hdescent : baseEnd_2219410 < baseStart_2219410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219421 : List Nat := [1, 4, 2, 1, 3, 2, 2, 7]
def baseStart_2219421 : Nat := 118140960795 + 2219421 * 2 ^ 59
def prefixEnd_2219421 : Nat := 4983230072969 + 3 ^ 40 * 2219421 * 2
def baseEnd_2219421 : Nat := 84417018346849351024487

theorem tailTrace_2219421 : CollatzResearch.WordTrace tailWord_2219421 prefixEnd_2219421 84417018346849351024487 := by
  unfold tailWord_2219421
  simp only [CollatzResearch.WordTrace]
  refine ⟨80948934092424238774442117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53965956061616159182961411 80948934092424238774442117)
  ·
    refine ⟨15177925142329544770207897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80948934092424238774442117 15177925142329544770207897)
    ·
      refine ⟨11383443856747158577655923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15177925142329544770207897 11383443856747158577655923)
      ·
        refine ⟨17075165785120737866483885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11383443856747158577655923 17075165785120737866483885)
        ·
          refine ⟨6403187169420276699931457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17075165785120737866483885 6403187169420276699931457)
          ·
            refine ⟨4802390377065207524948593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6403187169420276699931457 4802390377065207524948593)
            ·
              refine ⟨3601792782798905643711445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4802390377065207524948593 3601792782798905643711445)
              ·
                refine ⟨84417018346849351024487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3601792782798905643711445 84417018346849351024487)
                ·
                  rfl

theorem cell22_2219421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 7].length) (baseStart_2219421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219421 prefixEnd_2219421 := by exact prefixLift 2219421
  have htrace : WordTrace (prefixWord ++ tailWord_2219421) baseStart_2219421 baseEnd_2219421 := by
    simpa [prefixWord, tailWord_2219421, baseEnd_2219421] using wordTrace_append hprefix tailTrace_2219421
  have hstable : (prefixWord ++ tailWord_2219421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219421).length < 2 ^ (prefixWord ++ tailWord_2219421).sum := by decide
  have hdescent : baseEnd_2219421 < baseStart_2219421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219436 : List Nat := [2, 2, 1, 1, 1, 1, 4, 4, 3, 3]
def baseStart_2219436 : Nat := 118140960795 + 2219436 * 2 ^ 59
def prefixEnd_2219436 : Nat := 4983230072969 + 3 ^ 40 * 2219436 * 2
def baseEnd_2219436 : Nat := 759758299928189120095337

theorem tailTrace_2219436 : CollatzResearch.WordTrace tailWord_2219436 prefixEnd_2219436 759758299928189120095337 := by
  unfold tailWord_2219436
  simp only [CollatzResearch.WordTrace]
  refine ⟨40474740593684948168119081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53966320791579930890825441 40474740593684948168119081)
  ·
    refine ⟨30356055445263711126089311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40474740593684948168119081 30356055445263711126089311)
    ·
      refine ⟨45534083167895566689133967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30356055445263711126089311 45534083167895566689133967)
      ·
        refine ⟨68301124751843350033700951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45534083167895566689133967 68301124751843350033700951)
        ·
          refine ⟨102451687127765025050551427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68301124751843350033700951 102451687127765025050551427)
          ·
            refine ⟨153677530691647537575827141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102451687127765025050551427 153677530691647537575827141)
            ·
              refine ⟨28814537004683913295467589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153677530691647537575827141 28814537004683913295467589)
              ·
                refine ⟨5402725688378233742900173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28814537004683913295467589 5402725688378233742900173)
                ·
                  refine ⟨2026022133141837653587565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5402725688378233742900173 2026022133141837653587565)
                  ·
                    refine ⟨759758299928189120095337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2026022133141837653587565 759758299928189120095337)
                    ·
                      rfl

theorem cell22_2219436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 3].length) (baseStart_2219436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219436 prefixEnd_2219436 := by exact prefixLift 2219436
  have htrace : WordTrace (prefixWord ++ tailWord_2219436) baseStart_2219436 baseEnd_2219436 := by
    simpa [prefixWord, tailWord_2219436, baseEnd_2219436] using wordTrace_append hprefix tailTrace_2219436
  have hstable : (prefixWord ++ tailWord_2219436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219436).length < 2 ^ (prefixWord ++ tailWord_2219436).sum := by decide
  have hdescent : baseEnd_2219436 < baseStart_2219436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219466 : List Nat := [3, 1, 2, 1, 2, 3, 1, 4, 5]
def baseStart_2219466 : Nat := 118140960795 + 2219466 * 2 ^ 59
def prefixEnd_2219466 : Nat := 4983230072969 + 3 ^ 40 * 2219466 * 2
def baseEnd_2219466 : Nat := 253256189847093013948415

theorem tailTrace_2219466 : CollatzResearch.WordTrace tailWord_2219466 prefixEnd_2219466 253256189847093013948415 := by
  unfold tailWord_2219466
  simp only [CollatzResearch.WordTrace]
  refine ⟨20237643844315302864957563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53967050251507474306553501 20237643844315302864957563)
  ·
    refine ⟨30356465766472954297436345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20237643844315302864957563 30356465766472954297436345)
    ·
      refine ⟨22767349324854715723077259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30356465766472954297436345 22767349324854715723077259)
      ·
        refine ⟨34151023987282073584615889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22767349324854715723077259 34151023987282073584615889)
        ·
          refine ⟨25613267990461555188461917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34151023987282073584615889 25613267990461555188461917)
          ·
            refine ⟨9604975496423083195673219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25613267990461555188461917 9604975496423083195673219)
            ·
              refine ⟨14407463244634624793509829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9604975496423083195673219 14407463244634624793509829)
              ·
                refine ⟨2701399358368992148783093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14407463244634624793509829 2701399358368992148783093)
                ·
                  refine ⟨253256189847093013948415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2701399358368992148783093 253256189847093013948415)
                  ·
                    rfl

theorem cell22_2219466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_2219466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219466 prefixEnd_2219466 := by exact prefixLift 2219466
  have htrace : WordTrace (prefixWord ++ tailWord_2219466) baseStart_2219466 baseEnd_2219466 := by
    simpa [prefixWord, tailWord_2219466, baseEnd_2219466] using wordTrace_append hprefix tailTrace_2219466
  have hstable : (prefixWord ++ tailWord_2219466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219466).length < 2 ^ (prefixWord ++ tailWord_2219466).sum := by decide
  have hdescent : baseEnd_2219466 < baseStart_2219466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219481 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 2, 5]
def baseStart_2219481 : Nat := 118140960795 + 2219481 * 2 ^ 59
def prefixEnd_2219481 : Nat := 4983230072969 + 3 ^ 40 * 2219481 * 2
def baseEnd_2219481 : Nat := 759773704347824002720199

theorem tailTrace_2219481 : CollatzResearch.WordTrace tailWord_2219481 prefixEnd_2219481 759773704347824002720199 := by
  unfold tailWord_2219481
  simp only [CollatzResearch.WordTrace]
  refine ⟨80951122472206869021626297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53967414981471246014417531 80951122472206869021626297)
  ·
    refine ⟨60713341854155151766219723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80951122472206869021626297 60713341854155151766219723)
    ·
      refine ⟨91070012781232727649329585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60713341854155151766219723 91070012781232727649329585)
      ·
        refine ⟨68302509585924545736997189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91070012781232727649329585 68302509585924545736997189)
        ·
          refine ⟨12806720547360852325686973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68302509585924545736997189 12806720547360852325686973)
          ·
            refine ⟨4802520205260319622132615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12806720547360852325686973 4802520205260319622132615)
            ·
              refine ⟨7203780307890479433198923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4802520205260319622132615 7203780307890479433198923)
              ·
                refine ⟨10805670461835719149798385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7203780307890479433198923 10805670461835719149798385)
                ·
                  refine ⟨8104252846376789362348789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10805670461835719149798385 8104252846376789362348789)
                  ·
                    refine ⟨759773704347824002720199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8104252846376789362348789 759773704347824002720199)
                    ·
                      rfl

theorem cell22_2219481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 5].length) (baseStart_2219481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219481 prefixEnd_2219481 := by exact prefixLift 2219481
  have htrace : WordTrace (prefixWord ++ tailWord_2219481) baseStart_2219481 baseEnd_2219481 := by
    simpa [prefixWord, tailWord_2219481, baseEnd_2219481] using wordTrace_append hprefix tailTrace_2219481
  have hstable : (prefixWord ++ tailWord_2219481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219481).length < 2 ^ (prefixWord ++ tailWord_2219481).sum := by decide
  have hdescent : baseEnd_2219481 < baseStart_2219481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219496 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 3, 4]
def baseStart_2219496 : Nat := 118140960795 + 2219496 * 2 ^ 59
def prefixEnd_2219496 : Nat := 4983230072969 + 3 ^ 40 * 2219496 * 2
def baseEnd_2219496 : Nat := 759778839154368963595153

theorem tailTrace_2219496 : CollatzResearch.WordTrace tailWord_2219496 prefixEnd_2219496 759778839154368963595153 := by
  unfold tailWord_2219496
  simp only [CollatzResearch.WordTrace]
  refine ⟨40475834783576263291711171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53967779711435017722281561 40475834783576263291711171)
  ·
    refine ⟨60713752175364394937566757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40475834783576263291711171 60713752175364394937566757)
    ·
      refine ⟨11383828532880824050793767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60713752175364394937566757 11383828532880824050793767)
      ·
        refine ⟨17075742799321236076190651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11383828532880824050793767 17075742799321236076190651)
        ·
          refine ⟨25613614198981854114285977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17075742799321236076190651 25613614198981854114285977)
          ·
            refine ⟨19210210649236390585714483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25613614198981854114285977 19210210649236390585714483)
            ·
              refine ⟨28815315973854585878571725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19210210649236390585714483 28815315973854585878571725)
              ·
                refine ⟨10805743490195469704464397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28815315973854585878571725 10805743490195469704464397)
                ·
                  refine ⟨4052153808823301139174149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10805743490195469704464397 4052153808823301139174149)
                  ·
                    refine ⟨759778839154368963595153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4052153808823301139174149 759778839154368963595153)
                    ·
                      rfl

theorem cell22_2219496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_2219496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219496 prefixEnd_2219496 := by exact prefixLift 2219496
  have htrace : WordTrace (prefixWord ++ tailWord_2219496) baseStart_2219496 baseEnd_2219496 := by
    simpa [prefixWord, tailWord_2219496, baseEnd_2219496] using wordTrace_append hprefix tailTrace_2219496
  have hstable : (prefixWord ++ tailWord_2219496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219496).length < 2 ^ (prefixWord ++ tailWord_2219496).sum := by decide
  have hdescent : baseEnd_2219496 < baseStart_2219496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219528 : List Nat := [2, 1, 3, 2, 1, 1, 4, 4, 4]
def baseStart_2219528 : Nat := 118140960795 + 2219528 * 2 ^ 59
def prefixEnd_2219528 : Nat := 4983230072969 + 3 ^ 40 * 2219528 * 2
def baseEnd_2219528 : Nat := 253263264469443848931685

theorem tailTrace_2219528 : CollatzResearch.WordTrace tailWord_2219528 prefixEnd_2219528 253263264469443848931685 := by
  unfold tailWord_2219528
  simp only [CollatzResearch.WordTrace]
  refine ⟨40476418351518298024293619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53968557802024397365724825 40476418351518298024293619)
  ·
    refine ⟨60714627527277447036440429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40476418351518298024293619 60714627527277447036440429)
    ·
      refine ⟨22767985322729042638665161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60714627527277447036440429 22767985322729042638665161)
      ·
        refine ⟨17075988992046781978998871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22767985322729042638665161 17075988992046781978998871)
        ·
          refine ⟨25613983488070172968498307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17075988992046781978998871 25613983488070172968498307)
          ·
            refine ⟨38420975232105259452747461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25613983488070172968498307 38420975232105259452747461)
            ·
              refine ⟨7203932856019736147390149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38420975232105259452747461 7203932856019736147390149)
              ·
                refine ⟨1350737410503700527635653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7203932856019736147390149 1350737410503700527635653)
                ·
                  refine ⟨253263264469443848931685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1350737410503700527635653 253263264469443848931685)
                  ·
                    rfl

theorem cell22_2219528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 4].length) (baseStart_2219528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219528 prefixEnd_2219528 := by exact prefixLift 2219528
  have htrace : WordTrace (prefixWord ++ tailWord_2219528) baseStart_2219528 baseEnd_2219528 := by
    simpa [prefixWord, tailWord_2219528, baseEnd_2219528] using wordTrace_append hprefix tailTrace_2219528
  have hstable : (prefixWord ++ tailWord_2219528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219528).length < 2 ^ (prefixWord ++ tailWord_2219528).sum := by decide
  have hdescent : baseEnd_2219528 < baseStart_2219528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219541 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 1, 6]
def baseStart_2219541 : Nat := 118140960795 + 2219541 * 2 ^ 59
def prefixEnd_2219541 : Nat := 4983230072969 + 3 ^ 40 * 2219541 * 2
def baseEnd_2219541 : Nat := 759794243574003846220015

theorem tailTrace_2219541 : CollatzResearch.WordTrace tailWord_2219541 prefixEnd_2219541 759794243574003846220015 := by
  unfold tailWord_2219541
  simp only [CollatzResearch.WordTrace]
  refine ⟨80953310851989499268810477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53968873901326332845873651 80953310851989499268810477)
  ·
    refine ⟨30357491569496062225803929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80953310851989499268810477 30357491569496062225803929)
    ·
      refine ⟨22768118677122046669352947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30357491569496062225803929 22768118677122046669352947)
      ·
        refine ⟨34152178015683070004029421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22768118677122046669352947 34152178015683070004029421)
        ·
          refine ⟨12807066755881151251511033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34152178015683070004029421 12807066755881151251511033)
          ·
            refine ⟨9605300066910863438633275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12807066755881151251511033 9605300066910863438633275)
            ·
              refine ⟨14407950100366295157949913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9605300066910863438633275 14407950100366295157949913)
              ·
                refine ⟨10805962575274721368462435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14407950100366295157949913 10805962575274721368462435)
                ·
                  refine ⟨16208943862912082052693653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10805962575274721368462435 16208943862912082052693653)
                  ·
                    refine ⟨759794243574003846220015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16208943862912082052693653 759794243574003846220015)
                    ·
                      rfl

theorem cell22_2219541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_2219541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219541 prefixEnd_2219541 := by exact prefixLift 2219541
  have htrace : WordTrace (prefixWord ++ tailWord_2219541) baseStart_2219541 baseEnd_2219541 := by
    simpa [prefixWord, tailWord_2219541, baseEnd_2219541] using wordTrace_append hprefix tailTrace_2219541
  have hstable : (prefixWord ++ tailWord_2219541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219541).length < 2 ^ (prefixWord ++ tailWord_2219541).sum := by decide
  have hdescent : baseEnd_2219541 < baseStart_2219541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219616 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 4, 5]
def baseStart_2219616 : Nat := 118140960795 + 2219616 * 2 ^ 59
def prefixEnd_2219616 : Nat := 4983230072969 + 3 ^ 40 * 2219616 * 2
def baseEnd_2219616 : Nat := 759819917606728650594785

theorem tailTrace_2219616 : CollatzResearch.WordTrace tailWord_2219616 prefixEnd_2219616 759819917606728650594785 := by
  unfold tailWord_2219616
  simp only [CollatzResearch.WordTrace]
  refine ⟨40478023163358893538895351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53970697551145191385193801 40478023163358893538895351)
  ·
    refine ⟨60717034745038340308343027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40478023163358893538895351 60717034745038340308343027)
    ·
      refine ⟨91075552117557510462514541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60717034745038340308343027 91075552117557510462514541)
      ·
        refine ⟨34153332044084066423442953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91075552117557510462514541 34153332044084066423442953)
        ·
          refine ⟨25614999033063049817582215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34153332044084066423442953 25614999033063049817582215)
          ·
            refine ⟨38422498549594574726373323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25614999033063049817582215 38422498549594574726373323)
            ·
              refine ⟨57633747824391862089559985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38422498549594574726373323 57633747824391862089559985)
              ·
                refine ⟨43225310868293896567169989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57633747824391862089559985 43225310868293896567169989)
                ·
                  refine ⟨8104745787805105606344373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43225310868293896567169989 8104745787805105606344373)
                  ·
                    refine ⟨759819917606728650594785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8104745787805105606344373 759819917606728650594785)
                    ·
                      rfl

theorem cell22_2219616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_2219616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219616 prefixEnd_2219616 := by exact prefixLift 2219616
  have htrace : WordTrace (prefixWord ++ tailWord_2219616) baseStart_2219616 baseEnd_2219616 := by
    simpa [prefixWord, tailWord_2219616, baseEnd_2219616] using wordTrace_append hprefix tailTrace_2219616
  have hstable : (prefixWord ++ tailWord_2219616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219616).length < 2 ^ (prefixWord ++ tailWord_2219616).sum := by decide
  have hdescent : baseEnd_2219616 < baseStart_2219616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219680 : List Nat := [2, 1, 1, 4, 3, 1, 1, 5, 4]
def baseStart_2219680 : Nat := 118140960795 + 2219680 * 2 ^ 59
def prefixEnd_2219680 : Nat := 4983230072969 + 3 ^ 40 * 2219680 * 2
def baseEnd_2219680 : Nat := 253280608704884605664863

theorem tailTrace_2219680 : CollatzResearch.WordTrace tailWord_2219680 prefixEnd_2219680 253280608704884605664863 := by
  unfold tailWord_2219680
  simp only [CollatzResearch.WordTrace]
  refine ⟨40479190299242963004060247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53972253732323950672080329 40479190299242963004060247)
  ·
    refine ⟨60718785448864444506090371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40479190299242963004060247 60718785448864444506090371)
    ·
      refine ⟨91078178173296666759135557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60718785448864444506090371 91078178173296666759135557)
      ·
        refine ⟨17077158407493125017337917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91078178173296666759135557 17077158407493125017337917)
        ·
          refine ⟨6403934402809921881501719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17077158407493125017337917 6403934402809921881501719)
          ·
            refine ⟨9605901604214882822252579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6403934402809921881501719 9605901604214882822252579)
            ·
              refine ⟨14408852406322324233378869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9605901604214882822252579 14408852406322324233378869)
              ·
                refine ⟨1350829913092717896879269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14408852406322324233378869 1350829913092717896879269)
                ·
                  refine ⟨253280608704884605664863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1350829913092717896879269 253280608704884605664863)
                  ·
                    rfl

theorem cell22_2219680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 4].length) (baseStart_2219680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219680 prefixEnd_2219680 := by exact prefixLift 2219680
  have htrace : WordTrace (prefixWord ++ tailWord_2219680) baseStart_2219680 baseEnd_2219680 := by
    simpa [prefixWord, tailWord_2219680, baseEnd_2219680] using wordTrace_append hprefix tailTrace_2219680
  have hstable : (prefixWord ++ tailWord_2219680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219680).length < 2 ^ (prefixWord ++ tailWord_2219680).sum := by decide
  have hdescent : baseEnd_2219680 < baseStart_2219680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219712 : List Nat := [2, 1, 1, 2, 4, 1, 5, 1, 2, 3]
def baseStart_2219712 : Nat := 118140960795 + 2219712 * 2 ^ 59
def prefixEnd_2219712 : Nat := 4983230072969 + 3 ^ 40 * 2219712 * 2
def baseEnd_2219712 : Nat := 759852780368616400194491

theorem tailTrace_2219712 : CollatzResearch.WordTrace tailWord_2219712 prefixEnd_2219712 759852780368616400194491 := by
  unfold tailWord_2219712
  simp only [CollatzResearch.WordTrace]
  refine ⟨40479773867184997736642695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53973031822913330315523593 40479773867184997736642695)
  ·
    refine ⟨60719660800777496604964043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40479773867184997736642695 60719660800777496604964043)
    ·
      refine ⟨91079491201166244907446065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60719660800777496604964043 91079491201166244907446065)
      ·
        refine ⟨68309618400874683680584549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91079491201166244907446065 68309618400874683680584549)
        ·
          refine ⟨12808053450164003190109603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68309618400874683680584549 12808053450164003190109603)
          ·
            refine ⟨19212080175246004785164405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12808053450164003190109603 19212080175246004785164405)
            ·
              refine ⟨1801132516429312948609163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19212080175246004785164405 1801132516429312948609163)
              ·
                refine ⟨2701698774643969422913745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1801132516429312948609163 2701698774643969422913745)
                ·
                  refine ⟨2026274080982977067185309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2701698774643969422913745 2026274080982977067185309)
                  ·
                    refine ⟨759852780368616400194491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2026274080982977067185309 759852780368616400194491)
                    ·
                      rfl

theorem cell22_2219712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 2, 3].length) (baseStart_2219712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219712 prefixEnd_2219712 := by exact prefixLift 2219712
  have htrace : WordTrace (prefixWord ++ tailWord_2219712) baseStart_2219712 baseEnd_2219712 := by
    simpa [prefixWord, tailWord_2219712, baseEnd_2219712] using wordTrace_append hprefix tailTrace_2219712
  have hstable : (prefixWord ++ tailWord_2219712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219712).length < 2 ^ (prefixWord ++ tailWord_2219712).sum := by decide
  have hdescent : baseEnd_2219712 < baseStart_2219712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219753 : List Nat := [1, 2, 1, 1, 1, 2, 3, 6, 5]
def baseStart_2219753 : Nat := 118140960795 + 2219753 * 2 ^ 59
def prefixEnd_2219753 : Nat := 4983230072969 + 3 ^ 40 * 2219753 * 2
def baseEnd_2219753 : Nat := 253288938502168653306455

theorem tailTrace_2219753 : CollatzResearch.WordTrace tailWord_2219753 prefixEnd_2219753 253288938502168653306455 := by
  unfold tailWord_2219753
  simp only [CollatzResearch.WordTrace]
  refine ⟨80961043127221459475527913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53974028751480972983685275 80961043127221459475527913)
  ·
    refine ⟨60720782345416094606645935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80961043127221459475527913 60720782345416094606645935)
    ·
      refine ⟨91081173518124141909968903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60720782345416094606645935 91081173518124141909968903)
      ·
        refine ⟨136621760277186212864953355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91081173518124141909968903 136621760277186212864953355)
        ·
          refine ⟨204932640415779319297430033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136621760277186212864953355 204932640415779319297430033)
          ·
            refine ⟨153699480311834489473072525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204932640415779319297430033 153699480311834489473072525)
            ·
              refine ⟨57637305116937933552402197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153699480311834489473072525 57637305116937933552402197)
              ·
                refine ⟨2701748677356465635268853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57637305116937933552402197 2701748677356465635268853)
                ·
                  refine ⟨253288938502168653306455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2701748677356465635268853 253288938502168653306455)
                  ·
                    rfl

theorem cell22_2219753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 5].length) (baseStart_2219753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219753 prefixEnd_2219753 := by exact prefixLift 2219753
  have htrace : WordTrace (prefixWord ++ tailWord_2219753) baseStart_2219753 baseEnd_2219753 := by
    simpa [prefixWord, tailWord_2219753, baseEnd_2219753] using wordTrace_append hprefix tailTrace_2219753
  have hstable : (prefixWord ++ tailWord_2219753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219753).length < 2 ^ (prefixWord ++ tailWord_2219753).sum := by decide
  have hdescent : baseEnd_2219753 < baseStart_2219753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219757 : List Nat := [1, 5, 1, 2, 1, 2, 3, 1, 3, 3]
def baseStart_2219757 : Nat := 118140960795 + 2219757 * 2 ^ 59
def prefixEnd_2219757 : Nat := 4983230072969 + 3 ^ 40 * 2219757 * 2
def baseEnd_2219757 : Nat := 759868184788251282819353

theorem tailTrace_2219757 : CollatzResearch.WordTrace tailWord_2219757 prefixEnd_2219757 759868184788251282819353 := by
  unfold tailWord_2219757
  simp only [CollatzResearch.WordTrace]
  refine ⟨80961189019206968158673525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53974126012804645439115683 80961189019206968158673525)
  ·
    refine ⟨7590111470550653264875643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80961189019206968158673525 7590111470550653264875643)
    ·
      refine ⟨11385167205825979897313465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7590111470550653264875643 11385167205825979897313465)
      ·
        refine ⟨8538875404369484922985099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11385167205825979897313465 8538875404369484922985099)
        ·
          refine ⟨12808313106554227384477649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8538875404369484922985099 12808313106554227384477649)
          ·
            refine ⟨9606234829915670538358237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12808313106554227384477649 9606234829915670538358237)
            ·
              refine ⟨3602338061218376451884339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9606234829915670538358237 3602338061218376451884339)
              ·
                refine ⟨5403507091827564677826509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3602338061218376451884339 5403507091827564677826509)
                ·
                  refine ⟨2026315159435336754184941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5403507091827564677826509 2026315159435336754184941)
                  ·
                    refine ⟨759868184788251282819353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2026315159435336754184941 759868184788251282819353)
                    ·
                      rfl

theorem cell22_2219757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_2219757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219757 prefixEnd_2219757 := by exact prefixLift 2219757
  have htrace : WordTrace (prefixWord ++ tailWord_2219757) baseStart_2219757 baseEnd_2219757 := by
    simpa [prefixWord, tailWord_2219757, baseEnd_2219757] using wordTrace_append hprefix tailTrace_2219757
  have hstable : (prefixWord ++ tailWord_2219757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219757).length < 2 ^ (prefixWord ++ tailWord_2219757).sum := by decide
  have hdescent : baseEnd_2219757 < baseStart_2219757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219800 : List Nat := [2, 1, 2, 3, 1, 1, 2, 5, 1, 4]
def baseStart_2219800 : Nat := 118140960795 + 2219800 * 2 ^ 59
def prefixEnd_2219800 : Nat := 4983230072969 + 3 ^ 40 * 2219800 * 2
def baseEnd_2219800 : Nat := 759882904567013503994221

theorem tailTrace_2219800 : CollatzResearch.WordTrace tailWord_2219800 prefixEnd_2219800 759882904567013503994221 := by
  unfold tailWord_2219800
  simp only [CollatzResearch.WordTrace]
  refine ⟨40481378679025593251244427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53975171572034124334992569 40481378679025593251244427)
  ·
    refine ⟨60722068018538389876866641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40481378679025593251244427 60722068018538389876866641)
    ·
      refine ⟨45541551013903792407649981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60722068018538389876866641 45541551013903792407649981)
      ·
        refine ⟨17078081630213922152868743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45541551013903792407649981 17078081630213922152868743)
        ·
          refine ⟨25617122445320883229303115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17078081630213922152868743 25617122445320883229303115)
          ·
            refine ⟨38425683667981324843954673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25617122445320883229303115 38425683667981324843954673)
            ·
              refine ⟨28819262750985993632966005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38425683667981324843954673 28819262750985993632966005)
              ·
                refine ⟨2701805882904936903090563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28819262750985993632966005 2701805882904936903090563)
                ·
                  refine ⟨4052708824357405354635845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2701805882904936903090563 4052708824357405354635845)
                  ·
                    refine ⟨759882904567013503994221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4052708824357405354635845 759882904567013503994221)
                    ·
                      rfl

theorem cell22_2219800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_2219800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219800 prefixEnd_2219800 := by exact prefixLift 2219800
  have htrace : WordTrace (prefixWord ++ tailWord_2219800) baseStart_2219800 baseEnd_2219800 := by
    simpa [prefixWord, tailWord_2219800, baseEnd_2219800] using wordTrace_append hprefix tailTrace_2219800
  have hstable : (prefixWord ++ tailWord_2219800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219800).length < 2 ^ (prefixWord ++ tailWord_2219800).sum := by decide
  have hdescent : baseEnd_2219800 < baseStart_2219800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219860 : List Nat := [2, 4, 1, 1, 3, 2, 9]
def baseStart_2219860 : Nat := 118140960795 + 2219860 * 2 ^ 59
def prefixEnd_2219860 : Nat := 4983230072969 + 3 ^ 40 * 2219860 * 2
def baseEnd_2219860 : Nat := 28144571992340494351631

theorem tailTrace_2219860 : CollatzResearch.WordTrace tailWord_2219860 prefixEnd_2219860 28144571992340494351631 := by
  unfold tailWord_2219860
  simp only [CollatzResearch.WordTrace]
  refine ⟨40482472868916908374836517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53976630491889211166448689 40482472868916908374836517)
  ·
    refine ⟨7590463662921920320281847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40482472868916908374836517 7590463662921920320281847)
    ·
      refine ⟨11385695494382880480422771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7590463662921920320281847 11385695494382880480422771)
      ·
        refine ⟨17078543241574320720634157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11385695494382880480422771 17078543241574320720634157)
        ·
          refine ⟨6404453715590370270237809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17078543241574320720634157 6404453715590370270237809)
          ·
            refine ⟨4803340286692777702678357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6404453715590370270237809 4803340286692777702678357)
            ·
              refine ⟨28144571992340494351631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4803340286692777702678357 28144571992340494351631)
              ·
                rfl

theorem cell22_2219860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 9].length) (baseStart_2219860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219860 prefixEnd_2219860 := by exact prefixLift 2219860
  have htrace : WordTrace (prefixWord ++ tailWord_2219860) baseStart_2219860 baseEnd_2219860 := by
    simpa [prefixWord, tailWord_2219860, baseEnd_2219860] using wordTrace_append hprefix tailTrace_2219860
  have hstable : (prefixWord ++ tailWord_2219860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219860).length < 2 ^ (prefixWord ++ tailWord_2219860).sum := by decide
  have hdescent : baseEnd_2219860 < baseStart_2219860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219922 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 7]
def baseStart_2219922 : Nat := 118140960795 + 2219922 * 2 ^ 59
def prefixEnd_2219922 : Nat := 4983230072969 + 3 ^ 40 * 2219922 * 2
def baseEnd_2219922 : Nat := 253308222553415284147949

theorem tailTrace_2219922 : CollatzResearch.WordTrace tailWord_2219922 prefixEnd_2219922 253308222553415284147949 := by
  unfold tailWord_2219922
  simp only [CollatzResearch.WordTrace]
  refine ⟨20241801765902300334607505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53978138042406134225620013 20241801765902300334607505)
  ·
    refine ⟨15181351324426725250955629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20241801765902300334607505 15181351324426725250955629)
    ·
      refine ⟨5693006746660021969108361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15181351324426725250955629 5693006746660021969108361)
      ·
        refine ⟨4269755059995016476831271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5693006746660021969108361 4269755059995016476831271)
        ·
          refine ⟨6404632589992524715246907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4269755059995016476831271 6404632589992524715246907)
          ·
            refine ⟨9606948884988787072870361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6404632589992524715246907 9606948884988787072870361)
            ·
              refine ⟨7205211663741590304652771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9606948884988787072870361 7205211663741590304652771)
              ·
                refine ⟨10807817495612385456979157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7205211663741590304652771 10807817495612385456979157)
                ·
                  refine ⟨253308222553415284147949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10807817495612385456979157 253308222553415284147949)
                  ·
                    rfl

theorem cell22_2219922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_2219922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219922 prefixEnd_2219922 := by exact prefixLift 2219922
  have htrace : WordTrace (prefixWord ++ tailWord_2219922) baseStart_2219922 baseEnd_2219922 := by
    simpa [prefixWord, tailWord_2219922, baseEnd_2219922] using wordTrace_append hprefix tailTrace_2219922
  have hstable : (prefixWord ++ tailWord_2219922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219922).length < 2 ^ (prefixWord ++ tailWord_2219922).sum := by decide
  have hdescent : baseEnd_2219922 < baseStart_2219922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219967 : List Nat := [1, 1, 2, 2, 2, 1, 4, 5, 4]
def baseStart_2219967 : Nat := 118140960795 + 2219967 * 2 ^ 59
def prefixEnd_2219967 : Nat := 4983230072969 + 3 ^ 40 * 2219967 * 2
def baseEnd_2219967 : Nat := 253313357359960245022903

theorem tailTrace_2219967 : CollatzResearch.WordTrace tailWord_2219967 prefixEnd_2219967 253313357359960245022903 := by
  unfold tailWord_2219967
  simp only [CollatzResearch.WordTrace]
  refine ⟨80968848348446174023818155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53979232232297449349212103 80968848348446174023818155)
  ·
    refine ⟨121453272522669261035727233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80968848348446174023818155 121453272522669261035727233)
    ·
      refine ⟨91089954392001945776795425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121453272522669261035727233 91089954392001945776795425)
      ·
        refine ⟨68317465794001459332596569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91089954392001945776795425 68317465794001459332596569)
        ·
          refine ⟨51238099345501094499447427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68317465794001459332596569 51238099345501094499447427)
          ·
            refine ⟨76857149018251641749171141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51238099345501094499447427 76857149018251641749171141)
            ·
              refine ⟨14410715440922182827969589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76857149018251641749171141 14410715440922182827969589)
              ·
                refine ⟨1351004572586454640122149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14410715440922182827969589 1351004572586454640122149)
                ·
                  refine ⟨253313357359960245022903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1351004572586454640122149 253313357359960245022903)
                  ·
                    rfl

theorem cell22_2219967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 4].length) (baseStart_2219967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219967 prefixEnd_2219967 := by exact prefixLift 2219967
  have htrace : WordTrace (prefixWord ++ tailWord_2219967) baseStart_2219967 baseEnd_2219967 := by
    simpa [prefixWord, tailWord_2219967, baseEnd_2219967] using wordTrace_append hprefix tailTrace_2219967
  have hstable : (prefixWord ++ tailWord_2219967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219967).length < 2 ^ (prefixWord ++ tailWord_2219967).sum := by decide
  have hdescent : baseEnd_2219967 < baseStart_2219967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219984 : List Nat := [2, 1, 1, 1, 1, 2, 8, 2, 4]
def baseStart_2219984 : Nat := 118140960795 + 2219984 * 2 ^ 59
def prefixEnd_2219984 : Nat := 4983230072969 + 3 ^ 40 * 2219984 * 2
def baseEnd_2219984 : Nat := 253315297175766119131219

theorem tailTrace_2219984 : CollatzResearch.WordTrace tailWord_2219984 prefixEnd_2219984 253315297175766119131219 := by
  unfold tailWord_2219984
  simp only [CollatzResearch.WordTrace]
  refine ⟨40484734194692292963593503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53979645592923057284791337 40484734194692292963593503)
  ·
    refine ⟨60727101292038439445390255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40484734194692292963593503 60727101292038439445390255)
    ·
      refine ⟨91090651938057659168085383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60727101292038439445390255 91090651938057659168085383)
      ·
        refine ⟨136635977907086488752128075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91090651938057659168085383 136635977907086488752128075)
        ·
          refine ⟨204953966860629733128192113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136635977907086488752128075 204953966860629733128192113)
          ·
            refine ⟨153715475145472299846144085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204953966860629733128192113 153715475145472299846144085)
            ·
              refine ⟨1801353224361003513822001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 153715475145472299846144085 1801353224361003513822001)
              ·
                refine ⟨1351014918270752635366501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1801353224361003513822001 1351014918270752635366501)
                ·
                  refine ⟨253315297175766119131219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1351014918270752635366501 253315297175766119131219)
                  ·
                    rfl

theorem cell22_2219984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 4].length) (baseStart_2219984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219984 prefixEnd_2219984 := by exact prefixLift 2219984
  have htrace : WordTrace (prefixWord ++ tailWord_2219984) baseStart_2219984 baseEnd_2219984 := by
    simpa [prefixWord, tailWord_2219984, baseEnd_2219984] using wordTrace_append hprefix tailTrace_2219984
  have hstable : (prefixWord ++ tailWord_2219984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219984).length < 2 ^ (prefixWord ++ tailWord_2219984).sum := by decide
  have hdescent : baseEnd_2219984 < baseStart_2219984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219999 : List Nat := [1, 1, 2, 3, 4, 1, 2, 3, 2, 3]
def baseStart_2219999 : Nat := 118140960795 + 2219999 * 2 ^ 59
def prefixEnd_2219999 : Nat := 4983230072969 + 3 ^ 40 * 2219999 * 2
def baseEnd_2219999 : Nat := 759951026333843318268611

theorem tailTrace_2219999 : CollatzResearch.WordTrace tailWord_2219999 prefixEnd_2219999 759951026333843318268611 := by
  unfold tailWord_2219999
  simp only [CollatzResearch.WordTrace]
  refine ⟨80970015484330243488983051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53980010322886828992655367 80970015484330243488983051)
  ·
    refine ⟨121455023226495365233474577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80970015484330243488983051 121455023226495365233474577)
    ·
      refine ⟨91091267419871523925105933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121455023226495365233474577 91091267419871523925105933)
      ·
        refine ⟨34159225282451821471914725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91091267419871523925105933 34159225282451821471914725)
        ·
          refine ⟨6404854740459716525984011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34159225282451821471914725 6404854740459716525984011)
          ·
            refine ⟨9607282110689574788976017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6404854740459716525984011 9607282110689574788976017)
            ·
              refine ⟨7205461583017181091732013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9607282110689574788976017 7205461583017181091732013)
              ·
                refine ⟨2702048093631442909399505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7205461583017181091732013 2702048093631442909399505)
                ·
                  refine ⟨2026536070223582182049629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2702048093631442909399505 2026536070223582182049629)
                  ·
                    refine ⟨759951026333843318268611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2026536070223582182049629 759951026333843318268611)
                    ·
                      rfl

theorem cell22_2219999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 3].length) (baseStart_2219999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2219999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2219999 prefixEnd_2219999 := by exact prefixLift 2219999
  have htrace : WordTrace (prefixWord ++ tailWord_2219999) baseStart_2219999 baseEnd_2219999 := by
    simpa [prefixWord, tailWord_2219999, baseEnd_2219999] using wordTrace_append hprefix tailTrace_2219999
  have hstable : (prefixWord ++ tailWord_2219999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219999).length < 2 ^ (prefixWord ++ tailWord_2219999).sum := by decide
  have hdescent : baseEnd_2219999 < baseStart_2219999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220014 : List Nat := [4, 1, 2, 1, 3, 1, 3, 1, 2, 4]
def baseStart_2220014 : Nat := 118140960795 + 2220014 * 2 ^ 59
def prefixEnd_2220014 : Nat := 4983230072969 + 3 ^ 40 * 2220014 * 2
def baseEnd_2220014 : Nat := 759956161140388279143565

theorem tailTrace_2220014 : CollatzResearch.WordTrace tailWord_2220014 prefixEnd_2220014 759956161140388279143565 := by
  unfold tailWord_2220014
  simp only [CollatzResearch.WordTrace]
  refine ⟨10121320322409487631347387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53980375052850600700519397 10121320322409487631347387)
  ·
    refine ⟨15181980483614231447021081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10121320322409487631347387 15181980483614231447021081)
    ·
      refine ⟨11386485362710673585265811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15181980483614231447021081 11386485362710673585265811)
      ·
        refine ⟨17079728044066010377898717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11386485362710673585265811 17079728044066010377898717)
        ·
          refine ⟨6404898016524753891712019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17079728044066010377898717 6404898016524753891712019)
          ·
            refine ⟨9607347024787130837568029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6404898016524753891712019 9607347024787130837568029)
            ·
              refine ⟨3602755134295174064088011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9607347024787130837568029 3602755134295174064088011)
              ·
                refine ⟨5404132701442761096132017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3602755134295174064088011 5404132701442761096132017)
                ·
                  refine ⟨4053099526082070822099013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5404132701442761096132017 4053099526082070822099013)
                  ·
                    refine ⟨759956161140388279143565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4053099526082070822099013 759956161140388279143565)
                    ·
                      rfl

theorem cell22_2220014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_2220014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220014 prefixEnd_2220014 := by exact prefixLift 2220014
  have htrace : WordTrace (prefixWord ++ tailWord_2220014) baseStart_2220014 baseEnd_2220014 := by
    simpa [prefixWord, tailWord_2220014, baseEnd_2220014] using wordTrace_append hprefix tailTrace_2220014
  have hstable : (prefixWord ++ tailWord_2220014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220014).length < 2 ^ (prefixWord ++ tailWord_2220014).sum := by decide
  have hdescent : baseEnd_2220014 < baseStart_2220014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220044 : List Nat := [2, 2, 1, 2, 3, 1, 4, 1, 3, 3]
def baseStart_2220044 : Nat := 118140960795 + 2220044 * 2 ^ 59
def prefixEnd_2220044 : Nat := 4983230072969 + 3 ^ 40 * 2220044 * 2
def baseEnd_2220044 : Nat := 759966430753478200893473

theorem tailTrace_2220044 : CollatzResearch.WordTrace tailWord_2220044 prefixEnd_2220044 759966430753478200893473 := by
  unfold tailWord_2220044
  simp only [CollatzResearch.WordTrace]
  refine ⟨40485828384583608087185593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53981104512778144116247457 40485828384583608087185593)
  ·
    refine ⟨30364371288437706065389195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40485828384583608087185593 30364371288437706065389195)
    ·
      refine ⟨45546556932656559098083793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30364371288437706065389195 45546556932656559098083793)
      ·
        refine ⟨34159917699492419323562845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45546556932656559098083793 34159917699492419323562845)
        ·
          refine ⟨12809969137309657246336067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34159917699492419323562845 12809969137309657246336067)
          ·
            refine ⟨19214953705964485869504101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12809969137309657246336067 19214953705964485869504101)
            ·
              refine ⟨3602803819868341100532019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19214953705964485869504101 3602803819868341100532019)
              ·
                refine ⟨5404205729802511650798029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3602803819868341100532019 5404205729802511650798029)
                ·
                  refine ⟨2026577148675941869049261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5404205729802511650798029 2026577148675941869049261)
                  ·
                    refine ⟨759966430753478200893473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2026577148675941869049261 759966430753478200893473)
                    ·
                      rfl

theorem cell22_2220044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 3, 3].length) (baseStart_2220044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220044 prefixEnd_2220044 := by exact prefixLift 2220044
  have htrace : WordTrace (prefixWord ++ tailWord_2220044) baseStart_2220044 baseEnd_2220044 := by
    simpa [prefixWord, tailWord_2220044, baseEnd_2220044] using wordTrace_append hprefix tailTrace_2220044
  have hstable : (prefixWord ++ tailWord_2220044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220044).length < 2 ^ (prefixWord ++ tailWord_2220044).sum := by decide
  have hdescent : baseEnd_2220044 < baseStart_2220044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220078 : List Nat := [4, 1, 3, 1, 1, 2, 3, 3, 1, 3]
def baseStart_2220078 : Nat := 118140960795 + 2220078 * 2 ^ 59
def prefixEnd_2220078 : Nat := 4983230072969 + 3 ^ 40 * 2220078 * 2
def baseEnd_2220078 : Nat := 759978069648313445543369

theorem tailTrace_2220078 : CollatzResearch.WordTrace tailWord_2220078 prefixEnd_2220078 759978069648313445543369 := by
  unfold tailWord_2220078
  simp only [CollatzResearch.WordTrace]
  refine ⟨10121612106380504997638611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53981931234029359987405925 10121612106380504997638611)
  ·
    refine ⟨15182418159570757496457917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10121612106380504997638611 15182418159570757496457917)
    ·
      refine ⟨5693406809839034061171719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15182418159570757496457917 5693406809839034061171719)
      ·
        refine ⟨8540110214758551091757579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5693406809839034061171719 8540110214758551091757579)
        ·
          refine ⟨12810165322137826637636369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8540110214758551091757579 12810165322137826637636369)
          ·
            refine ⟨9607623991603369978227277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12810165322137826637636369 9607623991603369978227277)
            ·
              refine ⟨3602858996851263741835229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9607623991603369978227277 3602858996851263741835229)
              ·
                refine ⟨1351072123819223903188211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3602858996851263741835229 1351072123819223903188211)
                ·
                  refine ⟨2026608185728835854782317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1351072123819223903188211 2026608185728835854782317)
                  ·
                    refine ⟨759978069648313445543369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2026608185728835854782317 759978069648313445543369)
                    ·
                      rfl

theorem cell22_2220078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_2220078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220078 prefixEnd_2220078 := by exact prefixLift 2220078
  have htrace : WordTrace (prefixWord ++ tailWord_2220078) baseStart_2220078 baseEnd_2220078 := by
    simpa [prefixWord, tailWord_2220078, baseEnd_2220078] using wordTrace_append hprefix tailTrace_2220078
  have hstable : (prefixWord ++ tailWord_2220078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220078).length < 2 ^ (prefixWord ++ tailWord_2220078).sum := by decide
  have hdescent : baseEnd_2220078 < baseStart_2220078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220132 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 1, 6]
def baseStart_2220132 : Nat := 118140960795 + 2220132 * 2 ^ 59
def prefixEnd_2220132 : Nat := 4983230072969 + 3 ^ 40 * 2220132 * 2
def baseEnd_2220132 : Nat := 759996554951875304693203

theorem tailTrace_2220132 : CollatzResearch.WordTrace tailWord_2220132 prefixEnd_2220132 759996554951875304693203 := by
  unfold tailWord_2220132
  simp only [CollatzResearch.WordTrace]
  refine ⟨40487433196424203601787325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53983244261898938135716433 40487433196424203601787325)
  ·
    refine ⟨15182787448659076350670247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40487433196424203601787325 15182787448659076350670247)
    ·
      refine ⟨22774181172988614526005371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15182787448659076350670247 22774181172988614526005371)
      ·
        refine ⟨34161271759482921789008057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22774181172988614526005371 34161271759482921789008057)
        ·
          refine ⟨25620953819612191341756043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34161271759482921789008057 25620953819612191341756043)
          ·
            refine ⟨38431430729418287012634065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25620953819612191341756043 38431430729418287012634065)
            ·
              refine ⟨28823573047063715259475549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38431430729418287012634065 28823573047063715259475549)
              ·
                refine ⟨10808839892648893222303331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28823573047063715259475549 10808839892648893222303331)
                ·
                  refine ⟨16213259838973339833454997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10808839892648893222303331 16213259838973339833454997)
                  ·
                    refine ⟨759996554951875304693203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16213259838973339833454997 759996554951875304693203)
                    ·
                      rfl

theorem cell22_2220132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_2220132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220132 prefixEnd_2220132 := by exact prefixLift 2220132
  have htrace : WordTrace (prefixWord ++ tailWord_2220132) baseStart_2220132 baseEnd_2220132 := by
    simpa [prefixWord, tailWord_2220132, baseEnd_2220132] using wordTrace_append hprefix tailTrace_2220132
  have hstable : (prefixWord ++ tailWord_2220132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220132).length < 2 ^ (prefixWord ++ tailWord_2220132).sum := by decide
  have hdescent : baseEnd_2220132 < baseStart_2220132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220138 : List Nat := [3, 1, 3, 2, 3, 1, 3, 1, 1, 4]
def baseStart_2220138 : Nat := 118140960795 + 2220138 * 2 ^ 59
def prefixEnd_2220138 : Nat := 4983230072969 + 3 ^ 40 * 2220138 * 2
def baseEnd_2220138 : Nat := 759998608874493289043185

theorem tailTrace_2220138 : CollatzResearch.WordTrace tailWord_2220138 prefixEnd_2220138 759998608874493289043185 := by
  unfold tailWord_2220138
  simp only [CollatzResearch.WordTrace]
  refine ⟨20243771307706667557073267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53983390153884446818862045 20243771307706667557073267)
  ·
    refine ⟨30365656961560001335609901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20243771307706667557073267 30365656961560001335609901)
    ·
      refine ⟨11387121360585000500853713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30365656961560001335609901 11387121360585000500853713)
      ·
        refine ⟨8540341020438750375640285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11387121360585000500853713 8540341020438750375640285)
        ·
          refine ⟨3202627882664531390865107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8540341020438750375640285 3202627882664531390865107)
          ·
            refine ⟨4803941823996797086297661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3202627882664531390865107 4803941823996797086297661)
            ·
              refine ⟨1801478183998798907361623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4803941823996797086297661 1801478183998798907361623)
              ·
                refine ⟨2702217275998198361042435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1801478183998798907361623 2702217275998198361042435)
                ·
                  refine ⟨4053325913997297541563653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2702217275998198361042435 4053325913997297541563653)
                  ·
                    refine ⟨759998608874493289043185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4053325913997297541563653 759998608874493289043185)
                    ·
                      rfl

theorem cell22_2220138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_2220138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220138 prefixEnd_2220138 := by exact prefixLift 2220138
  have htrace : WordTrace (prefixWord ++ tailWord_2220138) baseStart_2220138 baseEnd_2220138 := by
    simpa [prefixWord, tailWord_2220138, baseEnd_2220138] using wordTrace_append hprefix tailTrace_2220138
  have hstable : (prefixWord ++ tailWord_2220138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220138).length < 2 ^ (prefixWord ++ tailWord_2220138).sum := by decide
  have hdescent : baseEnd_2220138 < baseStart_2220138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220151 : List Nat := [1, 1, 3, 1, 1, 6, 2, 2, 2, 3]
def baseStart_2220151 : Nat := 118140960795 + 2220151 * 2 ^ 59
def prefixEnd_2220151 : Nat := 4983230072969 + 3 ^ 40 * 2220151 * 2
def baseEnd_2220151 : Nat := 760003059040165588468145

theorem tailTrace_2220151 : CollatzResearch.WordTrace tailWord_2220151 prefixEnd_2220151 760003059040165588468145 := by
  unfold tailWord_2220151
  simp only [CollatzResearch.WordTrace]
  refine ⟨80975559379779573448516307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53983706253186382299010871 80975559379779573448516307)
  ·
    refine ⟨121463339069669360172774461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80975559379779573448516307 121463339069669360172774461)
    ·
      refine ⟨45548752151126010064790423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121463339069669360172774461 45548752151126010064790423)
      ·
        refine ⟨68323128226689015097185635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45548752151126010064790423 68323128226689015097185635)
        ·
          refine ⟨102484692340033522645778453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68323128226689015097185635 102484692340033522645778453)
          ·
            refine ⟨4803969953439071374020865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 102484692340033522645778453 4803969953439071374020865)
            ·
              refine ⟨3602977465079303530515649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4803969953439071374020865 3602977465079303530515649)
              ·
                refine ⟨2702233098809477647886737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3602977465079303530515649 2702233098809477647886737)
                ·
                  refine ⟨2026674824107108235915053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2702233098809477647886737 2026674824107108235915053)
                  ·
                    refine ⟨760003059040165588468145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2026674824107108235915053 760003059040165588468145)
                    ·
                      rfl

theorem cell22_2220151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 3].length) (baseStart_2220151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220151 prefixEnd_2220151 := by exact prefixLift 2220151
  have htrace : WordTrace (prefixWord ++ tailWord_2220151) baseStart_2220151 baseEnd_2220151 := by
    simpa [prefixWord, tailWord_2220151, baseEnd_2220151] using wordTrace_append hprefix tailTrace_2220151
  have hstable : (prefixWord ++ tailWord_2220151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220151).length < 2 ^ (prefixWord ++ tailWord_2220151).sum := by decide
  have hdescent : baseEnd_2220151 < baseStart_2220151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220153 : List Nat := [1, 2, 1, 3, 4, 3, 2, 2, 4]
def baseStart_2220153 : Nat := 118140960795 + 2220153 * 2 ^ 59
def prefixEnd_2220153 : Nat := 4983230072969 + 3 ^ 40 * 2220153 * 2
def baseEnd_2220153 : Nat := 253334581227012749972713

theorem tailTrace_2220153 : CollatzResearch.WordTrace tailWord_2220153 prefixEnd_2220153 253334581227012749972713 := by
  unfold tailWord_2220153
  simp only [CollatzResearch.WordTrace]
  refine ⟨80975632325772327790089113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53983754883848218526726075 80975632325772327790089113)
  ·
    refine ⟨60731724244329245842566835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80975632325772327790089113 60731724244329245842566835)
    ·
      refine ⟨91097586366493868763850253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60731724244329245842566835 91097586366493868763850253)
      ·
        refine ⟨34161594887435200786443845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91097586366493868763850253 34161594887435200786443845)
        ·
          refine ⟨6405299041394100147458221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34161594887435200786443845 6405299041394100147458221)
          ·
            refine ⟨2401987140522787555296833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6405299041394100147458221 2401987140522787555296833)
            ·
              refine ⟨1801490355392090666472625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2401987140522787555296833 1801490355392090666472625)
              ·
                refine ⟨1351117766544067999854469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1801490355392090666472625 1351117766544067999854469)
                ·
                  refine ⟨253334581227012749972713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1351117766544067999854469 253334581227012749972713)
                  ·
                    rfl

theorem cell22_2220153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 4].length) (baseStart_2220153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220153 prefixEnd_2220153 := by exact prefixLift 2220153
  have htrace : WordTrace (prefixWord ++ tailWord_2220153) baseStart_2220153 baseEnd_2220153 := by
    simpa [prefixWord, tailWord_2220153, baseEnd_2220153] using wordTrace_append hprefix tailTrace_2220153
  have hstable : (prefixWord ++ tailWord_2220153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220153).length < 2 ^ (prefixWord ++ tailWord_2220153).sum := by decide
  have hdescent : baseEnd_2220153 < baseStart_2220153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220183 : List Nat := [1, 1, 3, 3, 5, 1, 1, 1, 2, 4]
def baseStart_2220183 : Nat := 118140960795 + 2220183 * 2 ^ 59
def prefixEnd_2220183 : Nat := 4983230072969 + 3 ^ 40 * 2220183 * 2
def baseEnd_2220183 : Nat := 760014013294128171668047

theorem tailTrace_2220183 : CollatzResearch.WordTrace tailWord_2220183 prefixEnd_2220183 760014013294128171668047 := by
  unfold tailWord_2220183
  simp only [CollatzResearch.WordTrace]
  refine ⟨80976726515663642913681203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53984484343775761942454135 80976726515663642913681203)
  ·
    refine ⟨121465089773495464370521805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80976726515663642913681203 121465089773495464370521805)
    ·
      refine ⟨45549408665060799138945677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121465089773495464370521805 45549408665060799138945677)
      ·
        refine ⟨17081028249397799677104629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45549408665060799138945677 17081028249397799677104629)
        ·
          refine ⟨1601346398381043719728559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17081028249397799677104629 1601346398381043719728559)
          ·
            refine ⟨2402019597571565579592839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1601346398381043719728559 2402019597571565579592839)
            ·
              refine ⟨3603029396357348369389259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2402019597571565579592839 3603029396357348369389259)
              ·
                refine ⟨5404544094536022554083889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3603029396357348369389259 5404544094536022554083889)
                ·
                  refine ⟨4053408070902016915562917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5404544094536022554083889 4053408070902016915562917)
                  ·
                    refine ⟨760014013294128171668047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4053408070902016915562917 760014013294128171668047)
                    ·
                      rfl

theorem cell22_2220183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 2, 4].length) (baseStart_2220183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220183 prefixEnd_2220183 := by exact prefixLift 2220183
  have htrace : WordTrace (prefixWord ++ tailWord_2220183) baseStart_2220183 baseEnd_2220183 := by
    simpa [prefixWord, tailWord_2220183, baseEnd_2220183] using wordTrace_append hprefix tailTrace_2220183
  have hstable : (prefixWord ++ tailWord_2220183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220183).length < 2 ^ (prefixWord ++ tailWord_2220183).sum := by decide
  have hdescent : baseEnd_2220183 < baseStart_2220183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220202 : List Nat := [3, 1, 5, 1, 3, 1, 1, 2, 2, 3]
def baseStart_2220202 : Nat := 118140960795 + 2220202 * 2 ^ 59
def prefixEnd_2220202 : Nat := 4983230072969 + 3 ^ 40 * 2220202 * 2
def baseEnd_2220202 : Nat := 760020517382418455442989

theorem tailTrace_2220202 : CollatzResearch.WordTrace tailWord_2220202 prefixEnd_2220202 760020517382418455442989 := by
  unfold tailWord_2220202
  simp only [CollatzResearch.WordTrace]
  refine ⟨20244354875648702289655715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53984946335063206105748573 20244354875648702289655715)
  ·
    refine ⟨30366532313473053434483573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20244354875648702289655715 30366532313473053434483573)
    ·
      refine ⟨2846862404388098759482835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30366532313473053434483573 2846862404388098759482835)
      ·
        refine ⟨4270293606582148139224253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2846862404388098759482835 4270293606582148139224253)
        ·
          refine ⟨1601360102468305552209095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4270293606582148139224253 1601360102468305552209095)
          ·
            refine ⟨2402040153702458328313643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1601360102468305552209095 2402040153702458328313643)
            ·
              refine ⟨3603060230553687492470465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2402040153702458328313643 3603060230553687492470465)
              ·
                refine ⟨2702295172915265619352849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3603060230553687492470465 2702295172915265619352849)
                ·
                  refine ⟨2026721379686449214514637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2702295172915265619352849 2026721379686449214514637)
                  ·
                    refine ⟨760020517382418455442989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2026721379686449214514637 760020517382418455442989)
                    ·
                      rfl

theorem cell22_2220202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_2220202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220202 prefixEnd_2220202 := by exact prefixLift 2220202
  have htrace : WordTrace (prefixWord ++ tailWord_2220202) baseStart_2220202 baseEnd_2220202 := by
    simpa [prefixWord, tailWord_2220202, baseEnd_2220202] using wordTrace_append hprefix tailTrace_2220202
  have hstable : (prefixWord ++ tailWord_2220202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220202).length < 2 ^ (prefixWord ++ tailWord_2220202).sum := by decide
  have hdescent : baseEnd_2220202 < baseStart_2220202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220224 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 2, 5]
def baseStart_2220224 : Nat := 118140960795 + 2220224 * 2 ^ 59
def prefixEnd_2220224 : Nat := 4983230072969 + 3 ^ 40 * 2220224 * 2
def baseEnd_2220224 : Nat := 760028048432017731392921

theorem tailTrace_2220224 : CollatzResearch.WordTrace tailWord_2220224 prefixEnd_2220224 760028048432017731392921 := by
  unfold tailWord_2220224
  simp only [CollatzResearch.WordTrace]
  refine ⟨40489110954257553457961863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53985481272343404610615817 40489110954257553457961863)
  ·
    refine ⟨60733666431386330186942795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40489110954257553457961863 60733666431386330186942795)
    ·
      refine ⟨91100499647079495280414193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60733666431386330186942795 91100499647079495280414193)
      ·
        refine ⟨68325374735309621460310645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91100499647079495280414193 68325374735309621460310645)
        ·
          refine ⟨6405503881435277011904123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68325374735309621460310645 6405503881435277011904123)
          ·
            refine ⟨9608255822152915517856185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6405503881435277011904123 9608255822152915517856185)
            ·
              refine ⟨7206191866614686638392139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9608255822152915517856185 7206191866614686638392139)
              ·
                refine ⟨10809287799922029957588209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7206191866614686638392139 10809287799922029957588209)
                ·
                  refine ⟨8106965849941522468191157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10809287799922029957588209 8106965849941522468191157)
                  ·
                    refine ⟨760028048432017731392921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8106965849941522468191157 760028048432017731392921)
                    ·
                      rfl

theorem cell22_2220224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 2, 5].length) (baseStart_2220224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220224 prefixEnd_2220224 := by exact prefixLift 2220224
  have htrace : WordTrace (prefixWord ++ tailWord_2220224) baseStart_2220224 baseEnd_2220224 := by
    simpa [prefixWord, tailWord_2220224, baseEnd_2220224] using wordTrace_append hprefix tailTrace_2220224
  have hstable : (prefixWord ++ tailWord_2220224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220224).length < 2 ^ (prefixWord ++ tailWord_2220224).sum := by decide
  have hdescent : baseEnd_2220224 < baseStart_2220224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220271 : List Nat := [1, 1, 2, 1, 6, 3, 1, 1, 6]
def baseStart_2220271 : Nat := 118140960795 + 2220271 * 2 ^ 59
def prefixEnd_2220271 : Nat := 4983230072969 + 3 ^ 40 * 2220271 * 2
def baseEnd_2220271 : Nat := 253348045830841758489259

theorem tailTrace_2220271 : CollatzResearch.WordTrace tailWord_2220271 prefixEnd_2220271 253348045830841758489259 := by
  unfold tailWord_2220271
  simp only [CollatzResearch.WordTrace]
  refine ⟨80979936139344833942884667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53986624092896555961923111 80979936139344833942884667)
  ·
    refine ⟨121469904209017250914327001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80979936139344833942884667 121469904209017250914327001)
    ·
      refine ⟨91102428156762938185745251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121469904209017250914327001 91102428156762938185745251)
      ·
        refine ⟨136653642235144407278617877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91102428156762938185745251 136653642235144407278617877)
        ·
          refine ⟨6405639479772394091185213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 136653642235144407278617877 6405639479772394091185213)
          ·
            refine ⟨2402114804914647784194455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6405639479772394091185213 2402114804914647784194455)
            ·
              refine ⟨3603172207371971676291683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2402114804914647784194455 3603172207371971676291683)
              ·
                refine ⟨5404758311057957514437525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3603172207371971676291683 5404758311057957514437525)
                ·
                  refine ⟨253348045830841758489259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5404758311057957514437525 253348045830841758489259)
                  ·
                    rfl

theorem cell22_2220271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 6].length) (baseStart_2220271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220271 prefixEnd_2220271 := by exact prefixLift 2220271
  have htrace : WordTrace (prefixWord ++ tailWord_2220271) baseStart_2220271 baseEnd_2220271 := by
    simpa [prefixWord, tailWord_2220271, baseEnd_2220271] using wordTrace_append hprefix tailTrace_2220271
  have hstable : (prefixWord ++ tailWord_2220271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220271).length < 2 ^ (prefixWord ++ tailWord_2220271).sum := by decide
  have hdescent : baseEnd_2220271 < baseStart_2220271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220286 : List Nat := [4, 2, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_2220286 : Nat := 118140960795 + 2220286 * 2 ^ 59
def prefixEnd_2220286 : Nat := 4983230072969 + 3 ^ 40 * 2220286 * 2
def baseEnd_2220286 : Nat := 760049272299070236342731

theorem tailTrace_2220286 : CollatzResearch.WordTrace tailWord_2220286 prefixEnd_2220286 760049272299070236342731 := by
  unfold tailWord_2220286
  simp only [CollatzResearch.WordTrace]
  refine ⟨10122560404286311438085089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53986988822860327669787141 10122560404286311438085089)
  ·
    refine ⟨7591920303214733578563817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10122560404286311438085089 7591920303214733578563817)
    ·
      refine ⟨5693940227411050183922863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7591920303214733578563817 5693940227411050183922863)
      ·
        refine ⟨8540910341116575275884295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5693940227411050183922863 8540910341116575275884295)
        ·
          refine ⟨12811365511674862913826443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8540910341116575275884295 12811365511674862913826443)
          ·
            refine ⟨19217048267512294370739665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12811365511674862913826443 19217048267512294370739665)
            ·
              refine ⟨14412786200634220778054749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19217048267512294370739665 14412786200634220778054749)
              ·
                refine ⟨5404794825237832791770531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14412786200634220778054749 5404794825237832791770531)
                ·
                  refine ⟨8107192237856749187655797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5404794825237832791770531 8107192237856749187655797)
                  ·
                    refine ⟨760049272299070236342731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8107192237856749187655797 760049272299070236342731)
                    ·
                      rfl

theorem cell22_2220286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_2220286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220286 prefixEnd_2220286 := by exact prefixLift 2220286
  have htrace : WordTrace (prefixWord ++ tailWord_2220286) baseStart_2220286 baseEnd_2220286 := by
    simpa [prefixWord, tailWord_2220286, baseEnd_2220286] using wordTrace_append hprefix tailTrace_2220286
  have hstable : (prefixWord ++ tailWord_2220286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220286).length < 2 ^ (prefixWord ++ tailWord_2220286).sum := by decide
  have hdescent : baseEnd_2220286 < baseStart_2220286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220290 : List Nat := [3, 4, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_2220290 : Nat := 118140960795 + 2220290 * 2 ^ 59
def prefixEnd_2220290 : Nat := 4983230072969 + 3 ^ 40 * 2220290 * 2
def baseEnd_2220290 : Nat := 760050641580815559242719

theorem tailTrace_2220290 : CollatzResearch.WordTrace tailWord_2220290 prefixEnd_2220290 760050641580815559242719 := by
  unfold tailWord_2220290
  simp only [CollatzResearch.WordTrace]
  refine ⟨20245157281569000046956581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53987086084184000125217549 20245157281569000046956581)
  ·
    refine ⟨3795966990294187508804359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20245157281569000046956581 3795966990294187508804359)
    ·
      refine ⟨5693950485441281263206539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3795966990294187508804359 5693950485441281263206539)
      ·
        refine ⟨8540925728161921894809809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5693950485441281263206539 8540925728161921894809809)
        ·
          refine ⟨6405694296121441421107357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8540925728161921894809809 6405694296121441421107357)
          ·
            refine ⟨2402135361045540532915259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6405694296121441421107357 2402135361045540532915259)
            ·
              refine ⟨3603203041568310799372889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2402135361045540532915259 3603203041568310799372889)
              ·
                refine ⟨2702402281176233099529667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3603203041568310799372889 2702402281176233099529667)
                ·
                  refine ⟨4053603421764349649294501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2702402281176233099529667 4053603421764349649294501)
                  ·
                    refine ⟨760050641580815559242719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4053603421764349649294501 760050641580815559242719)
                    ·
                      rfl

theorem cell22_2220290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_2220290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220290 prefixEnd_2220290 := by exact prefixLift 2220290
  have htrace : WordTrace (prefixWord ++ tailWord_2220290) baseStart_2220290 baseEnd_2220290 := by
    simpa [prefixWord, tailWord_2220290, baseEnd_2220290] using wordTrace_append hprefix tailTrace_2220290
  have hstable : (prefixWord ++ tailWord_2220290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220290).length < 2 ^ (prefixWord ++ tailWord_2220290).sum := by decide
  have hdescent : baseEnd_2220290 < baseStart_2220290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220359 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 1, 7]
def baseStart_2220359 : Nat := 118140960795 + 2220359 * 2 ^ 59
def prefixEnd_2220359 : Nat := 4983230072969 + 3 ^ 40 * 2220359 * 2
def baseEnd_2220359 : Nat := 760074261690922379267507

theorem tailTrace_2220359 : CollatzResearch.WordTrace tailWord_2220359 prefixEnd_2220359 760074261690922379267507 := by
  unfold tailWord_2220359
  simp only [CollatzResearch.WordTrace]
  refine ⟨80983145763026024972088131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53988763842017349981392087 80983145763026024972088131)
  ·
    refine ⟨121474718644539037458132197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80983145763026024972088131 121474718644539037458132197)
    ·
      refine ⟨22776509745851069523399787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121474718644539037458132197 22776509745851069523399787)
      ·
        refine ⟨34164764618776604285099681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22776509745851069523399787 34164764618776604285099681)
        ·
          refine ⟨25623573464082453213824761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34164764618776604285099681 25623573464082453213824761)
          ·
            refine ⟨19217680098061839910368571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25623573464082453213824761 19217680098061839910368571)
            ·
              refine ⟨28826520147092759865552857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19217680098061839910368571 28826520147092759865552857)
              ·
                refine ⟨21619890110319569899164643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28826520147092759865552857 21619890110319569899164643)
                ·
                  refine ⟨32429835165479354848746965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21619890110319569899164643 32429835165479354848746965)
                  ·
                    refine ⟨760074261690922379267507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32429835165479354848746965 760074261690922379267507)
                    ·
                      rfl

theorem cell22_2220359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_2220359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220359 prefixEnd_2220359 := by exact prefixLift 2220359
  have htrace : WordTrace (prefixWord ++ tailWord_2220359) baseStart_2220359 baseEnd_2220359 := by
    simpa [prefixWord, tailWord_2220359, baseEnd_2220359] using wordTrace_append hprefix tailTrace_2220359
  have hstable : (prefixWord ++ tailWord_2220359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220359).length < 2 ^ (prefixWord ++ tailWord_2220359).sum := by decide
  have hdescent : baseEnd_2220359 < baseStart_2220359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220451 : List Nat := [1, 1, 1, 4, 1, 5, 2, 7]
def baseStart_2220451 : Nat := 118140960795 + 2220451 * 2 ^ 59
def prefixEnd_2220451 : Nat := 4983230072969 + 3 ^ 40 * 2220451 * 2
def baseEnd_2220451 : Nat := 84456195019007200663025

theorem tailTrace_2220451 : CollatzResearch.WordTrace tailWord_2220451 prefixEnd_2220451 84456195019007200663025 := by
  unfold tailWord_2220451
  simp only [CollatzResearch.WordTrace]
  refine ⟨80986501278692724684437207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53991000852461816456291471 80986501278692724684437207)
  ·
    refine ⟨121479751918039087026655811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80986501278692724684437207 121479751918039087026655811)
    ·
      refine ⟨182219627877058630539983717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121479751918039087026655811 182219627877058630539983717)
      ·
        refine ⟨34166180226948493226246947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182219627877058630539983717 34166180226948493226246947)
        ·
          refine ⟨51249270340422739839370421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34166180226948493226246947 51249270340422739839370421)
          ·
            refine ⟨4804619094414631859940977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51249270340422739839370421 4804619094414631859940977)
            ·
              refine ⟨3603464320810973894955733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4804619094414631859940977 3603464320810973894955733)
              ·
                refine ⟨84456195019007200663025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3603464320810973894955733 84456195019007200663025)
                ·
                  rfl

theorem cell22_2220451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 7].length) (baseStart_2220451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220451 prefixEnd_2220451 := by exact prefixLift 2220451
  have htrace : WordTrace (prefixWord ++ tailWord_2220451) baseStart_2220451 baseEnd_2220451 := by
    simpa [prefixWord, tailWord_2220451, baseEnd_2220451] using wordTrace_append hprefix tailTrace_2220451
  have hstable : (prefixWord ++ tailWord_2220451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220451).length < 2 ^ (prefixWord ++ tailWord_2220451).sum := by decide
  have hdescent : baseEnd_2220451 < baseStart_2220451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220455 : List Nat := [1, 1, 6, 1, 1, 3, 1, 3, 2, 3]
def baseStart_2220455 : Nat := 118140960795 + 2220455 * 2 ^ 59
def prefixEnd_2220455 : Nat := 4983230072969 + 3 ^ 40 * 2220455 * 2
def baseEnd_2220455 : Nat := 760107124452810128867213

theorem tailTrace_2220455 : CollatzResearch.WordTrace tailWord_2220455 prefixEnd_2220455 760107124452810128867213 := by
  unfold tailWord_2220455
  simp only [CollatzResearch.WordTrace]
  refine ⟨80986647170678233367582819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53991098113785488911721879 80986647170678233367582819)
  ·
    refine ⟨121479970756017350051374229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80986647170678233367582819 121479970756017350051374229)
    ·
      refine ⟨5694373629188313283658167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 121479970756017350051374229 5694373629188313283658167)
      ·
        refine ⟨8541560443782469925487251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5694373629188313283658167 8541560443782469925487251)
        ·
          refine ⟨12812340665673704888230877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8541560443782469925487251 12812340665673704888230877)
          ·
            refine ⟨4804627749627639333086579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12812340665673704888230877 4804627749627639333086579)
            ·
              refine ⟨7206941624441458999629869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4804627749627639333086579 7206941624441458999629869)
              ·
                refine ⟨2702603109165547124861201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7206941624441458999629869 2702603109165547124861201)
                ·
                  refine ⟨2026952331874160343645901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2702603109165547124861201 2026952331874160343645901)
                  ·
                    refine ⟨760107124452810128867213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2026952331874160343645901 760107124452810128867213)
                    ·
                      rfl

theorem cell22_2220455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_2220455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220455 prefixEnd_2220455 := by exact prefixLift 2220455
  have htrace : WordTrace (prefixWord ++ tailWord_2220455) baseStart_2220455 baseEnd_2220455 := by
    simpa [prefixWord, tailWord_2220455, baseEnd_2220455] using wordTrace_append hprefix tailTrace_2220455
  have hstable : (prefixWord ++ tailWord_2220455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220455).length < 2 ^ (prefixWord ++ tailWord_2220455).sum := by decide
  have hdescent : baseEnd_2220455 < baseStart_2220455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220511 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 1, 7]
def baseStart_2220511 : Nat := 118140960795 + 2220511 * 2 ^ 59
def prefixEnd_2220511 : Nat := 4983230072969 + 3 ^ 40 * 2220511 * 2
def baseEnd_2220511 : Nat := 760126294397244649467041

theorem tailTrace_2220511 : CollatzResearch.WordTrace tailWord_2220511 prefixEnd_2220511 760126294397244649467041 := by
  unfold tailWord_2220511
  simp only [CollatzResearch.WordTrace]
  refine ⟨80988689658475354931621387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53992459772316903287747591 80988689658475354931621387)
  ·
    refine ⟨121483034487713032397432081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80988689658475354931621387 121483034487713032397432081)
    ·
      refine ⟨91112275865784774298074061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121483034487713032397432081 91112275865784774298074061)
      ·
        refine ⟨34167103449669290361777773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91112275865784774298074061 34167103449669290361777773)
        ·
          refine ⟨12812663793625983885666665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34167103449669290361777773 12812663793625983885666665)
          ·
            refine ⟨9609497845219487914249999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12812663793625983885666665 9609497845219487914249999)
            ·
              refine ⟨14414246767829231871374999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9609497845219487914249999 14414246767829231871374999)
              ·
                refine ⟨21621370151743847807062499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14414246767829231871374999 21621370151743847807062499)
                ·
                  refine ⟨32432055227615771710593749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21621370151743847807062499 32432055227615771710593749)
                  ·
                    refine ⟨760126294397244649467041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32432055227615771710593749 760126294397244649467041)
                    ·
                      rfl

theorem cell22_2220511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_2220511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220511 prefixEnd_2220511 := by exact prefixLift 2220511
  have htrace : WordTrace (prefixWord ++ tailWord_2220511) baseStart_2220511 baseEnd_2220511 := by
    simpa [prefixWord, tailWord_2220511, baseEnd_2220511] using wordTrace_append hprefix tailTrace_2220511
  have hstable : (prefixWord ++ tailWord_2220511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220511).length < 2 ^ (prefixWord ++ tailWord_2220511).sum := by decide
  have hdescent : baseEnd_2220511 < baseStart_2220511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220541 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 8]
def baseStart_2220541 : Nat := 118140960795 + 2220541 * 2 ^ 59
def prefixEnd_2220541 : Nat := 4983230072969 + 3 ^ 40 * 2220541 * 2
def baseEnd_2220541 : Nat := 253378854670111523738983

theorem tailTrace_2220541 : CollatzResearch.WordTrace tailWord_2220541 prefixEnd_2220541 253378854670111523738983 := by
  unfold tailWord_2220541
  simp only [CollatzResearch.WordTrace]
  refine ⟨80989783848366670055213477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53993189232244446703475651 80989783848366670055213477)
  ·
    refine ⟨15185584471568750635352527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80989783848366670055213477 15185584471568750635352527)
    ·
      refine ⟨22778376707353125953028791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15185584471568750635352527 22778376707353125953028791)
      ·
        refine ⟨34167565061029688929543187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22778376707353125953028791 34167565061029688929543187)
        ·
          refine ⟨51251347591544533394314781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34167565061029688929543187 51251347591544533394314781)
          ·
            refine ⟨19219255346829200022868043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51251347591544533394314781 19219255346829200022868043)
            ·
              refine ⟨28828883020243800034302065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19219255346829200022868043 28828883020243800034302065)
              ·
                refine ⟨21621662265182850025726549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28828883020243800034302065 21621662265182850025726549)
                ·
                  refine ⟨253378854670111523738983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21621662265182850025726549 253378854670111523738983)
                  ·
                    rfl

theorem cell22_2220541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_2220541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220541 prefixEnd_2220541 := by exact prefixLift 2220541
  have htrace : WordTrace (prefixWord ++ tailWord_2220541) baseStart_2220541 baseEnd_2220541 := by
    simpa [prefixWord, tailWord_2220541, baseEnd_2220541] using wordTrace_append hprefix tailTrace_2220541
  have hstable : (prefixWord ++ tailWord_2220541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220541).length < 2 ^ (prefixWord ++ tailWord_2220541).sum := by decide
  have hdescent : baseEnd_2220541 < baseStart_2220541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220543 : List Nat := [1, 1, 2, 2, 1, 2, 5, 3, 1, 4]
def baseStart_2220543 : Nat := 118140960795 + 2220543 * 2 ^ 59
def prefixEnd_2220543 : Nat := 4983230072969 + 3 ^ 40 * 2220543 * 2
def baseEnd_2220543 : Nat := 760137248651207232666943

theorem tailTrace_2220543 : CollatzResearch.WordTrace tailWord_2220543 prefixEnd_2220543 760137248651207232666943 := by
  unfold tailWord_2220543
  simp only [CollatzResearch.WordTrace]
  refine ⟨80989856794359424396786283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53993237862906282931190855 80989856794359424396786283)
  ·
    refine ⟨121484785191539136595179425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80989856794359424396786283 121484785191539136595179425)
    ·
      refine ⟨91113588893654352446384569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121484785191539136595179425 91113588893654352446384569)
      ·
        refine ⟨68335191670240764334788427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91113588893654352446384569 68335191670240764334788427)
        ·
          refine ⟨102502787505361146502182641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68335191670240764334788427 102502787505361146502182641)
          ·
            refine ⟨76877090629020859876636981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102502787505361146502182641 76877090629020859876636981)
            ·
              refine ⟨7207227246470705613434717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76877090629020859876636981 7207227246470705613434717)
              ·
                refine ⟨2702710217426514605038019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7207227246470705613434717 2702710217426514605038019)
                ·
                  refine ⟨4054065326139771907557029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2702710217426514605038019 4054065326139771907557029)
                  ·
                    refine ⟨760137248651207232666943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4054065326139771907557029 760137248651207232666943)
                    ·
                      rfl

theorem cell22_2220543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 4].length) (baseStart_2220543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220543 prefixEnd_2220543 := by exact prefixLift 2220543
  have htrace : WordTrace (prefixWord ++ tailWord_2220543) baseStart_2220543 baseEnd_2220543 := by
    simpa [prefixWord, tailWord_2220543, baseEnd_2220543] using wordTrace_append hprefix tailTrace_2220543
  have hstable : (prefixWord ++ tailWord_2220543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220543).length < 2 ^ (prefixWord ++ tailWord_2220543).sum := by decide
  have hdescent : baseEnd_2220543 < baseStart_2220543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220558 : List Nat := [4, 1, 1, 2, 3, 1, 1, 3, 6]
def baseStart_2220558 : Nat := 118140960795 + 2220558 * 2 ^ 59
def prefixEnd_2220558 : Nat := 4983230072969 + 3 ^ 40 * 2220558 * 2
def baseEnd_2220558 : Nat := 253380794485917397847299

theorem tailTrace_2220558 : CollatzResearch.WordTrace tailWord_2220558 prefixEnd_2220558 253380794485917397847299 := by
  unfold tailWord_2220558
  simp only [CollatzResearch.WordTrace]
  refine ⟨10123800486163135244822791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53993602592870054639054885 10123800486163135244822791)
  ·
    refine ⟨15185700729244702867234187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10123800486163135244822791 15185700729244702867234187)
    ·
      refine ⟨22778551093867054300851281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15185700729244702867234187 22778551093867054300851281)
      ·
        refine ⟨17083913320400290725638461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22778551093867054300851281 17083913320400290725638461)
        ·
          refine ⟨6406467495150109022114423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17083913320400290725638461 6406467495150109022114423)
          ·
            refine ⟨9609701242725163533171635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6406467495150109022114423 9609701242725163533171635)
            ·
              refine ⟨14414551864087745299757453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9609701242725163533171635 14414551864087745299757453)
              ·
                refine ⟨5405456949032904487409045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14414551864087745299757453 5405456949032904487409045)
                ·
                  refine ⟨253380794485917397847299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5405456949032904487409045 253380794485917397847299)
                  ·
                    rfl

theorem cell22_2220558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_2220558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220558 prefixEnd_2220558 := by exact prefixLift 2220558
  have htrace : WordTrace (prefixWord ++ tailWord_2220558) baseStart_2220558 baseEnd_2220558 := by
    simpa [prefixWord, tailWord_2220558, baseEnd_2220558] using wordTrace_append hprefix tailTrace_2220558
  have hstable : (prefixWord ++ tailWord_2220558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220558).length < 2 ^ (prefixWord ++ tailWord_2220558).sum := by decide
  have hdescent : baseEnd_2220558 < baseStart_2220558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220605 : List Nat := [1, 4, 1, 3, 2, 2, 1, 2, 2, 4]
def baseStart_2220605 : Nat := 118140960795 + 2220605 * 2 ^ 59
def prefixEnd_2220605 : Nat := 4983230072969 + 3 ^ 40 * 2220605 * 2
def baseEnd_2220605 : Nat := 760158472518259737616753

theorem tailTrace_2220605 : CollatzResearch.WordTrace tailWord_2220605 prefixEnd_2220605 760158472518259737616753 := by
  unfold tailWord_2220605
  simp only [CollatzResearch.WordTrace]
  refine ⟨80992118120134808985543269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53994745413423205990362179 80992118120134808985543269)
  ·
    refine ⟨15186022147525276684789363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80992118120134808985543269 15186022147525276684789363)
    ·
      refine ⟨22779033221287915027184045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15186022147525276684789363 22779033221287915027184045)
      ·
        refine ⟨8542137457982968135194017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22779033221287915027184045 8542137457982968135194017)
        ·
          refine ⟨6406603093487226101395513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8542137457982968135194017 6406603093487226101395513)
          ·
            refine ⟨4804952320115419576046635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6406603093487226101395513 4804952320115419576046635)
            ·
              refine ⟨7207428480173129364069953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4804952320115419576046635 7207428480173129364069953)
              ·
                refine ⟨5405571360129847023052465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7207428480173129364069953 5405571360129847023052465)
                ·
                  refine ⟨4054178520097385267289349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5405571360129847023052465 4054178520097385267289349)
                  ·
                    refine ⟨760158472518259737616753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4054178520097385267289349 760158472518259737616753)
                    ·
                      rfl

theorem cell22_2220605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_2220605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220605 prefixEnd_2220605 := by exact prefixLift 2220605
  have htrace : WordTrace (prefixWord ++ tailWord_2220605) baseStart_2220605 baseEnd_2220605 := by
    simpa [prefixWord, tailWord_2220605, baseEnd_2220605] using wordTrace_append hprefix tailTrace_2220605
  have hstable : (prefixWord ++ tailWord_2220605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220605).length < 2 ^ (prefixWord ++ tailWord_2220605).sum := by decide
  have hdescent : baseEnd_2220605 < baseStart_2220605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220665 : List Nat := [1, 2, 1, 3, 3, 3, 2, 2, 5]
def baseStart_2220665 : Nat := 118140960795 + 2220665 * 2 ^ 59
def prefixEnd_2220665 : Nat := 4983230072969 + 3 ^ 40 * 2220665 * 2
def baseEnd_2220665 : Nat := 253393003914813193705523

theorem tailTrace_2220665 : CollatzResearch.WordTrace tailWord_2220665 prefixEnd_2220665 253393003914813193705523 := by
  unfold tailWord_2220665
  simp only [CollatzResearch.WordTrace]
  refine ⟨80994306499917439232727449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53996204333278292821818299 80994306499917439232727449)
  ·
    refine ⟨60745729874938079424545587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80994306499917439232727449 60745729874938079424545587)
    ·
      refine ⟨91118594812407119136818381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60745729874938079424545587 91118594812407119136818381)
      ·
        refine ⟨34169473054652669676306893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91118594812407119136818381 34169473054652669676306893)
        ·
          refine ⟨12813552395494751128615085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34169473054652669676306893 12813552395494751128615085)
          ·
            refine ⟨4805082148310531673230657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12813552395494751128615085 4805082148310531673230657)
            ·
              refine ⟨3603811611232898754922993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4805082148310531673230657 3603811611232898754922993)
              ·
                refine ⟨2702858708424674066192245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3603811611232898754922993 2702858708424674066192245)
                ·
                  refine ⟨253393003914813193705523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2702858708424674066192245 253393003914813193705523)
                  ·
                    rfl

theorem cell22_2220665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 5].length) (baseStart_2220665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220665 prefixEnd_2220665 := by exact prefixLift 2220665
  have htrace : WordTrace (prefixWord ++ tailWord_2220665) baseStart_2220665 baseEnd_2220665 := by
    simpa [prefixWord, tailWord_2220665, baseEnd_2220665] using wordTrace_append hprefix tailTrace_2220665
  have hstable : (prefixWord ++ tailWord_2220665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220665).length < 2 ^ (prefixWord ++ tailWord_2220665).sum := by decide
  have hdescent : baseEnd_2220665 < baseStart_2220665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220669 : List Nat := [1, 4, 1, 1, 5, 1, 1, 4, 1, 3]
def baseStart_2220669 : Nat := 118140960795 + 2220669 * 2 ^ 59
def prefixEnd_2220669 : Nat := 4983230072969 + 3 ^ 40 * 2220669 * 2
def baseEnd_2220669 : Nat := 760180381026184904016557

theorem tailTrace_2220669 : CollatzResearch.WordTrace tailWord_2220669 prefixEnd_2220669 760180381026184904016557 := by
  unfold tailWord_2220669
  simp only [CollatzResearch.WordTrace]
  refine ⟨80994452391902947915873061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53996301594601965277248707 80994452391902947915873061)
  ·
    refine ⟨15186459823481802734226199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80994452391902947915873061 15186459823481802734226199)
    ·
      refine ⟨22779689735222704101339299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15186459823481802734226199 22779689735222704101339299)
      ·
        refine ⟨34169534602834056152008949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22779689735222704101339299 34169534602834056152008949)
        ·
          refine ⟨3203393869015692764250839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34169534602834056152008949 3203393869015692764250839)
          ·
            refine ⟨4805090803523539146376259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3203393869015692764250839 4805090803523539146376259)
            ·
              refine ⟨7207636205285308719564389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4805090803523539146376259 7207636205285308719564389)
              ·
                refine ⟨1351431788490995384918323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7207636205285308719564389 1351431788490995384918323)
                ·
                  refine ⟨2027147682736493077377485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1351431788490995384918323 2027147682736493077377485)
                  ·
                    refine ⟨760180381026184904016557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2027147682736493077377485 760180381026184904016557)
                    ·
                      rfl

theorem cell22_2220669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_2220669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220669 prefixEnd_2220669 := by exact prefixLift 2220669
  have htrace : WordTrace (prefixWord ++ tailWord_2220669) baseStart_2220669 baseEnd_2220669 := by
    simpa [prefixWord, tailWord_2220669, baseEnd_2220669] using wordTrace_append hprefix tailTrace_2220669
  have hstable : (prefixWord ++ tailWord_2220669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220669).length < 2 ^ (prefixWord ++ tailWord_2220669).sum := by decide
  have hdescent : baseEnd_2220669 < baseStart_2220669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220695 : List Nat := [1, 1, 3, 3, 2, 1, 2, 4, 1, 4]
def baseStart_2220695 : Nat := 118140960795 + 2220695 * 2 ^ 59
def prefixEnd_2220695 : Nat := 4983230072969 + 3 ^ 40 * 2220695 * 2
def baseEnd_2220695 : Nat := 760189281357529502866477

theorem tailTrace_2220695 : CollatzResearch.WordTrace tailWord_2220695 prefixEnd_2220695 760189281357529502866477 := by
  unfold tailWord_2220695
  simp only [CollatzResearch.WordTrace]
  refine ⟨80995400689808754356319539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53996933793205836237546359 80995400689808754356319539)
  ·
    refine ⟨121493101034713131534479309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80995400689808754356319539 121493101034713131534479309)
    ·
      refine ⟨45559912888017424325429741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121493101034713131534479309 45559912888017424325429741)
      ·
        refine ⟨17084967333006534122036153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45559912888017424325429741 17084967333006534122036153)
        ·
          refine ⟨12813725499754900591527115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17084967333006534122036153 12813725499754900591527115)
          ·
            refine ⟨19220588249632350887290673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12813725499754900591527115 19220588249632350887290673)
            ·
              refine ⟨14415441187224263165468005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19220588249632350887290673 14415441187224263165468005)
              ·
                refine ⟨2702895222604549343525251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14415441187224263165468005 2702895222604549343525251)
                ·
                  refine ⟨4054342833906824015287877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2702895222604549343525251 4054342833906824015287877)
                  ·
                    refine ⟨760189281357529502866477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4054342833906824015287877 760189281357529502866477)
                    ·
                      rfl

theorem cell22_2220695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_2220695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220695 prefixEnd_2220695 := by exact prefixLift 2220695
  have htrace : WordTrace (prefixWord ++ tailWord_2220695) baseStart_2220695 baseEnd_2220695 := by
    simpa [prefixWord, tailWord_2220695, baseEnd_2220695] using wordTrace_append hprefix tailTrace_2220695
  have hstable : (prefixWord ++ tailWord_2220695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220695).length < 2 ^ (prefixWord ++ tailWord_2220695).sum := by decide
  have hdescent : baseEnd_2220695 < baseStart_2220695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220740 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 1, 6]
def baseStart_2220740 : Nat := 118140960795 + 2220740 * 2 ^ 59
def prefixEnd_2220740 : Nat := 4983230072969 + 3 ^ 40 * 2220740 * 2
def baseEnd_2220740 : Nat := 760204685777164385491339

theorem tailTrace_2220740 : CollatzResearch.WordTrace tailWord_2220740 prefixEnd_2220740 760204685777164385491339 := by
  unfold tailWord_2220740
  simp only [CollatzResearch.WordTrace]
  refine ⟨40498520987322863520853837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53998027983097151361138449 40498520987322863520853837)
  ·
    refine ⟨15186945370246073820320189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40498520987322863520853837 15186945370246073820320189)
    ·
      refine ⟨5695104513842277682620071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15186945370246073820320189 5695104513842277682620071)
      ·
        refine ⟨8542656770763416523930107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5695104513842277682620071 8542656770763416523930107)
        ·
          refine ⟨12813985156145124785895161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8542656770763416523930107 12813985156145124785895161)
          ·
            refine ⟨9610488867108843589421371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12813985156145124785895161 9610488867108843589421371)
            ·
              refine ⟨14415733300663265384132057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9610488867108843589421371 14415733300663265384132057)
              ·
                refine ⟨10811799975497449038099043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14415733300663265384132057 10811799975497449038099043)
                ·
                  refine ⟨16217699963246173557148565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10811799975497449038099043 16217699963246173557148565)
                  ·
                    refine ⟨760204685777164385491339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16217699963246173557148565 760204685777164385491339)
                    ·
                      rfl

theorem cell22_2220740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_2220740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220740 prefixEnd_2220740 := by exact prefixLift 2220740
  have htrace : WordTrace (prefixWord ++ tailWord_2220740) baseStart_2220740 baseEnd_2220740 := by
    simpa [prefixWord, tailWord_2220740, baseEnd_2220740] using wordTrace_append hprefix tailTrace_2220740
  have hstable : (prefixWord ++ tailWord_2220740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220740).length < 2 ^ (prefixWord ++ tailWord_2220740).sum := by decide
  have hdescent : baseEnd_2220740 < baseStart_2220740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220753 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 2, 7]
def baseStart_2220753 : Nat := 118140960795 + 2220753 * 2 ^ 59
def prefixEnd_2220753 : Nat := 4983230072969 + 3 ^ 40 * 2220753 * 2
def baseEnd_2220753 : Nat := 760209135942836684916299

theorem tailTrace_2220753 : CollatzResearch.WordTrace tailWord_2220753 prefixEnd_2220753 760209135942836684916299 := by
  unfold tailWord_2220753
  simp only [CollatzResearch.WordTrace]
  refine ⟨80997516123598630261930913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53998344082399086841287275 80997516123598630261930913)
  ·
    refine ⟨60748137092698972696448185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80997516123598630261930913 60748137092698972696448185)
    ·
      refine ⟨45561102819524229522336139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60748137092698972696448185 45561102819524229522336139)
      ·
        refine ⟨68341654229286344283504209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45561102819524229522336139 68341654229286344283504209)
        ·
          refine ⟨51256240671964758212628157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68341654229286344283504209 51256240671964758212628157)
          ·
            refine ⟨19221090251986784329735559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51256240671964758212628157 19221090251986784329735559)
            ·
              refine ⟨28831635377980176494603339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19221090251986784329735559 28831635377980176494603339)
              ·
                refine ⟨43247453066970264741905009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28831635377980176494603339 43247453066970264741905009)
                ·
                  refine ⟨32435589800227698556428757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43247453066970264741905009 32435589800227698556428757)
                  ·
                    refine ⟨760209135942836684916299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32435589800227698556428757 760209135942836684916299)
                    ·
                      rfl

theorem cell22_2220753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_2220753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220753 prefixEnd_2220753 := by exact prefixLift 2220753
  have htrace : WordTrace (prefixWord ++ tailWord_2220753) baseStart_2220753 baseEnd_2220753 := by
    simpa [prefixWord, tailWord_2220753, baseEnd_2220753] using wordTrace_append hprefix tailTrace_2220753
  have hstable : (prefixWord ++ tailWord_2220753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220753).length < 2 ^ (prefixWord ++ tailWord_2220753).sum := by decide
  have hdescent : baseEnd_2220753 < baseStart_2220753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220768 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 1, 8]
def baseStart_2220768 : Nat := 118140960795 + 2220768 * 2 ^ 59
def prefixEnd_2220768 : Nat := 4983230072969 + 3 ^ 40 * 2220768 * 2
def baseEnd_2220768 : Nat := 760214270749381645791253

theorem tailTrace_2220768 : CollatzResearch.WordTrace tailWord_2220768 prefixEnd_2220768 760214270749381645791253 := by
  unfold tailWord_2220768
  simp only [CollatzResearch.WordTrace]
  refine ⟨40499031609272143911863479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53998708812362858549151305 40499031609272143911863479)
  ·
    refine ⟨60748547413908215867795219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40499031609272143911863479 60748547413908215867795219)
    ·
      refine ⟨91122821120862323801692829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60748547413908215867795219 91122821120862323801692829)
      ·
        refine ⟨34171057920323371425634811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91122821120862323801692829 34171057920323371425634811)
        ·
          refine ⟨51256586880485057138452217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34171057920323371425634811 51256586880485057138452217)
          ·
            refine ⟨38442440160363792853839163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51256586880485057138452217 38442440160363792853839163)
            ·
              refine ⟨57663660240545689280758745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38442440160363792853839163 57663660240545689280758745)
              ·
                refine ⟨43247745180409266960569059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57663660240545689280758745 43247745180409266960569059)
                ·
                  refine ⟨64871617770613900440853589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43247745180409266960569059 64871617770613900440853589)
                  ·
                    refine ⟨760214270749381645791253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64871617770613900440853589 760214270749381645791253)
                    ·
                      rfl

theorem cell22_2220768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_2220768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220768 prefixEnd_2220768 := by exact prefixLift 2220768
  have htrace : WordTrace (prefixWord ++ tailWord_2220768) baseStart_2220768 baseEnd_2220768 := by
    simpa [prefixWord, tailWord_2220768, baseEnd_2220768] using wordTrace_append hprefix tailTrace_2220768
  have hstable : (prefixWord ++ tailWord_2220768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220768).length < 2 ^ (prefixWord ++ tailWord_2220768).sum := by decide
  have hdescent : baseEnd_2220768 < baseStart_2220768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220881 : List Nat := [1, 2, 2, 1, 6, 2, 2, 1, 1, 4]
def baseStart_2220881 : Nat := 118140960795 + 2220881 * 2 ^ 59
def prefixEnd_2220881 : Nat := 4983230072969 + 3 ^ 40 * 2220881 * 2
def baseEnd_2220881 : Nat := 760252952958687017715907

theorem tailTrace_2220881 : CollatzResearch.WordTrace tailWord_2220881 prefixEnd_2220881 760252952958687017715907 := by
  unfold tailWord_2220881
  simp only [CollatzResearch.WordTrace]
  refine ⟨81002184667134908122590497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54001456444756605415060331 81002184667134908122590497)
  ·
    refine ⟨60751638500351181091942873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81002184667134908122590497 60751638500351181091942873)
    ·
      refine ⟨45563728875263385818957155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60751638500351181091942873 45563728875263385818957155)
      ·
        refine ⟨68345593312895078728435733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45563728875263385818957155 68345593312895078728435733)
        ·
          refine ⟨3203699686541956815395425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 68345593312895078728435733 3203699686541956815395425)
          ·
            refine ⟨2402774764906467611546569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3203699686541956815395425 2402774764906467611546569)
            ·
              refine ⟨1802081073679850708659927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2402774764906467611546569 1802081073679850708659927)
              ·
                refine ⟨2703121610519776062989891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1802081073679850708659927 2703121610519776062989891)
                ·
                  refine ⟨4054682415779664094484837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2703121610519776062989891 4054682415779664094484837)
                  ·
                    refine ⟨760252952958687017715907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4054682415779664094484837 760252952958687017715907)
                    ·
                      rfl

theorem cell22_2220881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 1, 4].length) (baseStart_2220881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220881 prefixEnd_2220881 := by exact prefixLift 2220881
  have htrace : WordTrace (prefixWord ++ tailWord_2220881) baseStart_2220881 baseEnd_2220881 := by
    simpa [prefixWord, tailWord_2220881, baseEnd_2220881] using wordTrace_append hprefix tailTrace_2220881
  have hstable : (prefixWord ++ tailWord_2220881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220881).length < 2 ^ (prefixWord ++ tailWord_2220881).sum := by decide
  have hdescent : baseEnd_2220881 < baseStart_2220881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220890 : List Nat := [3, 1, 1, 2, 1, 5, 9]
def baseStart_2220890 : Nat := 118140960795 + 2220890 * 2 ^ 59
def prefixEnd_2220890 : Nat := 4983230072969 + 3 ^ 40 * 2220890 * 2
def baseEnd_2220890 : Nat := 28157630883059777564477

theorem tailTrace_2220890 : CollatzResearch.WordTrace tailWord_2220890 prefixEnd_2220890 28157630883059777564477 := by
  unfold tailWord_2220890
  simp only [CollatzResearch.WordTrace]
  refine ⟨20250628231025575664917031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54001675282734868439778749 20250628231025575664917031)
  ·
    refine ⟨30375942346538363497375547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20250628231025575664917031 30375942346538363497375547)
    ·
      refine ⟨45563913519807545246063321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30375942346538363497375547 45563913519807545246063321)
      ·
        refine ⟨34172935139855658934547491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45563913519807545246063321 34172935139855658934547491)
        ·
          refine ⟨51259402709783488401821237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34172935139855658934547491 51259402709783488401821237)
          ·
            refine ⟨4805569004042202037670741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51259402709783488401821237 4805569004042202037670741)
            ·
              refine ⟨28157630883059777564477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4805569004042202037670741 28157630883059777564477)
              ·
                rfl

theorem cell22_2220890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 9].length) (baseStart_2220890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220890 prefixEnd_2220890 := by exact prefixLift 2220890
  have htrace : WordTrace (prefixWord ++ tailWord_2220890) baseStart_2220890 baseEnd_2220890 := by
    simpa [prefixWord, tailWord_2220890, baseEnd_2220890] using wordTrace_append hprefix tailTrace_2220890
  have hstable : (prefixWord ++ tailWord_2220890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220890).length < 2 ^ (prefixWord ++ tailWord_2220890).sum := by decide
  have hdescent : baseEnd_2220890 < baseStart_2220890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220930 : List Nat := [3, 4, 2, 2, 1, 2, 1, 3, 4]
def baseStart_2220930 : Nat := 118140960795 + 2220930 * 2 ^ 59
def prefixEnd_2220930 : Nat := 4983230072969 + 3 ^ 40 * 2220930 * 2
def baseEnd_2220930 : Nat := 253423242220022407746919

theorem tailTrace_2220930 : CollatzResearch.WordTrace tailWord_2220930 prefixEnd_2220930 253423242220022407746919 := by
  unfold tailWord_2220930
  simp only [CollatzResearch.WordTrace]
  refine ⟨20250992960989347372781061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54002647895971592994082829 20250992960989347372781061)
  ·
    refine ⟨3797061180185502632396449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20250992960989347372781061 3797061180185502632396449)
    ·
      refine ⟨2847795885139126974297337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3797061180185502632396449 2847795885139126974297337)
      ·
        refine ⟨2135846913854345230723003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2847795885139126974297337 2135846913854345230723003)
        ·
          refine ⟨3203770370781517846084505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2135846913854345230723003 3203770370781517846084505)
          ·
            refine ⟨2402827778086138384563379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3203770370781517846084505 2402827778086138384563379)
            ·
              refine ⟨3604241667129207576845069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2402827778086138384563379 3604241667129207576845069)
              ·
                refine ⟨1351590625173452841316901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3604241667129207576845069 1351590625173452841316901)
                ·
                  refine ⟨253423242220022407746919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1351590625173452841316901 253423242220022407746919)
                  ·
                    rfl

theorem cell22_2220930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_2220930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220930 prefixEnd_2220930 := by exact prefixLift 2220930
  have htrace : WordTrace (prefixWord ++ tailWord_2220930) baseStart_2220930 baseEnd_2220930 := by
    simpa [prefixWord, tailWord_2220930, baseEnd_2220930] using wordTrace_append hprefix tailTrace_2220930
  have hstable : (prefixWord ++ tailWord_2220930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220930).length < 2 ^ (prefixWord ++ tailWord_2220930).sum := by decide
  have hdescent : baseEnd_2220930 < baseStart_2220930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220965 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 1, 10]
def baseStart_2220965 : Nat := 118140960795 + 2220965 * 2 ^ 59
def prefixEnd_2220965 : Nat := 4983230072969 + 3 ^ 40 * 2220965 * 2
def baseEnd_2220965 : Nat := 760281707875338798615649

theorem tailTrace_2220965 : CollatzResearch.WordTrace tailWord_2220965 prefixEnd_2220965 760281707875338798615649 := by
  unfold tailWord_2220965
  simp only [CollatzResearch.WordTrace]
  refine ⟨81005248398830590468648349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54003498932553726979098899 81005248398830590468648349)
  ·
    refine ⟨30376968149561471425743131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81005248398830590468648349 30376968149561471425743131)
    ·
      refine ⟨45565452224342207138614697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30376968149561471425743131 45565452224342207138614697)
      ·
        refine ⟨34174089168256655353961023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45565452224342207138614697 34174089168256655353961023)
        ·
          refine ⟨51261133752384983030941535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34174089168256655353961023 51261133752384983030941535)
          ·
            refine ⟨76891700628577474546412303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51261133752384983030941535 76891700628577474546412303)
            ·
              refine ⟨115337550942866211819618455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76891700628577474546412303 115337550942866211819618455)
              ·
                refine ⟨173006326414299317729427683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115337550942866211819618455 173006326414299317729427683)
                ·
                  refine ⟨259509489621448976594141525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173006326414299317729427683 259509489621448976594141525)
                  ·
                    refine ⟨760281707875338798615649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 259509489621448976594141525 760281707875338798615649)
                    ·
                      rfl

theorem cell22_2220965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_2220965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2220965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2220965 prefixEnd_2220965 := by exact prefixLift 2220965
  have htrace : WordTrace (prefixWord ++ tailWord_2220965) baseStart_2220965 baseEnd_2220965 := by
    simpa [prefixWord, tailWord_2220965, baseEnd_2220965] using wordTrace_append hprefix tailTrace_2220965
  have hstable : (prefixWord ++ tailWord_2220965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220965).length < 2 ^ (prefixWord ++ tailWord_2220965).sum := by decide
  have hdescent : baseEnd_2220965 < baseStart_2220965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221027 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 1, 6]
def baseStart_2221027 : Nat := 118140960795 + 2221027 * 2 ^ 59
def prefixEnd_2221027 : Nat := 4983230072969 + 3 ^ 40 * 2221027 * 2
def baseEnd_2221027 : Nat := 760302931742391303565459

theorem tailTrace_2221027 : CollatzResearch.WordTrace tailWord_2221027 prefixEnd_2221027 760302931742391303565459 := by
  unfold tailWord_2221027
  simp only [CollatzResearch.WordTrace]
  refine ⟨81007509724605975057405335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54005006483070650038270223 81007509724605975057405335)
  ·
    refine ⟨121511264586908962586108003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81007509724605975057405335 121511264586908962586108003)
    ·
      refine ⟨182266896880363443879162005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121511264586908962586108003 182266896880363443879162005)
      ·
        refine ⟨8543760791267036431835719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 182266896880363443879162005 8543760791267036431835719)
        ·
          refine ⟨12815641186900554647753579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8543760791267036431835719 12815641186900554647753579)
          ·
            refine ⟨19223461780350831971630369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12815641186900554647753579 19223461780350831971630369)
            ·
              refine ⟨14417596335263123978722777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19223461780350831971630369 14417596335263123978722777)
              ·
                refine ⟨10813197251447342984042083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14417596335263123978722777 10813197251447342984042083)
                ·
                  refine ⟨16219795877171014476063125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10813197251447342984042083 16219795877171014476063125)
                  ·
                    refine ⟨760302931742391303565459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16219795877171014476063125 760302931742391303565459)
                    ·
                      rfl

theorem cell22_2221027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 6].length) (baseStart_2221027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221027 prefixEnd_2221027 := by exact prefixLift 2221027
  have htrace : WordTrace (prefixWord ++ tailWord_2221027) baseStart_2221027 baseEnd_2221027 := by
    simpa [prefixWord, tailWord_2221027, baseEnd_2221027] using wordTrace_append hprefix tailTrace_2221027
  have hstable : (prefixWord ++ tailWord_2221027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221027).length < 2 ^ (prefixWord ++ tailWord_2221027).sum := by decide
  have hdescent : baseEnd_2221027 < baseStart_2221027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221134 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 3, 4]
def baseStart_2221134 : Nat := 118140960795 + 2221134 * 2 ^ 59
def prefixEnd_2221134 : Nat := 4983230072969 + 3 ^ 40 * 2221134 * 2
def baseEnd_2221134 : Nat := 760339560029078691140131

theorem tailTrace_2221134 : CollatzResearch.WordTrace tailWord_2221134 prefixEnd_2221134 760339560029078691140131 := by
  unfold tailWord_2221134
  simp only [CollatzResearch.WordTrace]
  refine ⟨10126426541902291541443807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54007608223478888221033637 10126426541902291541443807)
  ·
    refine ⟨15189639812853437312165711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10126426541902291541443807 15189639812853437312165711)
    ·
      refine ⟨22784459719280155968248567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15189639812853437312165711 22784459719280155968248567)
      ·
        refine ⟨34176689578920233952372851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22784459719280155968248567 34176689578920233952372851)
        ·
          refine ⟨51265034368380350928559277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34176689578920233952372851 51265034368380350928559277)
          ·
            refine ⟨19224387888142631598209729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51265034368380350928559277 19224387888142631598209729)
            ·
              refine ⟨14418290916106973698657297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19224387888142631598209729 14418290916106973698657297)
              ·
                refine ⟨10813718187080230273992973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14418290916106973698657297 10813718187080230273992973)
                ·
                  refine ⟨4055144320155086352747365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10813718187080230273992973 4055144320155086352747365)
                  ·
                    refine ⟨760339560029078691140131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4055144320155086352747365 760339560029078691140131)
                    ·
                      rfl

theorem cell22_2221134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_2221134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221134 prefixEnd_2221134 := by exact prefixLift 2221134
  have htrace : WordTrace (prefixWord ++ tailWord_2221134) baseStart_2221134 baseEnd_2221134 := by
    simpa [prefixWord, tailWord_2221134, baseEnd_2221134] using wordTrace_append hprefix tailTrace_2221134
  have hstable : (prefixWord ++ tailWord_2221134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221134).length < 2 ^ (prefixWord ++ tailWord_2221134).sum := by decide
  have hdescent : baseEnd_2221134 < baseStart_2221134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221138 : List Nat := [3, 2, 2, 1, 3, 3, 2, 1, 5]
def baseStart_2221138 : Nat := 118140960795 + 2221138 * 2 ^ 59
def prefixEnd_2221138 : Nat := 4983230072969 + 3 ^ 40 * 2221138 * 2
def baseEnd_2221138 : Nat := 253446976436941338013373

theorem tailTrace_2221138 : CollatzResearch.WordTrace tailWord_2221138 prefixEnd_2221138 253446976436941338013373 := by
  unfold tailWord_2221138
  simp only [CollatzResearch.WordTrace]
  refine ⟨20252889556800960253674017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54007705484802560676464045 20252889556800960253674017)
  ·
    refine ⟨15189667167600720190255513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20252889556800960253674017 15189667167600720190255513)
    ·
      refine ⟨11392250375700540142691635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15189667167600720190255513 11392250375700540142691635)
      ·
        refine ⟨17088375563550810214037453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11392250375700540142691635 17088375563550810214037453)
        ·
          refine ⟨6408140836331553830264045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17088375563550810214037453 6408140836331553830264045)
          ·
            refine ⟨2403052813624332686349017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6408140836331553830264045 2403052813624332686349017)
            ·
              refine ⟨1802289610218249514761763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2403052813624332686349017 1802289610218249514761763)
              ·
                refine ⟨2703434415327374272142645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1802289610218249514761763 2703434415327374272142645)
                ·
                  refine ⟨253446976436941338013373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2703434415327374272142645 253446976436941338013373)
                  ·
                    rfl

theorem cell22_2221138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_2221138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221138 prefixEnd_2221138 := by exact prefixLift 2221138
  have htrace : WordTrace (prefixWord ++ tailWord_2221138) baseStart_2221138 baseEnd_2221138 := by
    simpa [prefixWord, tailWord_2221138, baseEnd_2221138] using wordTrace_append hprefix tailTrace_2221138
  have hstable : (prefixWord ++ tailWord_2221138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221138).length < 2 ^ (prefixWord ++ tailWord_2221138).sum := by decide
  have hdescent : baseEnd_2221138 < baseStart_2221138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221164 : List Nat := [2, 2, 1, 1, 3, 2, 3, 2, 1, 5]
def baseStart_2221164 : Nat := 118140960795 + 2221164 * 2 ^ 59
def prefixEnd_2221164 : Nat := 4983230072969 + 3 ^ 40 * 2221164 * 2
def baseEnd_2221164 : Nat := 760349829642168612890039

theorem tailTrace_2221164 : CollatzResearch.WordTrace tailWord_2221164 prefixEnd_2221164 760349829642168612890039 := by
  unfold tailWord_2221164
  simp only [CollatzResearch.WordTrace]
  refine ⟨40506253262554823727571273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54008337683406431636761697 40506253262554823727571273)
  ·
    refine ⟨30379689946916117795678455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40506253262554823727571273 30379689946916117795678455)
    ·
      refine ⟨45569534920374176693517683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30379689946916117795678455 45569534920374176693517683)
      ·
        refine ⟨68354302380561265040276525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45569534920374176693517683 68354302380561265040276525)
        ·
          refine ⟨25632863392710474390103697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68354302380561265040276525 25632863392710474390103697)
          ·
            refine ⟨19224647544532855792577773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25632863392710474390103697 19224647544532855792577773)
            ·
              refine ⟨7209242829199820922216665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19224647544532855792577773 7209242829199820922216665)
              ·
                refine ⟨5406932121899865691662499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7209242829199820922216665 5406932121899865691662499)
                ·
                  refine ⟨8110398182849798537493749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5406932121899865691662499 8110398182849798537493749)
                  ·
                    refine ⟨760349829642168612890039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8110398182849798537493749 760349829642168612890039)
                    ·
                      rfl

theorem cell22_2221164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_2221164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221164 prefixEnd_2221164 := by exact prefixLift 2221164
  have htrace : WordTrace (prefixWord ++ tailWord_2221164) baseStart_2221164 baseEnd_2221164 := by
    simpa [prefixWord, tailWord_2221164, baseEnd_2221164] using wordTrace_append hprefix tailTrace_2221164
  have hstable : (prefixWord ++ tailWord_2221164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221164).length < 2 ^ (prefixWord ++ tailWord_2221164).sum := by decide
  have hdescent : baseEnd_2221164 < baseStart_2221164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221177 : List Nat := [1, 2, 1, 3, 15]
def baseStart_2221177 : Nat := 118140960795 + 2221177 * 2 ^ 59
def prefixEnd_2221177 : Nat := 4983230072969 + 3 ^ 40 * 2221177 * 2
def baseEnd_2221177 : Nat := 3129029958056958486893

theorem tailTrace_2221177 : CollatzResearch.WordTrace tailWord_2221177 prefixEnd_2221177 3129029958056958486893 := by
  unfold tailWord_2221177
  simp only [CollatzResearch.WordTrace]
  refine ⟨81012980674062550675365785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54008653782708367116910523 81012980674062550675365785)
  ·
    refine ⟨60759735505546913006524339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81012980674062550675365785 60759735505546913006524339)
    ·
      refine ⟨91139603258320369509786509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60759735505546913006524339 91139603258320369509786509)
      ·
        refine ⟨34177351221870138566169941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91139603258320369509786509 34177351221870138566169941)
        ·
          refine ⟨3129029958056958486893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 34177351221870138566169941 3129029958056958486893)
          ·
            rfl

theorem cell22_2221177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 15].length) (baseStart_2221177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221177 prefixEnd_2221177 := by exact prefixLift 2221177
  have htrace : WordTrace (prefixWord ++ tailWord_2221177) baseStart_2221177 baseEnd_2221177 := by
    simpa [prefixWord, tailWord_2221177, baseEnd_2221177] using wordTrace_append hprefix tailTrace_2221177
  have hstable : (prefixWord ++ tailWord_2221177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221177).length < 2 ^ (prefixWord ++ tailWord_2221177).sum := by decide
  have hdescent : baseEnd_2221177 < baseStart_2221177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221198 : List Nat := [4, 1, 1, 3, 2, 1, 2, 3, 2, 3]
def baseStart_2221198 : Nat := 118140960795 + 2221198 * 2 ^ 59
def prefixEnd_2221198 : Nat := 4983230072969 + 3 ^ 40 * 2221198 * 2
def baseEnd_2221198 : Nat := 760361468537003857539935

theorem tailTrace_2221198 : CollatzResearch.WordTrace tailWord_2221198 prefixEnd_2221198 760361468537003857539935 := by
  unfold tailWord_2221198
  simp only [CollatzResearch.WordTrace]
  refine ⟨10126718325873308907735031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54009164404657647507920165 10126718325873308907735031)
  ·
    refine ⟨15190077488809963361602547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10126718325873308907735031 15190077488809963361602547)
    ·
      refine ⟨22785116233214945042403821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15190077488809963361602547 22785116233214945042403821)
      ·
        refine ⟨8544418587455604390901433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22785116233214945042403821 8544418587455604390901433)
        ·
          refine ⟨6408313940591703293176075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8544418587455604390901433 6408313940591703293176075)
          ·
            refine ⟨9612470910887554939764113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6408313940591703293176075 9612470910887554939764113)
            ·
              refine ⟨7209353183165666204823085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9612470910887554939764113 7209353183165666204823085)
              ·
                refine ⟨2703507443687124826808657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7209353183165666204823085 2703507443687124826808657)
                ·
                  refine ⟨2027630582765343620106493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2703507443687124826808657 2027630582765343620106493)
                  ·
                    refine ⟨760361468537003857539935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2027630582765343620106493 760361468537003857539935)
                    ·
                      rfl

theorem cell22_2221198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_2221198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221198 prefixEnd_2221198 := by exact prefixLift 2221198
  have htrace : WordTrace (prefixWord ++ tailWord_2221198) baseStart_2221198 baseEnd_2221198 := by
    simpa [prefixWord, tailWord_2221198, baseEnd_2221198] using wordTrace_append hprefix tailTrace_2221198
  have hstable : (prefixWord ++ tailWord_2221198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221198).length < 2 ^ (prefixWord ++ tailWord_2221198).sum := by decide
  have hdescent : baseEnd_2221198 < baseStart_2221198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221239 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 7]
def baseStart_2221239 : Nat := 118140960795 + 2221239 * 2 ^ 59
def prefixEnd_2221239 : Nat := 4983230072969 + 3 ^ 40 * 2221239 * 2
def baseEnd_2221239 : Nat := 253458501224964472421603

theorem tailTrace_2221239 : CollatzResearch.WordTrace tailWord_2221239 prefixEnd_2221239 253458501224964472421603 := by
  unfold tailWord_2221239
  simp only [CollatzResearch.WordTrace]
  refine ⟨81015241999837935264122771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54010161333225290176081847 81015241999837935264122771)
  ·
    refine ⟨121522862999756902896184157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81015241999837935264122771 121522862999756902896184157)
    ·
      refine ⟨45571073624908838586069059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121522862999756902896184157 45571073624908838586069059)
      ·
        refine ⟨68356610437363257879103589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45571073624908838586069059 68356610437363257879103589)
        ·
          refine ⟨12816864457005610852331923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68356610437363257879103589 12816864457005610852331923)
          ·
            refine ⟨19225296685508416278497885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12816864457005610852331923 19225296685508416278497885)
            ·
              refine ⟨7209486257065656104436707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19225296685508416278497885 7209486257065656104436707)
              ·
                refine ⟨10814229385598484156655061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7209486257065656104436707 10814229385598484156655061)
                ·
                  refine ⟨253458501224964472421603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10814229385598484156655061 253458501224964472421603)
                  ·
                    rfl

theorem cell22_2221239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 7].length) (baseStart_2221239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221239 prefixEnd_2221239 := by exact prefixLift 2221239
  have htrace : WordTrace (prefixWord ++ tailWord_2221239) baseStart_2221239 baseEnd_2221239 := by
    simpa [prefixWord, tailWord_2221239, baseEnd_2221239] using wordTrace_append hprefix tailTrace_2221239
  have hstable : (prefixWord ++ tailWord_2221239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221239).length < 2 ^ (prefixWord ++ tailWord_2221239).sum := by decide
  have hdescent : baseEnd_2221239 < baseStart_2221239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221284 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 8]
def baseStart_2221284 : Nat := 118140960795 + 2221284 * 2 ^ 59
def prefixEnd_2221284 : Nat := 4983230072969 + 3 ^ 40 * 2221284 * 2
def baseEnd_2221284 : Nat := 253463636031509433296557

theorem tailTrace_2221284 : CollatzResearch.WordTrace tailWord_2221284 prefixEnd_2221284 253463636031509433296557 := by
  unfold tailWord_2221284
  simp only [CollatzResearch.WordTrace]
  refine ⟨40508441642337453974755453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54011255523116605299673937 40508441642337453974755453)
  ·
    refine ⟨15190665615876545240533295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40508441642337453974755453 15190665615876545240533295)
    ·
      refine ⟨22785998423814817860799943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15190665615876545240533295 22785998423814817860799943)
      ·
        refine ⟨34178997635722226791199915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22785998423814817860799943 34178997635722226791199915)
        ·
          refine ⟨51268496453583340186799873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34178997635722226791199915 51268496453583340186799873)
          ·
            refine ⟨38451372340187505140099905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51268496453583340186799873 38451372340187505140099905)
            ·
              refine ⟨28838529255140628855074929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38451372340187505140099905 28838529255140628855074929)
              ·
                refine ⟨21628896941355471641306197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28838529255140628855074929 21628896941355471641306197)
                ·
                  refine ⟨253463636031509433296557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21628896941355471641306197 253463636031509433296557)
                  ·
                    rfl

theorem cell22_2221284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_2221284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221284 prefixEnd_2221284 := by exact prefixLift 2221284
  have htrace : WordTrace (prefixWord ++ tailWord_2221284) baseStart_2221284 baseEnd_2221284 := by
    simpa [prefixWord, tailWord_2221284, baseEnd_2221284] using wordTrace_append hprefix tailTrace_2221284
  have hstable : (prefixWord ++ tailWord_2221284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221284).length < 2 ^ (prefixWord ++ tailWord_2221284).sum := by decide
  have hdescent : baseEnd_2221284 < baseStart_2221284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221320 : List Nat := [2, 1, 3, 2, 4, 2, 1, 2, 1, 4]
def baseStart_2221320 : Nat := 118140960795 + 2221320 * 2 ^ 59
def prefixEnd_2221320 : Nat := 4983230072969 + 3 ^ 40 * 2221320 * 2
def baseEnd_2221320 : Nat := 760403231630236205989561

theorem tailTrace_2221320 : CollatzResearch.WordTrace tailWord_2221320 prefixEnd_2221320 760403231630236205989561 := by
  unfold tailWord_2221320
  simp only [CollatzResearch.WordTrace]
  refine ⟨40509098156272243048910707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54012130875029657398547609 40509098156272243048910707)
  ·
    refine ⟨60763647234408364573366061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40509098156272243048910707 60763647234408364573366061)
    ·
      refine ⟨22786367712903136715012273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60763647234408364573366061 22786367712903136715012273)
      ·
        refine ⟨17089775784677352536259205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22786367712903136715012273 17089775784677352536259205)
        ·
          refine ⟨3204332959627003600548601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17089775784677352536259205 3204332959627003600548601)
          ·
            refine ⟨2403249719720252700411451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3204332959627003600548601 2403249719720252700411451)
            ·
              refine ⟨3604874579580379050617177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2403249719720252700411451 3604874579580379050617177)
              ·
                refine ⟨2703655934685284287962883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3604874579580379050617177 2703655934685284287962883)
                ·
                  refine ⟨4055483902027926431944325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2703655934685284287962883 4055483902027926431944325)
                  ·
                    refine ⟨760403231630236205989561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4055483902027926431944325 760403231630236205989561)
                    ·
                      rfl

theorem cell22_2221320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_2221320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221320 prefixEnd_2221320 := by exact prefixLift 2221320
  have htrace : WordTrace (prefixWord ++ tailWord_2221320) baseStart_2221320 baseEnd_2221320 := by
    simpa [prefixWord, tailWord_2221320, baseEnd_2221320] using wordTrace_append hprefix tailTrace_2221320
  have hstable : (prefixWord ++ tailWord_2221320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221320).length < 2 ^ (prefixWord ++ tailWord_2221320).sum := by decide
  have hdescent : baseEnd_2221320 < baseStart_2221320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221329 : List Nat := [1, 2, 2, 1, 1, 4, 1, 10]
def baseStart_2221329 : Nat := 118140960795 + 2221329 * 2 ^ 59
def prefixEnd_2221329 : Nat := 4983230072969 + 3 ^ 40 * 2221329 * 2
def baseEnd_2221329 : Nat := 84489590279351464723837

theorem tailTrace_2221329 : CollatzResearch.WordTrace tailWord_2221329 prefixEnd_2221329 84489590279351464723837 := by
  unfold tailWord_2221329
  simp only [CollatzResearch.WordTrace]
  refine ⟨81018524569511880634899041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54012349713007920423266027 81018524569511880634899041)
  ·
    refine ⟨60763893427133910476174281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81018524569511880634899041 60763893427133910476174281)
    ·
      refine ⟨45572920070350432857130711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60763893427133910476174281 45572920070350432857130711)
      ·
        refine ⟨68359380105525649285696067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45572920070350432857130711 68359380105525649285696067)
        ·
          refine ⟨102539070158288473928544101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68359380105525649285696067 102539070158288473928544101)
          ·
            refine ⟨19226075654679088861602019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102539070158288473928544101 19226075654679088861602019)
            ·
              refine ⟨28839113482018633292403029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19226075654679088861602019 28839113482018633292403029)
              ·
                refine ⟨84489590279351464723837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28839113482018633292403029 84489590279351464723837)
                ·
                  rfl

theorem cell22_2221329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 10].length) (baseStart_2221329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221329 prefixEnd_2221329 := by exact prefixLift 2221329
  have htrace : WordTrace (prefixWord ++ tailWord_2221329) baseStart_2221329 baseEnd_2221329 := by
    simpa [prefixWord, tailWord_2221329, baseEnd_2221329] using wordTrace_append hprefix tailTrace_2221329
  have hstable : (prefixWord ++ tailWord_2221329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221329).length < 2 ^ (prefixWord ++ tailWord_2221329).sum := by decide
  have hdescent : baseEnd_2221329 < baseStart_2221329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221346 : List Nat := [3, 3, 1, 1, 4, 10]
def baseStart_2221346 : Nat := 118140960795 + 2221346 * 2 ^ 59
def prefixEnd_2221346 : Nat := 4983230072969 + 3 ^ 40 * 2221346 * 2
def baseEnd_2221346 : Nat := 9387804098291121047401

theorem tailTrace_2221346 : CollatzResearch.WordTrace tailWord_2221346 prefixEnd_2221346 9387804098291121047401 := by
  unfold tailWord_2221346
  simp only [CollatzResearch.WordTrace]
  refine ⟨20254786152612573134566973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54012763073633528358845261 20254786152612573134566973)
  ·
    refine ⟨7595544807229714925462615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20254786152612573134566973 7595544807229714925462615)
    ·
      refine ⟨11393317210844572388193923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7595544807229714925462615 11393317210844572388193923)
      ·
        refine ⟨17089975816266858582290885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11393317210844572388193923 17089975816266858582290885)
        ·
          refine ⟨3204370465550035984179541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17089975816266858582290885 3204370465550035984179541)
          ·
            refine ⟨9387804098291121047401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3204370465550035984179541 9387804098291121047401)
            ·
              rfl

theorem cell22_2221346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 10].length) (baseStart_2221346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221346 prefixEnd_2221346 := by exact prefixLift 2221346
  have htrace : WordTrace (prefixWord ++ tailWord_2221346) baseStart_2221346 baseEnd_2221346 := by
    simpa [prefixWord, tailWord_2221346, baseEnd_2221346] using wordTrace_append hprefix tailTrace_2221346
  have hstable : (prefixWord ++ tailWord_2221346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221346).length < 2 ^ (prefixWord ++ tailWord_2221346).sum := by decide
  have hdescent : baseEnd_2221346 < baseStart_2221346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221352 : List Nat := [2, 1, 5, 1, 2, 3, 2, 2, 4]
def baseStart_2221352 : Nat := 118140960795 + 2221352 * 2 ^ 59
def prefixEnd_2221352 : Nat := 4983230072969 + 3 ^ 40 * 2221352 * 2
def baseEnd_2221352 : Nat := 253471395294732929729821

theorem tailTrace_2221352 : CollatzResearch.WordTrace tailWord_2221352 prefixEnd_2221352 253471395294732929729821 := by
  unfold tailWord_2221352
  simp only [CollatzResearch.WordTrace]
  refine ⟨40509681724214277781493155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54012908965619037041990873 40509681724214277781493155)
  ·
    refine ⟨60764522586321416672239733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40509681724214277781493155 60764522586321416672239733)
    ·
      refine ⟨5696673992467632813022475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60764522586321416672239733 5696673992467632813022475)
      ·
        refine ⟨8545010988701449219533713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5696673992467632813022475 8545010988701449219533713)
        ·
          refine ⟨6408758241526086914650285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8545010988701449219533713 6408758241526086914650285)
          ·
            refine ⟨2403284340572282592993857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6408758241526086914650285 2403284340572282592993857)
            ·
              refine ⟨1802463255429211944745393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2403284340572282592993857 1802463255429211944745393)
              ·
                refine ⟨1351847441571908958559045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1802463255429211944745393 1351847441571908958559045)
                ·
                  refine ⟨253471395294732929729821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1351847441571908958559045 253471395294732929729821)
                  ·
                    rfl

theorem cell22_2221352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 4].length) (baseStart_2221352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221352 prefixEnd_2221352 := by exact prefixLift 2221352
  have htrace : WordTrace (prefixWord ++ tailWord_2221352) baseStart_2221352 baseEnd_2221352 := by
    simpa [prefixWord, tailWord_2221352, baseEnd_2221352] using wordTrace_append hprefix tailTrace_2221352
  have hstable : (prefixWord ++ tailWord_2221352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221352).length < 2 ^ (prefixWord ++ tailWord_2221352).sum := by decide
  have hdescent : baseEnd_2221352 < baseStart_2221352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221380 : List Nat := [2, 3, 4, 1, 1, 2, 3, 6]
def baseStart_2221380 : Nat := 118140960795 + 2221380 * 2 ^ 59
def prefixEnd_2221380 : Nat := 4983230072969 + 3 ^ 40 * 2221380 * 2
def baseEnd_2221380 : Nat := 84491530095157338832153

theorem tailTrace_2221380 : CollatzResearch.WordTrace tailWord_2221380 prefixEnd_2221380 84491530095157338832153 := by
  unfold tailWord_2221380
  simp only [CollatzResearch.WordTrace]
  refine ⟨40510192346163558172502797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54013589794884744230003729 40510192346163558172502797)
  ·
    refine ⟨15191322129811334314688549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40510192346163558172502797 15191322129811334314688549)
    ·
      refine ⟨2848372899339625184004103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15191322129811334314688549 2848372899339625184004103)
      ·
        refine ⟨4272559349009437776006155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2848372899339625184004103 4272559349009437776006155)
        ·
          refine ⟨6408839023514156664009233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4272559349009437776006155 6408839023514156664009233)
          ·
            refine ⟨4806629267635617498006925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6408839023514156664009233 4806629267635617498006925)
            ·
              refine ⟨1802485975363356561752597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4806629267635617498006925 1802485975363356561752597)
              ·
                refine ⟨84491530095157338832153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1802485975363356561752597 84491530095157338832153)
                ·
                  rfl

theorem cell22_2221380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 6].length) (baseStart_2221380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221380 prefixEnd_2221380 := by exact prefixLift 2221380
  have htrace : WordTrace (prefixWord ++ tailWord_2221380) baseStart_2221380 baseEnd_2221380 := by
    simpa [prefixWord, tailWord_2221380, baseEnd_2221380] using wordTrace_append hprefix tailTrace_2221380
  have hstable : (prefixWord ++ tailWord_2221380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221380).length < 2 ^ (prefixWord ++ tailWord_2221380).sum := by decide
  have hdescent : baseEnd_2221380 < baseStart_2221380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221382 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_2221382 : Nat := 118140960795 + 2221382 * 2 ^ 59
def prefixEnd_2221382 : Nat := 4983230072969 + 3 ^ 40 * 2221382 * 2
def baseEnd_2221382 : Nat := 760424455497288710939371

theorem tailTrace_2221382 : CollatzResearch.WordTrace tailWord_2221382 prefixEnd_2221382 760424455497288710939371 := by
  unfold tailWord_2221382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2531889301197495958955575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54013638425546580457718933 2531889301197495958955575)
  ·
    refine ⟨3797833951796243938433363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2531889301197495958955575 3797833951796243938433363)
    ·
      refine ⟨5696750927694365907650045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3797833951796243938433363 5696750927694365907650045)
      ·
        refine ⟨2136281597885387215368767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5696750927694365907650045 2136281597885387215368767)
        ·
          refine ⟨3204422396828080823053151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2136281597885387215368767 3204422396828080823053151)
          ·
            refine ⟨4806633595242121234579727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3204422396828080823053151 4806633595242121234579727)
            ·
              refine ⟨7209950392863181851869591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4806633595242121234579727 7209950392863181851869591)
              ·
                refine ⟨10814925589294772777804387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7209950392863181851869591 10814925589294772777804387)
                ·
                  refine ⟨16222388383942159166706581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10814925589294772777804387 16222388383942159166706581)
                  ·
                    refine ⟨760424455497288710939371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16222388383942159166706581 760424455497288710939371)
                    ·
                      rfl

theorem cell22_2221382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_2221382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221382 prefixEnd_2221382 := by exact prefixLift 2221382
  have htrace : WordTrace (prefixWord ++ tailWord_2221382) baseStart_2221382 baseEnd_2221382 := by
    simpa [prefixWord, tailWord_2221382, baseEnd_2221382] using wordTrace_append hprefix tailTrace_2221382
  have hstable : (prefixWord ++ tailWord_2221382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221382).length < 2 ^ (prefixWord ++ tailWord_2221382).sum := by decide
  have hdescent : baseEnd_2221382 < baseStart_2221382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221395 : List Nat := [1, 1, 1, 2, 1, 1, 8, 3, 1, 3]
def baseStart_2221395 : Nat := 118140960795 + 2221395 * 2 ^ 59
def prefixEnd_2221395 : Nat := 4983230072969 + 3 ^ 40 * 2221395 * 2
def baseEnd_2221395 : Nat := 760428905662961010364331

theorem tailTrace_2221395 : CollatzResearch.WordTrace tailWord_2221395 prefixEnd_2221395 760428905662961010364331 := by
  unfold tailWord_2221395
  simp only [CollatzResearch.WordTrace]
  refine ⟨81020931787272773906801639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54013954524848515937867759 81020931787272773906801639)
  ·
    refine ⟨121531397680909160860202459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81020931787272773906801639 121531397680909160860202459)
    ·
      refine ⟨182297096521363741290303689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121531397680909160860202459 182297096521363741290303689)
      ·
        refine ⟨136722822391022805967727767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182297096521363741290303689 136722822391022805967727767)
        ·
          refine ⟨205084233586534208951591651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136722822391022805967727767 205084233586534208951591651)
          ·
            refine ⟨307626350379801313427387477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205084233586534208951591651 307626350379801313427387477)
            ·
              refine ⟨3604996293513296641727197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 307626350379801313427387477 3604996293513296641727197)
              ·
                refine ⟨1351873610067486240647699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3604996293513296641727197 1351873610067486240647699)
                ·
                  refine ⟨2027810415101229360971549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1351873610067486240647699 2027810415101229360971549)
                  ·
                    refine ⟨760428905662961010364331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2027810415101229360971549 760428905662961010364331)
                    ·
                      rfl

theorem cell22_2221395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 1, 3].length) (baseStart_2221395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221395 prefixEnd_2221395 := by exact prefixLift 2221395
  have htrace : WordTrace (prefixWord ++ tailWord_2221395) baseStart_2221395 baseEnd_2221395 := by
    simpa [prefixWord, tailWord_2221395, baseEnd_2221395] using wordTrace_append hprefix tailTrace_2221395
  have hstable : (prefixWord ++ tailWord_2221395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221395).length < 2 ^ (prefixWord ++ tailWord_2221395).sum := by decide
  have hdescent : baseEnd_2221395 < baseStart_2221395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221408 : List Nat := [2, 1, 1, 3, 4, 1, 3, 2, 5]
def baseStart_2221408 : Nat := 118140960795 + 2221408 * 2 ^ 59
def prefixEnd_2221408 : Nat := 4983230072969 + 3 ^ 40 * 2221408 * 2
def baseEnd_2221408 : Nat := 253477785276211103263097

theorem tailTrace_2221408 : CollatzResearch.WordTrace tailWord_2221408 prefixEnd_2221408 253477785276211103263097 := by
  unfold tailWord_2221408
  simp only [CollatzResearch.WordTrace]
  refine ⟨40510702968112838563512439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54014270624150451418016585 40510702968112838563512439)
  ·
    refine ⟨60766054452169257845268659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40510702968112838563512439 60766054452169257845268659)
    ·
      refine ⟨91149081678253886767902989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60766054452169257845268659 91149081678253886767902989)
      ·
        refine ⟨34180905629345207537963621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91149081678253886767902989 34180905629345207537963621)
        ·
          refine ⟨6408919805502226413368179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34180905629345207537963621 6408919805502226413368179)
          ·
            refine ⟨9613379708253339620052269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6408919805502226413368179 9613379708253339620052269)
            ·
              refine ⟨3605017390595002357519601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9613379708253339620052269 3605017390595002357519601)
              ·
                refine ⟨2703763042946251768139701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3605017390595002357519601 2703763042946251768139701)
                ·
                  refine ⟨253477785276211103263097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2703763042946251768139701 253477785276211103263097)
                  ·
                    rfl

theorem cell22_2221408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 5].length) (baseStart_2221408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221408 prefixEnd_2221408 := by exact prefixLift 2221408
  have htrace : WordTrace (prefixWord ++ tailWord_2221408) baseStart_2221408 baseEnd_2221408 := by
    simpa [prefixWord, tailWord_2221408, baseEnd_2221408] using wordTrace_append hprefix tailTrace_2221408
  have hstable : (prefixWord ++ tailWord_2221408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221408).length < 2 ^ (prefixWord ++ tailWord_2221408).sum := by decide
  have hdescent : baseEnd_2221408 < baseStart_2221408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221436 : List Nat := [2, 2, 2, 1, 1, 1, 3, 4, 6]
def baseStart_2221436 : Nat := 118140960795 + 2221436 * 2 ^ 59
def prefixEnd_2221436 : Nat := 4983230072969 + 3 ^ 40 * 2221436 * 2
def baseEnd_2221436 : Nat := 253480980266950190029735

theorem tailTrace_2221436 : CollatzResearch.WordTrace tailWord_2221436 prefixEnd_2221436 253480980266950190029735 := by
  unfold tailWord_2221436
  simp only [CollatzResearch.WordTrace]
  refine ⟨40511213590062118954522081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54014951453416158606029441 40511213590062118954522081)
  ·
    refine ⟨30383410192546589215891561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40511213590062118954522081 30383410192546589215891561)
    ·
      refine ⟨22787557644409941911918671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30383410192546589215891561 22787557644409941911918671)
      ·
        refine ⟨34181336466614912867878007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22787557644409941911918671 34181336466614912867878007)
        ·
          refine ⟨51272004699922369301817011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34181336466614912867878007 51272004699922369301817011)
          ·
            refine ⟨76908007049883553952725517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51272004699922369301817011 76908007049883553952725517)
            ·
              refine ⟨28840502643706332732272069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76908007049883553952725517 28840502643706332732272069)
              ·
                refine ⟨5407594245694937387301013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28840502643706332732272069 5407594245694937387301013)
                ·
                  refine ⟨253480980266950190029735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5407594245694937387301013 253480980266950190029735)
                  ·
                    rfl

theorem cell22_2221436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_2221436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221436 prefixEnd_2221436 := by exact prefixLift 2221436
  have htrace : WordTrace (prefixWord ++ tailWord_2221436) baseStart_2221436 baseEnd_2221436 := by
    simpa [prefixWord, tailWord_2221436, baseEnd_2221436] using wordTrace_append hprefix tailTrace_2221436
  have hstable : (prefixWord ++ tailWord_2221436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221436).length < 2 ^ (prefixWord ++ tailWord_2221436).sum := by decide
  have hdescent : baseEnd_2221436 < baseStart_2221436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221451 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 3, 5]
def baseStart_2221451 : Nat := 118140960795 + 2221451 * 2 ^ 59
def prefixEnd_2221451 : Nat := 4983230072969 + 3 ^ 40 * 2221451 * 2
def baseEnd_2221451 : Nat := 760448075607395530964159

theorem tailTrace_2221451 : CollatzResearch.WordTrace tailWord_2221451 prefixEnd_2221451 760448075607395530964159 := by
  unfold tailWord_2221451
  simp only [CollatzResearch.WordTrace]
  refine ⟨81022974275069895470840207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54015316183379930313893471 81022974275069895470840207)
  ·
    refine ⟨121534461412604843206260311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81022974275069895470840207 121534461412604843206260311)
    ·
      refine ⟨182301692118907264809390467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121534461412604843206260311 182301692118907264809390467)
      ·
        refine ⟨273452538178360897214085701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182301692118907264809390467 273452538178360897214085701)
        ·
          refine ⟨51272350908442668227641069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 273452538178360897214085701 51272350908442668227641069)
          ·
            refine ⟨19227131590666000585365401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51272350908442668227641069 19227131590666000585365401)
            ·
              refine ⟨14420348692999500439024051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19227131590666000585365401 14420348692999500439024051)
              ·
                refine ⟨21630523039499250658536077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14420348692999500439024051 21630523039499250658536077)
                ·
                  refine ⟨8111446139812218996951029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21630523039499250658536077 8111446139812218996951029)
                  ·
                    refine ⟨760448075607395530964159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8111446139812218996951029 760448075607395530964159)
                    ·
                      rfl

theorem cell22_2221451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 5].length) (baseStart_2221451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221451 prefixEnd_2221451 := by exact prefixLift 2221451
  have htrace : WordTrace (prefixWord ++ tailWord_2221451) baseStart_2221451 baseEnd_2221451 := by
    simpa [prefixWord, tailWord_2221451, baseEnd_2221451] using wordTrace_append hprefix tailTrace_2221451
  have hstable : (prefixWord ++ tailWord_2221451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221451).length < 2 ^ (prefixWord ++ tailWord_2221451).sum := by decide
  have hdescent : baseEnd_2221451 < baseStart_2221451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221496 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 2, 7]
def baseStart_2221496 : Nat := 118140960795 + 2221496 * 2 ^ 59
def prefixEnd_2221496 : Nat := 4983230072969 + 3 ^ 40 * 2221496 * 2
def baseEnd_2221496 : Nat := 760463480027030413589021

theorem tailTrace_2221496 : CollatzResearch.WordTrace tailWord_2221496 prefixEnd_2221496 760463480027030413589021 := by
  unfold tailWord_2221496
  simp only [CollatzResearch.WordTrace]
  refine ⟨40512307779953434078114171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54016410373271245437485561 40512307779953434078114171)
  ·
    refine ⟨60768461669930151117171257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40512307779953434078114171 60768461669930151117171257)
    ·
      refine ⟨45576346252447613337878443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60768461669930151117171257 45576346252447613337878443)
      ·
        refine ⟨68364519378671420006817665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45576346252447613337878443 68364519378671420006817665)
        ·
          refine ⟨51273389534003565005113249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68364519378671420006817665 51273389534003565005113249)
          ·
            refine ⟨38455042150502673753834937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51273389534003565005113249 38455042150502673753834937)
            ·
              refine ⟨28841281612877005315376203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38455042150502673753834937 28841281612877005315376203)
              ·
                refine ⟨43261922419315507973064305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28841281612877005315376203 43261922419315507973064305)
                ·
                  refine ⟨32446441814486630979798229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43261922419315507973064305 32446441814486630979798229)
                  ·
                    refine ⟨760463480027030413589021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32446441814486630979798229 760463480027030413589021)
                    ·
                      rfl

theorem cell22_2221496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_2221496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221496 prefixEnd_2221496 := by exact prefixLift 2221496
  have htrace : WordTrace (prefixWord ++ tailWord_2221496) baseStart_2221496 baseEnd_2221496 := by
    simpa [prefixWord, tailWord_2221496, baseEnd_2221496] using wordTrace_append hprefix tailTrace_2221496
  have hstable : (prefixWord ++ tailWord_2221496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221496).length < 2 ^ (prefixWord ++ tailWord_2221496).sum := by decide
  have hdescent : baseEnd_2221496 < baseStart_2221496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221581 : List Nat := [1, 7, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_2221581 : Nat := 118140960795 + 2221581 * 2 ^ 59
def prefixEnd_2221581 : Nat := 4983230072969 + 3 ^ 40 * 2221581 * 2
def baseEnd_2221581 : Nat := 760492577264118525213761

theorem tailTrace_2221581 : CollatzResearch.WordTrace tailWord_2221581 prefixEnd_2221581 760492577264118525213761 := by
  unfold tailWord_2221581
  simp only [CollatzResearch.WordTrace]
  refine ⟨81027715764598927673072597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54018477176399285115381731 81027715764598927673072597)
  ·
    refine ⟨1899087088232787367337639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 81027715764598927673072597 1899087088232787367337639)
    ·
      refine ⟨2848630632349181051006459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1899087088232787367337639 2848630632349181051006459)
      ·
        refine ⟨4272945948523771576509689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2848630632349181051006459 4272945948523771576509689)
        ·
          refine ⟨3204709461392828682382267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4272945948523771576509689 3204709461392828682382267)
          ·
            refine ⟨4807064192089243023573401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3204709461392828682382267 4807064192089243023573401)
            ·
              refine ⟨3605298144066932267680051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4807064192089243023573401 3605298144066932267680051)
              ·
                refine ⟨5407947216100398401520077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3605298144066932267680051 5407947216100398401520077)
                ·
                  refine ⟨2027980206037649400570029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5407947216100398401520077 2027980206037649400570029)
                  ·
                    refine ⟨760492577264118525213761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2027980206037649400570029 760492577264118525213761)
                    ·
                      rfl

theorem cell22_2221581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_2221581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221581 prefixEnd_2221581 := by exact prefixLift 2221581
  have htrace : WordTrace (prefixWord ++ tailWord_2221581) baseStart_2221581 baseEnd_2221581 := by
    simpa [prefixWord, tailWord_2221581, baseEnd_2221581] using wordTrace_append hprefix tailTrace_2221581
  have hstable : (prefixWord ++ tailWord_2221581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221581).length < 2 ^ (prefixWord ++ tailWord_2221581).sum := by decide
  have hdescent : baseEnd_2221581 < baseStart_2221581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221639 : List Nat := [1, 1, 4, 1, 5, 1, 3, 2, 4]
def baseStart_2221639 : Nat := 118140960795 + 2221639 * 2 ^ 59
def prefixEnd_2221639 : Nat := 4983230072969 + 3 ^ 40 * 2221639 * 2
def baseEnd_2221639 : Nat := 253504143949808569087861

theorem tailTrace_2221639 : CollatzResearch.WordTrace tailWord_2221639 prefixEnd_2221639 253504143949808569087861 := by
  unfold tailWord_2221639
  simp only [CollatzResearch.WordTrace]
  refine ⟨81029831198388803578683971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54019887465592535719122647 81029831198388803578683971)
  ·
    refine ⟨121544746797583205368025957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81029831198388803578683971 121544746797583205368025957)
    ·
      refine ⟨22789640024546851006504867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121544746797583205368025957 22789640024546851006504867)
      ·
        refine ⟨34184460036820276509757301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22789640024546851006504867 34184460036820276509757301)
        ·
          refine ⟨3204793128451900922789747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34184460036820276509757301 3204793128451900922789747)
          ·
            refine ⟨4807189692677851384184621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3204793128451900922789747 4807189692677851384184621)
            ·
              refine ⟨1802696134754194269069233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4807189692677851384184621 1802696134754194269069233)
              ·
                refine ⟨1352022101065645701801925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1802696134754194269069233 1352022101065645701801925)
                ·
                  refine ⟨253504143949808569087861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1352022101065645701801925 253504143949808569087861)
                  ·
                    rfl

theorem cell22_2221639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 4].length) (baseStart_2221639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221639 prefixEnd_2221639 := by exact prefixLift 2221639
  have htrace : WordTrace (prefixWord ++ tailWord_2221639) baseStart_2221639 baseEnd_2221639 := by
    simpa [prefixWord, tailWord_2221639, baseEnd_2221639] using wordTrace_append hprefix tailTrace_2221639
  have hstable : (prefixWord ++ tailWord_2221639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221639).length < 2 ^ (prefixWord ++ tailWord_2221639).sum := by decide
  have hdescent : baseEnd_2221639 < baseStart_2221639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221650 : List Nat := [3, 2, 2, 1, 2, 3, 2, 7]
def baseStart_2221650 : Nat := 118140960795 + 2221650 * 2 ^ 59
def prefixEnd_2221650 : Nat := 4983230072969 + 3 ^ 40 * 2221650 * 2
def baseEnd_2221650 : Nat := 84501799708247260582061

theorem tailTrace_2221650 : CollatzResearch.WordTrace tailWord_2221650 prefixEnd_2221650 84501799708247260582061 := by
  unfold tailWord_2221650
  simp only [CollatzResearch.WordTrace]
  refine ⟨20257558100337238114333601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54020154934232634971556269 20257558100337238114333601)
  ·
    refine ⟨15193168575252928585750201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20257558100337238114333601 15193168575252928585750201)
    ·
      refine ⟨11394876431439696439312651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15193168575252928585750201 11394876431439696439312651)
      ·
        refine ⟨17092314647159544658968977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11394876431439696439312651 17092314647159544658968977)
        ·
          refine ⟨12819235985369658494226733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17092314647159544658968977 12819235985369658494226733)
          ·
            refine ⟨4807213494513621935335025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12819235985369658494226733 4807213494513621935335025)
            ·
              refine ⟨3605410120885216451501269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4807213494513621935335025 3605410120885216451501269)
              ·
                refine ⟨84501799708247260582061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3605410120885216451501269 84501799708247260582061)
                ·
                  rfl

theorem cell22_2221650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 7].length) (baseStart_2221650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221650 prefixEnd_2221650 := by exact prefixLift 2221650
  have htrace : WordTrace (prefixWord ++ tailWord_2221650) baseStart_2221650 baseEnd_2221650 := by
    simpa [prefixWord, tailWord_2221650, baseEnd_2221650] using wordTrace_append hprefix tailTrace_2221650
  have hstable : (prefixWord ++ tailWord_2221650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221650).length < 2 ^ (prefixWord ++ tailWord_2221650).sum := by decide
  have hdescent : baseEnd_2221650 < baseStart_2221650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221665 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 5, 3]
def baseStart_2221665 : Nat := 118140960795 + 2221665 * 2 ^ 59
def prefixEnd_2221665 : Nat := 4983230072969 + 3 ^ 40 * 2221665 * 2
def baseEnd_2221665 : Nat := 760521332180770306113503

theorem tailTrace_2221665 : CollatzResearch.WordTrace tailWord_2221665 prefixEnd_2221665 760521332180770306113503 := by
  unfold tailWord_2221665
  simp only [CollatzResearch.WordTrace]
  refine ⟨81030779496294610019130449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54020519664196406679420299 81030779496294610019130449)
  ·
    refine ⟨60773084622220957514347837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81030779496294610019130449 60773084622220957514347837)
    ·
      refine ⟨22789906733332859067880439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60773084622220957514347837 22789906733332859067880439)
      ·
        refine ⟨34184860099999288601820659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22789906733332859067880439 34184860099999288601820659)
        ·
          refine ⟨51277290149998932902730989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34184860099999288601820659 51277290149998932902730989)
          ·
            refine ⟨19228983806249599838524121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51277290149998932902730989 19228983806249599838524121)
            ·
              refine ⟨14421737854687199878893091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19228983806249599838524121 14421737854687199878893091)
              ·
                refine ⟨21632606782030799818339637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14421737854687199878893091 21632606782030799818339637)
                ·
                  refine ⟨2028056885815387482969341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21632606782030799818339637 2028056885815387482969341)
                  ·
                    refine ⟨760521332180770306113503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2028056885815387482969341 760521332180770306113503)
                    ·
                      rfl

theorem cell22_2221665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_2221665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221665 prefixEnd_2221665 := by exact prefixLift 2221665
  have htrace : WordTrace (prefixWord ++ tailWord_2221665) baseStart_2221665 baseEnd_2221665 := by
    simpa [prefixWord, tailWord_2221665, baseEnd_2221665] using wordTrace_append hprefix tailTrace_2221665
  have hstable : (prefixWord ++ tailWord_2221665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221665).length < 2 ^ (prefixWord ++ tailWord_2221665).sum := by decide
  have hdescent : baseEnd_2221665 < baseStart_2221665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221710 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 1, 7]
def baseStart_2221710 : Nat := 118140960795 + 2221710 * 2 ^ 59
def prefixEnd_2221710 : Nat := 4983230072969 + 3 ^ 40 * 2221710 * 2
def baseEnd_2221710 : Nat := 760536736600405188738365

theorem tailTrace_2221710 : CollatzResearch.WordTrace tailWord_2221710 prefixEnd_2221710 760536736600405188738365 := by
  unfold tailWord_2221710
  simp only [CollatzResearch.WordTrace]
  refine ⟨10129052597641447838064823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54021613854087721803012389 10129052597641447838064823)
  ·
    refine ⟨15193578896462171757097235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10129052597641447838064823 15193578896462171757097235)
    ·
      refine ⟨22790368344693257635645853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15193578896462171757097235 22790368344693257635645853)
      ·
        refine ⟨8546388129259971613367195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22790368344693257635645853 8546388129259971613367195)
        ·
          refine ⟨12819582193889957420050793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8546388129259971613367195 12819582193889957420050793)
          ·
            refine ⟨9614686645417468065038095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12819582193889957420050793 9614686645417468065038095)
            ·
              refine ⟨14422029968126202097557143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9614686645417468065038095 14422029968126202097557143)
              ·
                refine ⟨21633044952189303146335715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14422029968126202097557143 21633044952189303146335715)
                ·
                  refine ⟨32449567428283954719503573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21633044952189303146335715 32449567428283954719503573)
                  ·
                    refine ⟨760536736600405188738365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32449567428283954719503573 760536736600405188738365)
                    ·
                      rfl

theorem cell22_2221710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_2221710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221710 prefixEnd_2221710 := by exact prefixLift 2221710
  have htrace : WordTrace (prefixWord ++ tailWord_2221710) baseStart_2221710 baseEnd_2221710 := by
    simpa [prefixWord, tailWord_2221710, baseEnd_2221710] using wordTrace_append hprefix tailTrace_2221710
  have hstable : (prefixWord ++ tailWord_2221710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221710).length < 2 ^ (prefixWord ++ tailWord_2221710).sum := by decide
  have hdescent : baseEnd_2221710 < baseStart_2221710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221757 : List Nat := [1, 4, 1, 2, 1, 2, 1, 6, 4]
def baseStart_2221757 : Nat := 118140960795 + 2221757 * 2 ^ 59
def prefixEnd_2221757 : Nat := 4983230072969 + 3 ^ 40 * 2221757 * 2
def baseEnd_2221757 : Nat := 253517608553637577604407

theorem tailTrace_2221757 : CollatzResearch.WordTrace tailWord_2221757 prefixEnd_2221757 253517608553637577604407 := by
  unfold tailWord_2221757
  simp only [CollatzResearch.WordTrace]
  refine ⟨81034135011961309731479525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54022756674640873154319683 81034135011961309731479525)
  ·
    refine ⟨15193900314742745574652411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81034135011961309731479525 15193900314742745574652411)
    ·
      refine ⟨22790850472114118361978617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15193900314742745574652411 22790850472114118361978617)
      ·
        refine ⟨17093137854085588771483963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22790850472114118361978617 17093137854085588771483963)
        ·
          refine ⟨25639706781128383157225945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17093137854085588771483963 25639706781128383157225945)
          ·
            refine ⟨19229780085846287367919459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25639706781128383157225945 19229780085846287367919459)
            ·
              refine ⟨28844670128769431051879189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19229780085846287367919459 28844670128769431051879189)
              ·
                refine ⟨1352093912286067080556837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28844670128769431051879189 1352093912286067080556837)
                ·
                  refine ⟨253517608553637577604407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1352093912286067080556837 253517608553637577604407)
                  ·
                    rfl

theorem cell22_2221757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_2221757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221757 prefixEnd_2221757 := by exact prefixLift 2221757
  have htrace : WordTrace (prefixWord ++ tailWord_2221757) baseStart_2221757 baseEnd_2221757 := by
    simpa [prefixWord, tailWord_2221757, baseEnd_2221757] using wordTrace_append hprefix tailTrace_2221757
  have hstable : (prefixWord ++ tailWord_2221757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221757).length < 2 ^ (prefixWord ++ tailWord_2221757).sum := by decide
  have hdescent : baseEnd_2221757 < baseStart_2221757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221785 : List Nat := [1, 2, 1, 2, 3, 4, 1, 8]
def baseStart_2221785 : Nat := 118140960795 + 2221785 * 2 ^ 59
def prefixEnd_2221785 : Nat := 4983230072969 + 3 ^ 40 * 2221785 * 2
def baseEnd_2221785 : Nat := 84506934514792221457015

theorem tailTrace_2221785 : CollatzResearch.WordTrace tailWord_2221785 prefixEnd_2221785 84506934514792221457015 := by
  unfold tailWord_2221785
  simp only [CollatzResearch.WordTrace]
  refine ⟨81035156255859870513498809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54023437503906580342332539 81035156255859870513498809)
  ·
    refine ⟨60776367191894902885124107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81035156255859870513498809 60776367191894902885124107)
    ·
      refine ⟨91164550787842354327686161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60776367191894902885124107 91164550787842354327686161)
      ·
        refine ⟨68373413090881765745764621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91164550787842354327686161 68373413090881765745764621)
        ·
          refine ⟨25640029909080662154661733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68373413090881765745764621 25640029909080662154661733)
          ·
            refine ⟨4807505607952624153999075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25640029909080662154661733 4807505607952624153999075)
            ·
              refine ⟨7211258411928936230998613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4807505607952624153999075 7211258411928936230998613)
              ·
                refine ⟨84506934514792221457015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7211258411928936230998613 84506934514792221457015)
                ·
                  rfl

theorem cell22_2221785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 8].length) (baseStart_2221785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221785 prefixEnd_2221785 := by exact prefixLift 2221785
  have htrace : WordTrace (prefixWord ++ tailWord_2221785) baseStart_2221785 baseEnd_2221785 := by
    simpa [prefixWord, tailWord_2221785, baseEnd_2221785] using wordTrace_append hprefix tailTrace_2221785
  have hstable : (prefixWord ++ tailWord_2221785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221785).length < 2 ^ (prefixWord ++ tailWord_2221785).sum := by decide
  have hdescent : baseEnd_2221785 < baseStart_2221785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221864 : List Nat := [2, 1, 5, 1, 1, 3, 2, 2, 5]
def baseStart_2221864 : Nat := 118140960795 + 2221864 * 2 ^ 59
def prefixEnd_2221864 : Nat := 4983230072969 + 3 ^ 40 * 2221864 * 2
def baseEnd_2221864 : Nat := 253529817982533373462631

theorem tailTrace_2221864 : CollatzResearch.WordTrace tailWord_2221864 prefixEnd_2221864 253529817982533373462631 := by
  unfold tailWord_2221864
  simp only [CollatzResearch.WordTrace]
  refine ⟨40519018811286833502812323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54025358415049111337083097 40519018811286833502812323)
  ·
    refine ⟨60778528216930250254218485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40519018811286833502812323 60778528216930250254218485)
    ·
      refine ⟨5697987020337210961332983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60778528216930250254218485 5697987020337210961332983)
      ·
        refine ⟨8546980530505816441999475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5697987020337210961332983 8546980530505816441999475)
        ·
          refine ⟨12820470795758724662999213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8546980530505816441999475 12820470795758724662999213)
          ·
            refine ⟨4807676548409521748624705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12820470795758724662999213 4807676548409521748624705)
            ·
              refine ⟨3605757411307141311468529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4807676548409521748624705 3605757411307141311468529)
              ·
                refine ⟨2704318058480355983601397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3605757411307141311468529 2704318058480355983601397)
                ·
                  refine ⟨253529817982533373462631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2704318058480355983601397 253529817982533373462631)
                  ·
                    rfl

theorem cell22_2221864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 5].length) (baseStart_2221864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221864 prefixEnd_2221864 := by exact prefixLift 2221864
  have htrace : WordTrace (prefixWord ++ tailWord_2221864) baseStart_2221864 baseEnd_2221864 := by
    simpa [prefixWord, tailWord_2221864, baseEnd_2221864] using wordTrace_append hprefix tailTrace_2221864
  have hstable : (prefixWord ++ tailWord_2221864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221864).length < 2 ^ (prefixWord ++ tailWord_2221864).sum := by decide
  have hdescent : baseEnd_2221864 < baseStart_2221864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221868 : List Nat := [2, 2, 1, 1, 1, 7, 2, 2, 1, 3]
def baseStart_2221868 : Nat := 118140960795 + 2221868 * 2 ^ 59
def prefixEnd_2221868 : Nat := 4983230072969 + 3 ^ 40 * 2221868 * 2
def baseEnd_2221868 : Nat := 760590823229345443287881

theorem tailTrace_2221868 : CollatzResearch.WordTrace tailWord_2221868 prefixEnd_2221868 760590823229345443287881 := by
  unfold tailWord_2221868
  simp only [CollatzResearch.WordTrace]
  refine ⟨40519091757279587844385129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54025455676372783792513505 40519091757279587844385129)
  ·
    refine ⟨30389318817959690883288847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40519091757279587844385129 30389318817959690883288847)
    ·
      refine ⟨45583978226939536324933271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30389318817959690883288847 45583978226939536324933271)
      ·
        refine ⟨68375967340409304487399907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45583978226939536324933271 68375967340409304487399907)
        ·
          refine ⟨102563951010613956731099861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68375967340409304487399907 102563951010613956731099861)
          ·
            refine ⟨2403842601811264610885153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 102563951010613956731099861 2403842601811264610885153)
            ·
              refine ⟨1802881951358448458163865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2403842601811264610885153 1802881951358448458163865)
              ·
                refine ⟨1352161463518836343622899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1802881951358448458163865 1352161463518836343622899)
                ·
                  refine ⟨2028242195278254515434349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1352161463518836343622899 2028242195278254515434349)
                  ·
                    refine ⟨760590823229345443287881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2028242195278254515434349 760590823229345443287881)
                    ·
                      rfl

theorem cell22_2221868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 1, 3].length) (baseStart_2221868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221868 prefixEnd_2221868 := by exact prefixLift 2221868
  have htrace : WordTrace (prefixWord ++ tailWord_2221868) baseStart_2221868 baseEnd_2221868 := by
    simpa [prefixWord, tailWord_2221868, baseEnd_2221868] using wordTrace_append hprefix tailTrace_2221868
  have hstable : (prefixWord ++ tailWord_2221868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221868).length < 2 ^ (prefixWord ++ tailWord_2221868).sum := by decide
  have hdescent : baseEnd_2221868 < baseStart_2221868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221909 : List Nat := [1, 3, 2, 2, 2, 2, 1, 5, 4]
def baseStart_2221909 : Nat := 118140960795 + 2221909 * 2 ^ 59
def prefixEnd_2221909 : Nat := 4983230072969 + 3 ^ 40 * 2221909 * 2
def baseEnd_2221909 : Nat := 253534952789078334337585

theorem tailTrace_2221909 : CollatzResearch.WordTrace tailWord_2221909 prefixEnd_2221909 253534952789078334337585 := by
  unfold tailWord_2221909
  simp only [CollatzResearch.WordTrace]
  refine ⟨81039678907410639691012781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54026452604940426460675187 81039678907410639691012781)
  ·
    refine ⟨30389879590278989884129793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81039678907410639691012781 30389879590278989884129793)
    ·
      refine ⟨22792409692709242413097345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30389879590278989884129793 22792409692709242413097345)
      ·
        refine ⟨17094307269531931809823009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22792409692709242413097345 17094307269531931809823009)
        ·
          refine ⟨12820730452148948857367257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17094307269531931809823009 12820730452148948857367257)
          ·
            refine ⟨9615547839111711643025443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12820730452148948857367257 9615547839111711643025443)
            ·
              refine ⟨14423321758667567464538165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9615547839111711643025443 14423321758667567464538165)
              ·
                refine ⟨1352186414875084449800453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14423321758667567464538165 1352186414875084449800453)
                ·
                  refine ⟨253534952789078334337585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1352186414875084449800453 253534952789078334337585)
                  ·
                    rfl

theorem cell22_2221909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 4].length) (baseStart_2221909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221909 prefixEnd_2221909 := by exact prefixLift 2221909
  have htrace : WordTrace (prefixWord ++ tailWord_2221909) baseStart_2221909 baseEnd_2221909 := by
    simpa [prefixWord, tailWord_2221909, baseEnd_2221909] using wordTrace_append hprefix tailTrace_2221909
  have hstable : (prefixWord ++ tailWord_2221909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221909).length < 2 ^ (prefixWord ++ tailWord_2221909).sum := by decide
  have hdescent : baseEnd_2221909 < baseStart_2221909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221992 : List Nat := [2, 1, 6, 2, 1, 2, 2, 1, 2, 3]
def baseStart_2221992 : Nat := 118140960795 + 2221992 * 2 ^ 59
def prefixEnd_2221992 : Nat := 4983230072969 + 3 ^ 40 * 2221992 * 2
def baseEnd_2221992 : Nat := 760633270963450453187501

theorem tailTrace_2221992 : CollatzResearch.WordTrace tailWord_2221992 prefixEnd_2221992 760633270963450453187501 := by
  unfold tailWord_2221992
  simp only [CollatzResearch.WordTrace]
  refine ⟨40521353083054972433142115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54028470777406629910856153 40521353083054972433142115)
  ·
    refine ⟨60782029624582458649713173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40521353083054972433142115 60782029624582458649713173)
    ·
      refine ⟨2849157638652302749205305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60782029624582458649713173 2849157638652302749205305)
      ·
        refine ⟨2136868228989227061903979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2849157638652302749205305 2136868228989227061903979)
        ·
          refine ⟨3205302343483840592855969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2136868228989227061903979 3205302343483840592855969)
          ·
            refine ⟨2403976757612880444641977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3205302343483840592855969 2403976757612880444641977)
            ·
              refine ⟨1802982568209660333481483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2403976757612880444641977 1802982568209660333481483)
              ·
                refine ⟨2704473852314490500222225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1802982568209660333481483 2704473852314490500222225)
                ·
                  refine ⟨2028355389235867875166669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2704473852314490500222225 2028355389235867875166669)
                  ·
                    refine ⟨760633270963450453187501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2028355389235867875166669 760633270963450453187501)
                    ·
                      rfl

theorem cell22_2221992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_2221992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2221992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2221992 prefixEnd_2221992 := by exact prefixLift 2221992
  have htrace : WordTrace (prefixWord ++ tailWord_2221992) baseStart_2221992 baseEnd_2221992 := by
    simpa [prefixWord, tailWord_2221992, baseEnd_2221992] using wordTrace_append hprefix tailTrace_2221992
  have hstable : (prefixWord ++ tailWord_2221992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221992).length < 2 ^ (prefixWord ++ tailWord_2221992).sum := by decide
  have hdescent : baseEnd_2221992 < baseStart_2221992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222072 : List Nat := [2, 1, 2, 1, 1, 3, 2, 10]
def baseStart_2222072 : Nat := 118140960795 + 2222072 * 2 ^ 59
def prefixEnd_2222072 : Nat := 4983230072969 + 3 ^ 40 * 2222072 * 2
def baseEnd_2222072 : Nat := 84517850733150767909695

theorem tailTrace_2222072 : CollatzResearch.WordTrace tailWord_2222072 prefixEnd_2222072 84517850733150767909695 := by
  unfold tailWord_2222072
  simp only [CollatzResearch.WordTrace]
  refine ⟨40522812002910059264598235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54030416003880079019464313 40522812002910059264598235)
  ·
    refine ⟨60784218004365088896897353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40522812002910059264598235 60784218004365088896897353)
    ·
      refine ⟨45588163503273816672673015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60784218004365088896897353 45588163503273816672673015)
      ·
        refine ⟨68382245254910725009009523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45588163503273816672673015 68382245254910725009009523)
        ·
          refine ⟨102573367882366087513514285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68382245254910725009009523 102573367882366087513514285)
          ·
            refine ⟨38465012955887282817567857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102573367882366087513514285 38465012955887282817567857)
            ·
              refine ⟨28848759716915462113175893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38465012955887282817567857 28848759716915462113175893)
              ·
                refine ⟨84517850733150767909695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28848759716915462113175893 84517850733150767909695)
                ·
                  rfl

theorem cell22_2222072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 10].length) (baseStart_2222072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222072 prefixEnd_2222072 := by exact prefixLift 2222072
  have htrace : WordTrace (prefixWord ++ tailWord_2222072) baseStart_2222072 baseEnd_2222072 := by
    simpa [prefixWord, tailWord_2222072, baseEnd_2222072] using wordTrace_append hprefix tailTrace_2222072
  have hstable : (prefixWord ++ tailWord_2222072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222072).length < 2 ^ (prefixWord ++ tailWord_2222072).sum := by decide
  have hdescent : baseEnd_2222072 < baseStart_2222072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222078 : List Nat := [4, 2, 2, 2, 1, 1, 1, 5, 4]
def baseStart_2222078 : Nat := 118140960795 + 2222078 * 2 ^ 59
def prefixEnd_2222078 : Nat := 4983230072969 + 3 ^ 40 * 2222078 * 2
def baseEnd_2222078 : Nat := 253554236840324965179079

theorem tailTrace_2222078 : CollatzResearch.WordTrace tailWord_2222078 prefixEnd_2222078 253554236840324965179079 := by
  unfold tailWord_2222078
  simp only [CollatzResearch.WordTrace]
  refine ⟨10130730355474797694239361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54030561895865587702609925 10130730355474797694239361)
  ·
    refine ⟨7598047766606098270679521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10130730355474797694239361 7598047766606098270679521)
    ·
      refine ⟨5698535824954573703009641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7598047766606098270679521 5698535824954573703009641)
      ·
        refine ⟨4273901868715930277257231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5698535824954573703009641 4273901868715930277257231)
        ·
          refine ⟨6410852803073895415885847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4273901868715930277257231 6410852803073895415885847)
          ·
            refine ⟨9616279204610843123828771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6410852803073895415885847 9616279204610843123828771)
            ·
              refine ⟨14424418806916264685743157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9616279204610843123828771 14424418806916264685743157)
              ·
                refine ⟨1352289263148399814288421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14424418806916264685743157 1352289263148399814288421)
                ·
                  refine ⟨253554236840324965179079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1352289263148399814288421 253554236840324965179079)
                  ·
                    rfl

theorem cell22_2222078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_2222078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222078 prefixEnd_2222078 := by exact prefixLift 2222078
  have htrace : WordTrace (prefixWord ++ tailWord_2222078) baseStart_2222078 baseEnd_2222078 := by
    simpa [prefixWord, tailWord_2222078, baseEnd_2222078] using wordTrace_append hprefix tailTrace_2222078
  have hstable : (prefixWord ++ tailWord_2222078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222078).length < 2 ^ (prefixWord ++ tailWord_2222078).sum := by decide
  have hdescent : baseEnd_2222078 < baseStart_2222078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222164 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_2222164 : Nat := 118140960795 + 2222164 * 2 ^ 59
def prefixEnd_2222164 : Nat := 4983230072969 + 3 ^ 40 * 2222164 * 2
def baseEnd_2222164 : Nat := 760692150078499337886973

theorem tailTrace_2222164 : CollatzResearch.WordTrace tailWord_2222164 prefixEnd_2222164 760692150078499337886973 := by
  unfold tailWord_2222164
  simp only [CollatzResearch.WordTrace]
  refine ⟨40524489760743409120772773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54032653014324545494363697 40524489760743409120772773)
  ·
    refine ⟨7598341830139389210144895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40524489760743409120772773 7598341830139389210144895)
    ·
      refine ⟨11397512745209083815217343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7598341830139389210144895 11397512745209083815217343)
      ·
        refine ⟨17096269117813625722826015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11397512745209083815217343 17096269117813625722826015)
        ·
          refine ⟨25644403676720438584239023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17096269117813625722826015 25644403676720438584239023)
          ·
            refine ⟨38466605515080657876358535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25644403676720438584239023 38466605515080657876358535)
            ·
              refine ⟨57699908272620986814537803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38466605515080657876358535 57699908272620986814537803)
              ·
                refine ⟨86549862408931480221806705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57699908272620986814537803 86549862408931480221806705)
                ·
                  refine ⟨64912396806698610166355029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86549862408931480221806705 64912396806698610166355029)
                  ·
                    refine ⟨760692150078499337886973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64912396806698610166355029 760692150078499337886973)
                    ·
                      rfl

theorem cell22_2222164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_2222164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222164 prefixEnd_2222164 := by exact prefixLift 2222164
  have htrace : WordTrace (prefixWord ++ tailWord_2222164) baseStart_2222164 baseEnd_2222164 := by
    simpa [prefixWord, tailWord_2222164, baseEnd_2222164] using wordTrace_append hprefix tailTrace_2222164
  have hstable : (prefixWord ++ tailWord_2222164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222164).length < 2 ^ (prefixWord ++ tailWord_2222164).sum := by decide
  have hdescent : baseEnd_2222164 < baseStart_2222164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
