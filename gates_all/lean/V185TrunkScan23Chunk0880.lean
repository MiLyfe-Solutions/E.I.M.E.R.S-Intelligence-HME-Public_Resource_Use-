import V185TrunkScan23Chunk0879

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5207354 : List Nat := [3, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3]
def baseStart_5207354 : Nat := 118140960795 + 5207354 * 2 ^ 59
def prefixEnd_5207354 : Nat := 4983230072969 + 3 ^ 40 * 5207354 * 2
def baseEnd_5207354 : Nat := 2673875540112924437226821

theorem tailTrace_5207354 : CollatzResearch.WordTrace tailWord_5207354 prefixEnd_5207354 2673875540112924437226821 := by
  unfold tailWord_5207354
  simp only [CollatzResearch.WordTrace]
  refine ⟨47481950894163319525979279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126618535717768852069278077 47481950894163319525979279)
  ·
    refine ⟨71222926341244979288968919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47481950894163319525979279 71222926341244979288968919)
    ·
      refine ⟨106834389511867468933453379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71222926341244979288968919 106834389511867468933453379)
      ·
        refine ⟨160251584267801203400180069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106834389511867468933453379 160251584267801203400180069)
        ·
          refine ⟨30047172050212725637533763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160251584267801203400180069 30047172050212725637533763)
          ·
            refine ⟨45070758075319088456300645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30047172050212725637533763 45070758075319088456300645)
            ·
              refine ⟨8450767139122329085556371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45070758075319088456300645 8450767139122329085556371)
              ·
                refine ⟨12676150708683493628334557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8450767139122329085556371 12676150708683493628334557)
                ·
                  refine ⟨4753556515756310110625459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12676150708683493628334557 4753556515756310110625459)
                  ·
                    refine ⟨7130334773634465165938189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4753556515756310110625459 7130334773634465165938189)
                    ·
                      refine ⟨2673875540112924437226821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7130334773634465165938189 2673875540112924437226821)
                      ·
                        rfl

theorem cell23_5207354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3].length) (baseStart_5207354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207354 prefixEnd_5207354 := by exact prefixLift 5207354
  have htrace : WordTrace (prefixWord ++ tailWord_5207354) baseStart_5207354 baseEnd_5207354 := by
    simpa [prefixWord, tailWord_5207354, baseEnd_5207354] using wordTrace_append hprefix tailTrace_5207354
  have hstable : (prefixWord ++ tailWord_5207354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207354).length < 2 ^ (prefixWord ++ tailWord_5207354).sum := by decide
  have hdescent : baseEnd_5207354 < baseStart_5207354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207377 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 2, 6, 2]
def baseStart_5207377 : Nat := 118140960795 + 5207377 * 2 ^ 59
def prefixEnd_5207377 : Nat := 4983230072969 + 3 ^ 40 * 5207377 * 2
def baseEnd_5207377 : Nat := 2673887350167977847239215

theorem tailTrace_5207377 : CollatzResearch.WordTrace tailWord_5207377 prefixEnd_5207377 2673887350167977847239215 := by
  unfold tailWord_5207377
  simp only [CollatzResearch.WordTrace]
  refine ⟨189928642455569953032004385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126619094970379968688002923 189928642455569953032004385)
  ·
    refine ⟨142446481841677464774003289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189928642455569953032004385 142446481841677464774003289)
    ·
      refine ⟨106834861381258098580502467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142446481841677464774003289 106834861381258098580502467)
      ·
        refine ⟨160252292071887147870753701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106834861381258098580502467 160252292071887147870753701)
        ·
          refine ⟨30047304763478840225766319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160252292071887147870753701 30047304763478840225766319)
          ·
            refine ⟨45070957145218260338649479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30047304763478840225766319 45070957145218260338649479)
            ·
              refine ⟨67606435717827390507974219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45070957145218260338649479 67606435717827390507974219)
              ·
                refine ⟨101409653576741085761961329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67606435717827390507974219 101409653576741085761961329)
                ·
                  refine ⟨76057240182555814321470997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101409653576741085761961329 76057240182555814321470997)
                  ·
                    refine ⟨3565183133557303796318953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76057240182555814321470997 3565183133557303796318953)
                    ·
                      refine ⟨2673887350167977847239215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3565183133557303796318953 2673887350167977847239215)
                      ·
                        rfl

theorem cell23_5207377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 6, 2].length) (baseStart_5207377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207377 prefixEnd_5207377 := by exact prefixLift 5207377
  have htrace : WordTrace (prefixWord ++ tailWord_5207377) baseStart_5207377 baseEnd_5207377 := by
    simpa [prefixWord, tailWord_5207377, baseEnd_5207377] using wordTrace_append hprefix tailTrace_5207377
  have hstable : (prefixWord ++ tailWord_5207377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207377).length < 2 ^ (prefixWord ++ tailWord_5207377).sum := by decide
  have hdescent : baseEnd_5207377 < baseStart_5207377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207394 : List Nat := [3, 3, 2, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_5207394 : Nat := 118140960795 + 5207394 * 2 ^ 59
def prefixEnd_5207394 : Nat := 4983230072969 + 3 ^ 40 * 5207394 * 2
def baseEnd_5207394 : Nat := 2673896079339104280726637

theorem tailTrace_5207394 : CollatzResearch.WordTrace tailWord_5207394 prefixEnd_5207394 2673896079339104280726637 := by
  unfold tailWord_5207394
  simp only [CollatzResearch.WordTrace]
  refine ⟨47482315624127091233843309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126619508331005576623582157 47482315624127091233843309)
  ·
    refine ⟨17805868359047659212691241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47482315624127091233843309 17805868359047659212691241)
    ·
      refine ⟨13354401269285744409518431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17805868359047659212691241 13354401269285744409518431)
      ·
        refine ⟨20031601903928616614277647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13354401269285744409518431 20031601903928616614277647)
        ·
          refine ⟨30047402855892924921416471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20031601903928616614277647 30047402855892924921416471)
          ·
            refine ⟨45071104283839387382124707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30047402855892924921416471 45071104283839387382124707)
            ·
              refine ⟨67606656425759081073187061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45071104283839387382124707 67606656425759081073187061)
              ·
                refine ⟨6338124039914913850611287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67606656425759081073187061 6338124039914913850611287)
                ·
                  refine ⟨9507186059872370775916931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6338124039914913850611287 9507186059872370775916931)
                  ·
                    refine ⟨14260779089808556163875397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9507186059872370775916931 14260779089808556163875397)
                    ·
                      refine ⟨2673896079339104280726637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14260779089808556163875397 2673896079339104280726637)
                      ·
                        rfl

theorem cell23_5207394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_5207394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207394 prefixEnd_5207394 := by exact prefixLift 5207394
  have htrace : WordTrace (prefixWord ++ tailWord_5207394) baseStart_5207394 baseEnd_5207394 := by
    simpa [prefixWord, tailWord_5207394, baseEnd_5207394] using wordTrace_append hprefix tailTrace_5207394
  have hstable : (prefixWord ++ tailWord_5207394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207394).length < 2 ^ (prefixWord ++ tailWord_5207394).sum := by decide
  have hdescent : baseEnd_5207394 < baseStart_5207394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207397 : List Nat := [1, 3, 1, 3, 1, 2, 4, 1, 1, 1, 5]
def baseStart_5207397 : Nat := 118140960795 + 5207397 * 2 ^ 59
def prefixEnd_5207397 : Nat := 4983230072969 + 3 ^ 40 * 5207397 * 2
def baseEnd_5207397 : Nat := 2673897619781067768989123

theorem tailTrace_5207397 : CollatzResearch.WordTrace tailWord_5207397 prefixEnd_5207397 2673897619781067768989123 := by
  unfold tailWord_5207397
  simp only [CollatzResearch.WordTrace]
  refine ⟨189929371915497496447732445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126619581276998330965154963 189929371915497496447732445)
  ·
    refine ⟨71223514468311561167899667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189929371915497496447732445 71223514468311561167899667)
    ·
      refine ⟨106835271702467341751849501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71223514468311561167899667 106835271702467341751849501)
      ·
        refine ⟨40063226888425253156943563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106835271702467341751849501 40063226888425253156943563)
        ·
          refine ⟨60094840332637879735415345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40063226888425253156943563 60094840332637879735415345)
          ·
            refine ⟨45071130249478409801561509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60094840332637879735415345 45071130249478409801561509)
            ·
              refine ⟨8450836921777201837792783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45071130249478409801561509 8450836921777201837792783)
              ·
                refine ⟨12676255382665802756689175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8450836921777201837792783 12676255382665802756689175)
                ·
                  refine ⟨19014383073998704135033763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12676255382665802756689175 19014383073998704135033763)
                  ·
                    refine ⟨28521574610998056202550645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19014383073998704135033763 28521574610998056202550645)
                    ·
                      refine ⟨2673897619781067768989123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28521574610998056202550645 2673897619781067768989123)
                      ·
                        rfl

theorem cell23_5207397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_5207397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207397 prefixEnd_5207397 := by exact prefixLift 5207397
  have htrace : WordTrace (prefixWord ++ tailWord_5207397) baseStart_5207397 baseEnd_5207397 := by
    simpa [prefixWord, tailWord_5207397, baseEnd_5207397] using wordTrace_append hprefix tailTrace_5207397
  have hstable : (prefixWord ++ tailWord_5207397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207397).length < 2 ^ (prefixWord ++ tailWord_5207397).sum := by decide
  have hdescent : baseEnd_5207397 < baseStart_5207397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207420 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 2, 2, 6]
def baseStart_5207420 : Nat := 118140960795 + 5207420 * 2 ^ 59
def prefixEnd_5207420 : Nat := 4983230072969 + 3 ^ 40 * 5207420 * 2
def baseEnd_5207420 : Nat := 2673909429836121179001517

theorem tailTrace_5207420 : CollatzResearch.WordTrace tailWord_5207420 prefixEnd_5207420 2673909429836121179001517 := by
  unfold tailWord_5207420
  simp only [CollatzResearch.WordTrace]
  refine ⟨94965105397207085687909857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126620140529609447583879809 94965105397207085687909857)
  ·
    refine ⟨71223829047905314265932393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94965105397207085687909857 71223829047905314265932393)
    ·
      refine ⟨53417871785928985699449295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71223829047905314265932393 53417871785928985699449295)
      ·
        refine ⟨80126807678893478549173943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53417871785928985699449295 80126807678893478549173943)
        ·
          refine ⟨120190211518340217823760915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80126807678893478549173943 120190211518340217823760915)
          ·
            refine ⟨180285317277510326735641373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120190211518340217823760915 180285317277510326735641373)
            ·
              refine ⟨67606993979066372525865515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180285317277510326735641373 67606993979066372525865515)
              ·
                refine ⟨101410490968599558788798273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67606993979066372525865515 101410490968599558788798273)
                ·
                  refine ⟨76057868226449669091598705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101410490968599558788798273 76057868226449669091598705)
                  ·
                    refine ⟨57043401169837251818699029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76057868226449669091598705 57043401169837251818699029)
                    ·
                      refine ⟨2673909429836121179001517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57043401169837251818699029 2673909429836121179001517)
                      ·
                        rfl

theorem cell23_5207420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_5207420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207420 prefixEnd_5207420 := by exact prefixLift 5207420
  have htrace : WordTrace (prefixWord ++ tailWord_5207420) baseStart_5207420 baseEnd_5207420 := by
    simpa [prefixWord, tailWord_5207420, baseEnd_5207420] using wordTrace_append hprefix tailTrace_5207420
  have hstable : (prefixWord ++ tailWord_5207420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207420).length < 2 ^ (prefixWord ++ tailWord_5207420).sum := by decide
  have hdescent : baseEnd_5207420 < baseStart_5207420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207431 : List Nat := [1, 1, 4, 2, 2, 4, 1, 2, 1, 2, 3]
def baseStart_5207431 : Nat := 118140960795 + 5207431 * 2 ^ 59
def prefixEnd_5207431 : Nat := 4983230072969 + 3 ^ 40 * 5207431 * 2
def baseEnd_5207431 : Nat := 2673915078123320635963967

theorem tailTrace_5207431 : CollatzResearch.WordTrace tailWord_5207431 prefixEnd_5207431 2673915078123320635963967 := by
  unfold tailWord_5207431
  simp only [CollatzResearch.WordTrace]
  refine ⟨189930611997374320254470147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126620407998249546836313431 189930611997374320254470147)
  ·
    refine ⟨284895917996061480381705221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189930611997374320254470147 284895917996061480381705221)
    ·
      refine ⟨53417984624261527571569729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 284895917996061480381705221 53417984624261527571569729)
      ·
        refine ⟨40063488468196145678677297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53417984624261527571569729 40063488468196145678677297)
        ·
          refine ⟨30047616351147109259007973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40063488468196145678677297 30047616351147109259007973)
          ·
            refine ⟨5633928065840082986063995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30047616351147109259007973 5633928065840082986063995)
            ·
              refine ⟨8450892098760124479095993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5633928065840082986063995 8450892098760124479095993)
              ·
                refine ⟨6338169074070093359321995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8450892098760124479095993 6338169074070093359321995)
                ·
                  refine ⟨9507253611105140038982993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6338169074070093359321995 9507253611105140038982993)
                  ·
                    refine ⟨7130440208328855029237245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9507253611105140038982993 7130440208328855029237245)
                    ·
                      refine ⟨2673915078123320635963967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7130440208328855029237245 2673915078123320635963967)
                      ·
                        rfl

theorem cell23_5207431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_5207431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207431 prefixEnd_5207431 := by exact prefixLift 5207431
  have htrace : WordTrace (prefixWord ++ tailWord_5207431) baseStart_5207431 baseEnd_5207431 := by
    simpa [prefixWord, tailWord_5207431, baseEnd_5207431] using wordTrace_append hprefix tailTrace_5207431
  have hstable : (prefixWord ++ tailWord_5207431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207431).length < 2 ^ (prefixWord ++ tailWord_5207431).sum := by decide
  have hdescent : baseEnd_5207431 < baseStart_5207431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207444 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_5207444 : Nat := 118140960795 + 5207444 * 2 ^ 59
def prefixEnd_5207444 : Nat := 4983230072969 + 3 ^ 40 * 5207444 * 2
def baseEnd_5207444 : Nat := 2673921753371829085101407

theorem tailTrace_5207444 : CollatzResearch.WordTrace tailWord_5207444 prefixEnd_5207444 2673921753371829085101407 := by
  unfold tailWord_5207444
  simp only [CollatzResearch.WordTrace]
  refine ⟨94965543073163611737346693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126620724097551482316462257 94965543073163611737346693)
  ·
    refine ⟨17806039326218177200752505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94965543073163611737346693 17806039326218177200752505)
    ·
      refine ⟨13354529494663632900564379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17806039326218177200752505 13354529494663632900564379)
      ·
        refine ⟨20031794241995449350846569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13354529494663632900564379 20031794241995449350846569)
        ·
          refine ⟨15023845681496587013134927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20031794241995449350846569 15023845681496587013134927)
          ·
            refine ⟨22535768522244880519702391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15023845681496587013134927 22535768522244880519702391)
            ·
              refine ⟨33803652783367320779553587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22535768522244880519702391 33803652783367320779553587)
              ·
                refine ⟨50705479175050981169330381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33803652783367320779553587 50705479175050981169330381)
                ·
                  refine ⟨19014554690644117938498893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50705479175050981169330381 19014554690644117938498893)
                  ·
                    refine ⟨7130458008991544226937085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19014554690644117938498893 7130458008991544226937085)
                    ·
                      refine ⟨2673921753371829085101407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7130458008991544226937085 2673921753371829085101407)
                      ·
                        rfl

theorem cell23_5207444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_5207444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207444 prefixEnd_5207444 := by exact prefixLift 5207444
  have htrace : WordTrace (prefixWord ++ tailWord_5207444) baseStart_5207444 baseEnd_5207444 := by
    simpa [prefixWord, tailWord_5207444, baseEnd_5207444] using wordTrace_append hprefix tailTrace_5207444
  have hstable : (prefixWord ++ tailWord_5207444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207444).length < 2 ^ (prefixWord ++ tailWord_5207444).sum := by decide
  have hdescent : baseEnd_5207444 < baseStart_5207444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207448 : List Nat := [2, 1, 2, 5, 2, 1, 3, 1, 1, 2, 3]
def baseStart_5207448 : Nat := 118140960795 + 5207448 * 2 ^ 59
def prefixEnd_5207448 : Nat := 4983230072969 + 3 ^ 40 * 5207448 * 2
def baseEnd_5207448 : Nat := 2673923807294447069451389

theorem tailTrace_5207448 : CollatzResearch.WordTrace tailWord_5207448 prefixEnd_5207448 2673923807294447069451389 := by
  unfold tailWord_5207448
  simp only [CollatzResearch.WordTrace]
  refine ⟨94965616019156366078919499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126620821358875154771892665 94965616019156366078919499)
  ·
    refine ⟨142448424028734549118379249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94965616019156366078919499 142448424028734549118379249)
    ·
      refine ⟨106836318021550911838784437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142448424028734549118379249 106836318021550911838784437)
      ·
        refine ⟨10015904814520397984886041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106836318021550911838784437 10015904814520397984886041)
        ·
          refine ⟨7511928610890298488664531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10015904814520397984886041 7511928610890298488664531)
          ·
            refine ⟨11267892916335447732996797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7511928610890298488664531 11267892916335447732996797)
            ·
              refine ⟨4225459843625792899873799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11267892916335447732996797 4225459843625792899873799)
              ·
                refine ⟨6338189765438689349810699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4225459843625792899873799 6338189765438689349810699)
                ·
                  refine ⟨9507284648158034024716049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6338189765438689349810699 9507284648158034024716049)
                  ·
                    refine ⟨7130463486118525518537037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9507284648158034024716049 7130463486118525518537037)
                    ·
                      refine ⟨2673923807294447069451389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7130463486118525518537037 2673923807294447069451389)
                      ·
                        rfl

theorem cell23_5207448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_5207448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207448 prefixEnd_5207448 := by exact prefixLift 5207448
  have htrace : WordTrace (prefixWord ++ tailWord_5207448) baseStart_5207448 baseEnd_5207448 := by
    simpa [prefixWord, tailWord_5207448, baseEnd_5207448] using wordTrace_append hprefix tailTrace_5207448
  have hstable : (prefixWord ++ tailWord_5207448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207448).length < 2 ^ (prefixWord ++ tailWord_5207448).sum := by decide
  have hdescent : baseEnd_5207448 < baseStart_5207448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207477 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 1, 8]
def baseStart_5207477 : Nat := 118140960795 + 5207477 * 2 ^ 59
def prefixEnd_5207477 : Nat := 4983230072969 + 3 ^ 40 * 5207477 * 2
def baseEnd_5207477 : Nat := 891312899411142485329585

theorem tailTrace_5207477 : CollatzResearch.WordTrace tailWord_5207477 prefixEnd_5207477 891312899411142485329585 := by
  unfold tailWord_5207477
  simp only [CollatzResearch.WordTrace]
  refine ⟨189932289755207670110644685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126621526503471780073763123 189932289755207670110644685)
  ·
    refine ⟨71224608658202876291491757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189932289755207670110644685 71224608658202876291491757)
    ·
      refine ⟨26709228246826078609309409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71224608658202876291491757 26709228246826078609309409)
      ·
        refine ⟨20031921185119558956982057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26709228246826078609309409 20031921185119558956982057)
        ·
          refine ⟨15023940888839669217736543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20031921185119558956982057 15023940888839669217736543)
          ·
            refine ⟨22535911333259503826604815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15023940888839669217736543 22535911333259503826604815)
            ·
              refine ⟨33803866999889255739907223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22535911333259503826604815 33803866999889255739907223)
              ·
                refine ⟨50705800499833883609860835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33803866999889255739907223 50705800499833883609860835)
                ·
                  refine ⟨76058700749750825414791253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50705800499833883609860835 76058700749750825414791253)
                  ·
                    refine ⟨891312899411142485329585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76058700749750825414791253 891312899411142485329585)
                    ·
                      rfl

theorem cell23_5207477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_5207477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207477 prefixEnd_5207477 := by exact prefixLift 5207477
  have htrace : WordTrace (prefixWord ++ tailWord_5207477) baseStart_5207477 baseEnd_5207477 := by
    simpa [prefixWord, tailWord_5207477, baseEnd_5207477] using wordTrace_append hprefix tailTrace_5207477
  have hstable : (prefixWord ++ tailWord_5207477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207477).length < 2 ^ (prefixWord ++ tailWord_5207477).sum := by decide
  have hdescent : baseEnd_5207477 < baseStart_5207477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207534 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 2, 3, 3]
def baseStart_5207534 : Nat := 118140960795 + 5207534 * 2 ^ 59
def prefixEnd_5207534 : Nat := 4983230072969 + 3 ^ 40 * 5207534 * 2
def baseEnd_5207534 : Nat := 2673967966630733732975993

theorem tailTrace_5207534 : CollatzResearch.WordTrace tailWord_5207534 prefixEnd_5207534 2673967966630733732975993 := by
  unfold tailWord_5207534
  simp only [CollatzResearch.WordTrace]
  refine ⟨23741796089500146105683707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126622912477334112563646437 23741796089500146105683707)
  ·
    refine ⟨35612694134250219158525561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23741796089500146105683707 35612694134250219158525561)
    ·
      refine ⟨26709520600687664368894171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35612694134250219158525561 26709520600687664368894171)
      ·
        refine ⟨40064280901031496553341257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26709520600687664368894171 40064280901031496553341257)
        ·
          refine ⟨30048210675773622415005943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40064280901031496553341257 30048210675773622415005943)
          ·
            refine ⟨45072316013660433622508915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30048210675773622415005943 45072316013660433622508915)
            ·
              refine ⟨67608474020490650433763373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45072316013660433622508915 67608474020490650433763373)
              ·
                refine ⟨25353177757683993912661265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67608474020490650433763373 25353177757683993912661265)
                ·
                  refine ⟨19014883318262995434495949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25353177757683993912661265 19014883318262995434495949)
                  ·
                    refine ⟨7130581244348623287935981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19014883318262995434495949 7130581244348623287935981)
                    ·
                      refine ⟨2673967966630733732975993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7130581244348623287935981 2673967966630733732975993)
                      ·
                        rfl

theorem cell23_5207534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_5207534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207534 prefixEnd_5207534 := by exact prefixLift 5207534
  have htrace : WordTrace (prefixWord ++ tailWord_5207534) baseStart_5207534 baseEnd_5207534 := by
    simpa [prefixWord, tailWord_5207534, baseEnd_5207534] using wordTrace_append hprefix tailTrace_5207534
  have hstable : (prefixWord ++ tailWord_5207534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207534).length < 2 ^ (prefixWord ++ tailWord_5207534).sum := by decide
  have hdescent : baseEnd_5207534 < baseStart_5207534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207537 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 1, 7]
def baseStart_5207537 : Nat := 118140960795 + 5207537 * 2 ^ 59
def prefixEnd_5207537 : Nat := 4983230072969 + 3 ^ 40 * 5207537 * 2
def baseEnd_5207537 : Nat := 891323169024232407079493

theorem tailTrace_5207537 : CollatzResearch.WordTrace tailWord_5207537 prefixEnd_5207537 891323169024232407079493 := by
  unfold tailWord_5207537
  simp only [CollatzResearch.WordTrace]
  refine ⟨189934478134990300357828865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126622985423326866905219243 189934478134990300357828865)
  ·
    refine ⟨142450858601242725268371649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189934478134990300357828865 142450858601242725268371649)
    ·
      refine ⟨106838143950932043951278737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142450858601242725268371649 106838143950932043951278737)
      ·
        refine ⟨80128607963199032963459053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106838143950932043951278737 80128607963199032963459053)
        ·
          refine ⟨30048227986199637361297145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80128607963199032963459053 30048227986199637361297145)
          ·
            refine ⟨22536170989649728020972859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30048227986199637361297145 22536170989649728020972859)
            ·
              refine ⟨33804256484474592031459289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22536170989649728020972859 33804256484474592031459289)
              ·
                refine ⟨25353192363355944023594467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33804256484474592031459289 25353192363355944023594467)
                ·
                  refine ⟨38029788545033916035391701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25353192363355944023594467 38029788545033916035391701)
                  ·
                    refine ⟨891323169024232407079493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38029788545033916035391701 891323169024232407079493)
                    ·
                      rfl

theorem cell23_5207537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_5207537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207537 prefixEnd_5207537 := by exact prefixLift 5207537
  have htrace : WordTrace (prefixWord ++ tailWord_5207537) baseStart_5207537 baseEnd_5207537 := by
    simpa [prefixWord, tailWord_5207537, baseEnd_5207537] using wordTrace_append hprefix tailTrace_5207537
  have hstable : (prefixWord ++ tailWord_5207537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207537).length < 2 ^ (prefixWord ++ tailWord_5207537).sum := by decide
  have hdescent : baseEnd_5207537 < baseStart_5207537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207658 : List Nat := [3, 1, 3, 2, 1, 3, 1, 2, 3, 1, 3]
def baseStart_5207658 : Nat := 118140960795 + 5207658 * 2 ^ 59
def prefixEnd_5207658 : Nat := 4983230072969 + 3 ^ 40 * 5207658 * 2
def baseEnd_5207658 : Nat := 2674031638231891247825423

theorem tailTrace_5207658 : CollatzResearch.WordTrace tailWord_5207658 prefixEnd_5207658 2674031638231891247825423 := by
  unfold tailWord_5207658
  simp only [CollatzResearch.WordTrace]
  refine ⟨47484722841887984505745907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126625927578367958681989085 47484722841887984505745907)
  ·
    refine ⟨71227084262831976758618861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47484722841887984505745907 71227084262831976758618861)
    ·
      refine ⟨26710156598561991284482073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71227084262831976758618861 26710156598561991284482073)
      ·
        refine ⟨20032617448921493463361555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26710156598561991284482073 20032617448921493463361555)
        ·
          refine ⟨30048926173382240195042333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20032617448921493463361555 30048926173382240195042333)
          ·
            refine ⟨11268347315018340073140875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30048926173382240195042333 11268347315018340073140875)
            ·
              refine ⟨16902520972527510109711313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11268347315018340073140875 16902520972527510109711313)
              ·
                refine ⟨12676890729395632582283485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16902520972527510109711313 12676890729395632582283485)
                ·
                  refine ⟨4753834023523362218356307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12676890729395632582283485 4753834023523362218356307)
                  ·
                    refine ⟨7130751035285043327534461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4753834023523362218356307 7130751035285043327534461)
                    ·
                      refine ⟨2674031638231891247825423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7130751035285043327534461 2674031638231891247825423)
                      ·
                        rfl

theorem cell23_5207658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_5207658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207658 prefixEnd_5207658 := by exact prefixLift 5207658
  have htrace : WordTrace (prefixWord ++ tailWord_5207658) baseStart_5207658 baseEnd_5207658 := by
    simpa [prefixWord, tailWord_5207658, baseEnd_5207658] using wordTrace_append hprefix tailTrace_5207658
  have hstable : (prefixWord ++ tailWord_5207658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207658).length < 2 ^ (prefixWord ++ tailWord_5207658).sum := by decide
  have hdescent : baseEnd_5207658 < baseStart_5207658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207708 : List Nat := [2, 2, 3, 2, 3, 2, 1, 1, 1, 6]
def baseStart_5207708 : Nat := 118140960795 + 5207708 * 2 ^ 59
def prefixEnd_5207708 : Nat := 4983230072969 + 3 ^ 40 * 5207708 * 2
def baseEnd_5207708 : Nat := 891352437421538684066731

theorem tailTrace_5207708 : CollatzResearch.WordTrace tailWord_5207708 prefixEnd_5207708 891352437421538684066731 := by
  unfold tailWord_5207708
  simp only [CollatzResearch.WordTrace]
  refine ⟨94970357508685398281151889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126627143344913864374869185 94970357508685398281151889)
  ·
    refine ⟨71227768131514048710863917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94970357508685398281151889 71227768131514048710863917)
    ·
      refine ⟨26710413049317768266573969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71227768131514048710863917 26710413049317768266573969)
      ·
        refine ⟨20032809786988326199930477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26710413049317768266573969 20032809786988326199930477)
        ·
          refine ⟨7512303670120622324973929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20032809786988326199930477 7512303670120622324973929)
          ·
            refine ⟨5634227752590466743730447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7512303670120622324973929 5634227752590466743730447)
            ·
              refine ⟨8451341628885700115595671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5634227752590466743730447 8451341628885700115595671)
              ·
                refine ⟨12677012443328550173393507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8451341628885700115595671 12677012443328550173393507)
                ·
                  refine ⟨19015518664992825260090261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12677012443328550173393507 19015518664992825260090261)
                  ·
                    refine ⟨891352437421538684066731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19015518664992825260090261 891352437421538684066731)
                    ·
                      rfl

theorem cell23_5207708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_5207708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207708 prefixEnd_5207708 := by exact prefixLift 5207708
  have htrace : WordTrace (prefixWord ++ tailWord_5207708) baseStart_5207708 baseEnd_5207708 := by
    simpa [prefixWord, tailWord_5207708, baseEnd_5207708] using wordTrace_append hprefix tailTrace_5207708
  have hstable : (prefixWord ++ tailWord_5207708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207708).length < 2 ^ (prefixWord ++ tailWord_5207708).sum := by decide
  have hdescent : baseEnd_5207708 < baseStart_5207708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207726 : List Nat := [4, 1, 4, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_5207726 : Nat := 118140960795 + 5207726 * 2 ^ 59
def prefixEnd_5207726 : Nat := 4983230072969 + 3 ^ 40 * 5207726 * 2
def baseEnd_5207726 : Nat := 2674066554916396981775111

theorem tailTrace_5207726 : CollatzResearch.WordTrace tailWord_5207726 prefixEnd_5207726 2674066554916396981775111 := by
  unfold tailWord_5207726
  simp only [CollatzResearch.WordTrace]
  refine ⟨23742671441413198204557379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126627581020870390424306021 23742671441413198204557379)
  ·
    refine ⟨35614007162119797306836069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23742671441413198204557379 35614007162119797306836069)
    ·
      refine ⟨6677626342897461995031763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35614007162119797306836069 6677626342897461995031763)
      ·
        refine ⟨10016439514346192992547645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6677626342897461995031763 10016439514346192992547645)
        ·
          refine ⟨3756164817879822372205367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10016439514346192992547645 3756164817879822372205367)
          ·
            refine ⟨5634247226819733558308051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3756164817879822372205367 5634247226819733558308051)
            ·
              refine ⟨8451370840229600337462077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5634247226819733558308051 8451370840229600337462077)
              ·
                refine ⟨3169264065086100126548279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8451370840229600337462077 3169264065086100126548279)
                ·
                  refine ⟨4753896097629150189822419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3169264065086100126548279 4753896097629150189822419)
                  ·
                    refine ⟨7130844146443725284733629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4753896097629150189822419 7130844146443725284733629)
                    ·
                      refine ⟨2674066554916396981775111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7130844146443725284733629 2674066554916396981775111)
                      ·
                        rfl

theorem cell23_5207726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_5207726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207726 prefixEnd_5207726 := by exact prefixLift 5207726
  have htrace : WordTrace (prefixWord ++ tailWord_5207726) baseStart_5207726 baseEnd_5207726 := by
    simpa [prefixWord, tailWord_5207726, baseEnd_5207726] using wordTrace_append hprefix tailTrace_5207726
  have hstable : (prefixWord ++ tailWord_5207726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207726).length < 2 ^ (prefixWord ++ tailWord_5207726).sum := by decide
  have hdescent : baseEnd_5207726 < baseStart_5207726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207731 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 6, 1, 3]
def baseStart_5207731 : Nat := 118140960795 + 5207731 * 2 ^ 59
def prefixEnd_5207731 : Nat := 4983230072969 + 3 ^ 40 * 5207731 * 2
def baseEnd_5207731 : Nat := 2674069122319669462212587

theorem tailTrace_5207731 : CollatzResearch.WordTrace tailWord_5207731 prefixEnd_5207731 2674069122319669462212587 := by
  unfold tailWord_5207731
  simp only [CollatzResearch.WordTrace]
  refine ⟨189941553896287471490391047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126627702597524980993594031 189941553896287471490391047)
  ·
    refine ⟨284912330844431207235586571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189941553896287471490391047 284912330844431207235586571)
    ·
      refine ⟨427368496266646810853379857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284912330844431207235586571 427368496266646810853379857)
      ·
        refine ⟨320526372199985108140034893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 427368496266646810853379857 320526372199985108140034893)
        ·
          refine ⟨120197389574994415552513085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320526372199985108140034893 120197389574994415552513085)
          ·
            refine ⟨45074021090622905832192407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120197389574994415552513085 45074021090622905832192407)
            ·
              refine ⟨67611031635934358748288611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45074021090622905832192407 67611031635934358748288611)
              ·
                refine ⟨101416547453901538122432917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67611031635934358748288611 101416547453901538122432917)
                ·
                  refine ⟨4753900661901634599489043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 101416547453901538122432917 4753900661901634599489043)
                  ·
                    refine ⟨7130850992852451899233565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4753900661901634599489043 7130850992852451899233565)
                    ·
                      refine ⟨2674069122319669462212587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7130850992852451899233565 2674069122319669462212587)
                      ·
                        rfl

theorem cell23_5207731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 1, 3].length) (baseStart_5207731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207731 prefixEnd_5207731 := by exact prefixLift 5207731
  have htrace : WordTrace (prefixWord ++ tailWord_5207731) baseStart_5207731 baseEnd_5207731 := by
    simpa [prefixWord, tailWord_5207731, baseEnd_5207731] using wordTrace_append hprefix tailTrace_5207731
  have hstable : (prefixWord ++ tailWord_5207731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207731).length < 2 ^ (prefixWord ++ tailWord_5207731).sum := by decide
  have hdescent : baseEnd_5207731 < baseStart_5207731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207744 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 5]
def baseStart_5207744 : Nat := 118140960795 + 5207744 * 2 ^ 59
def prefixEnd_5207744 : Nat := 4983230072969 + 3 ^ 40 * 5207744 * 2
def baseEnd_5207744 : Nat := 2674075797568177911350027

theorem tailTrace_5207744 : CollatzResearch.WordTrace tailWord_5207744 prefixEnd_5207744 2674075797568177911350027 := by
  unfold tailWord_5207744
  simp only [CollatzResearch.WordTrace]
  refine ⟨94971014022620187355307143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126628018696826916473742857 94971014022620187355307143)
  ·
    refine ⟨142456521033930281032960715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94971014022620187355307143 142456521033930281032960715)
    ·
      refine ⟨213684781550895421549441073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142456521033930281032960715 213684781550895421549441073)
      ·
        refine ⟨160263586163171566162080805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213684781550895421549441073 160263586163171566162080805)
        ·
          refine ⟨30049422405594668655390151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160263586163171566162080805 30049422405594668655390151)
          ·
            refine ⟨45074133608392002983085227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30049422405594668655390151 45074133608392002983085227)
            ·
              refine ⟨67611200412588004474627841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45074133608392002983085227 67611200412588004474627841)
              ·
                refine ⟨50708400309441003355970881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67611200412588004474627841 50708400309441003355970881)
                ·
                  refine ⟨38031300232080752516978161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50708400309441003355970881 38031300232080752516978161)
                  ·
                    refine ⟨28523475174060564387733621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38031300232080752516978161 28523475174060564387733621)
                    ·
                      refine ⟨2674075797568177911350027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28523475174060564387733621 2674075797568177911350027)
                      ·
                        rfl

theorem cell23_5207744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_5207744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207744 prefixEnd_5207744 := by exact prefixLift 5207744
  have htrace : WordTrace (prefixWord ++ tailWord_5207744) baseStart_5207744 baseEnd_5207744 := by
    simpa [prefixWord, tailWord_5207744, baseEnd_5207744] using wordTrace_append hprefix tailTrace_5207744
  have hstable : (prefixWord ++ tailWord_5207744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207744).length < 2 ^ (prefixWord ++ tailWord_5207744).sum := by decide
  have hdescent : baseEnd_5207744 < baseStart_5207744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207748 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_5207748 : Nat := 118140960795 + 5207748 * 2 ^ 59
def prefixEnd_5207748 : Nat := 4983230072969 + 3 ^ 40 * 5207748 * 2
def baseEnd_5207748 : Nat := 2674077851490795895700009

theorem tailTrace_5207748 : CollatzResearch.WordTrace tailWord_5207748 prefixEnd_5207748 2674077851490795895700009 := by
  unfold tailWord_5207748
  simp only [CollatzResearch.WordTrace]
  refine ⟨94971086968612941696879949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126628115958150588929173265 94971086968612941696879949)
  ·
    refine ⟨35614157613229853136329981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94971086968612941696879949 35614157613229853136329981)
    ·
      refine ⟨13355309104961194926123743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35614157613229853136329981 13355309104961194926123743)
      ·
        refine ⟨20032963657441792389185615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13355309104961194926123743 20032963657441792389185615)
        ·
          refine ⟨30049445486162688583778423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20032963657441792389185615 30049445486162688583778423)
          ·
            refine ⟨45074168229244032875667635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30049445486162688583778423 45074168229244032875667635)
            ·
              refine ⟨67611252343866049313501453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45074168229244032875667635 67611252343866049313501453)
              ·
                refine ⟨25354219628949768492563045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67611252343866049313501453 25354219628949768492563045)
                ·
                  refine ⟨4753916180428081592355571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25354219628949768492563045 4753916180428081592355571)
                  ·
                    refine ⟨7130874270642122388533357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4753916180428081592355571 7130874270642122388533357)
                    ·
                      refine ⟨2674077851490795895700009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7130874270642122388533357 2674077851490795895700009)
                      ·
                        rfl

theorem cell23_5207748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_5207748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207748 prefixEnd_5207748 := by exact prefixLift 5207748
  have htrace : WordTrace (prefixWord ++ tailWord_5207748) baseStart_5207748 baseEnd_5207748 := by
    simpa [prefixWord, tailWord_5207748, baseEnd_5207748] using wordTrace_append hprefix tailTrace_5207748
  have hstable : (prefixWord ++ tailWord_5207748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207748).length < 2 ^ (prefixWord ++ tailWord_5207748).sum := by decide
  have hdescent : baseEnd_5207748 < baseStart_5207748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207758 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2]
def baseStart_5207758 : Nat := 118140960795 + 5207758 * 2 ^ 59
def prefixEnd_5207758 : Nat := 4983230072969 + 3 ^ 40 * 5207758 * 2
def baseEnd_5207758 : Nat := 2674082986297340856574963

theorem tailTrace_5207758 : CollatzResearch.WordTrace tailWord_5207758 prefixEnd_5207758 2674082986297340856574963 := by
  unfold tailWord_5207758
  simp only [CollatzResearch.WordTrace]
  refine ⟨23742817333398706887702991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126628359111459770067749285 23742817333398706887702991)
  ·
    refine ⟨35614226000098060331554487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23742817333398706887702991 35614226000098060331554487)
    ·
      refine ⟨53421339000147090497331731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35614226000098060331554487 53421339000147090497331731)
      ·
        refine ⟨80132008500220635745997597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53421339000147090497331731 80132008500220635745997597)
        ·
          refine ⟨30049503187582738404749099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80132008500220635745997597 30049503187582738404749099)
          ·
            refine ⟨45074254781374107607123649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30049503187582738404749099 45074254781374107607123649)
            ·
              refine ⟨33805691086030580705342737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45074254781374107607123649 33805691086030580705342737)
              ·
                refine ⟨25354268314522935529007053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33805691086030580705342737 25354268314522935529007053)
                ·
                  refine ⟨9507850617946100823377645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25354268314522935529007053 9507850617946100823377645)
                  ·
                    refine ⟨3565443981729787808766617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9507850617946100823377645 3565443981729787808766617)
                    ·
                      refine ⟨2674082986297340856574963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3565443981729787808766617 2674082986297340856574963)
                      ·
                        rfl

theorem cell23_5207758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2].length) (baseStart_5207758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207758 prefixEnd_5207758 := by exact prefixLift 5207758
  have htrace : WordTrace (prefixWord ++ tailWord_5207758) baseStart_5207758 baseEnd_5207758 := by
    simpa [prefixWord, tailWord_5207758, baseEnd_5207758] using wordTrace_append hprefix tailTrace_5207758
  have hstable : (prefixWord ++ tailWord_5207758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207758).length < 2 ^ (prefixWord ++ tailWord_5207758).sum := by decide
  have hdescent : baseEnd_5207758 < baseStart_5207758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207788 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 6, 2, 2]
def baseStart_5207788 : Nat := 118140960795 + 5207788 * 2 ^ 59
def prefixEnd_5207788 : Nat := 4983230072969 + 3 ^ 40 * 5207788 * 2
def baseEnd_5207788 : Nat := 2674098390716975739199825

theorem tailTrace_5207788 : CollatzResearch.WordTrace tailWord_5207788 prefixEnd_5207788 2674098390716975739199825 := by
  unfold tailWord_5207788
  simp only [CollatzResearch.WordTrace]
  refine ⟨94971816428540485112608009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126629088571387313483477345 94971816428540485112608009)
  ·
    refine ⟨71228862321405363834456007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94971816428540485112608009 71228862321405363834456007)
    ·
      refine ⟨106843293482108045751684011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71228862321405363834456007 106843293482108045751684011)
      ·
        refine ⟨160264940223162068627526017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106843293482108045751684011 160264940223162068627526017)
        ·
          refine ⟨120198705167371551470644513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160264940223162068627526017 120198705167371551470644513)
          ·
            refine ⟨90149028875528663602983385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120198705167371551470644513 90149028875528663602983385)
            ·
              refine ⟨67611771656646497702237539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90149028875528663602983385 67611771656646497702237539)
              ·
                refine ⟨101417657484969746553356309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67611771656646497702237539 101417657484969746553356309)
                ·
                  refine ⟨4753952694607956869688577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 101417657484969746553356309 4753952694607956869688577)
                  ·
                    refine ⟨3565464520955967652266433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4753952694607956869688577 3565464520955967652266433)
                    ·
                      refine ⟨2674098390716975739199825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3565464520955967652266433 2674098390716975739199825)
                      ·
                        rfl

theorem cell23_5207788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 2, 2].length) (baseStart_5207788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207788 prefixEnd_5207788 := by exact prefixLift 5207788
  have htrace : WordTrace (prefixWord ++ tailWord_5207788) baseStart_5207788 baseEnd_5207788 := by
    simpa [prefixWord, tailWord_5207788, baseEnd_5207788] using wordTrace_append hprefix tailTrace_5207788
  have hstable : (prefixWord ++ tailWord_5207788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207788).length < 2 ^ (prefixWord ++ tailWord_5207788).sum := by decide
  have hdescent : baseEnd_5207788 < baseStart_5207788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207841 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 1, 7]
def baseStart_5207841 : Nat := 118140960795 + 5207841 * 2 ^ 59
def prefixEnd_5207841 : Nat := 4983230072969 + 3 ^ 40 * 5207841 * 2
def baseEnd_5207841 : Nat := 891375201730554677279027

theorem tailTrace_5207841 : CollatzResearch.WordTrace tailWord_5207841 prefixEnd_5207841 891375201730554677279027 := by
  unfold tailWord_5207841
  simp only [CollatzResearch.WordTrace]
  refine ⟨189945565925888960276895377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126630377283925973517930251 189945565925888960276895377)
  ·
    refine ⟨142459174444416720207671533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189945565925888960276895377 142459174444416720207671533)
    ·
      refine ⟨53422190416656270077876825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142459174444416720207671533 53422190416656270077876825)
      ·
        refine ⟨40066642812492202558407619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53422190416656270077876825 40066642812492202558407619)
        ·
          refine ⟨60099964218738303837611429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40066642812492202558407619 60099964218738303837611429)
          ·
            refine ⟨11268743291013431969552143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60099964218738303837611429 11268743291013431969552143)
            ·
              refine ⟨16903114936520147954328215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11268743291013431969552143 16903114936520147954328215)
              ·
                refine ⟨25354672404780221931492323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16903114936520147954328215 25354672404780221931492323)
                ·
                  refine ⟨38032008607170332897238485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25354672404780221931492323 38032008607170332897238485)
                  ·
                    refine ⟨891375201730554677279027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38032008607170332897238485 891375201730554677279027)
                    ·
                      rfl

theorem cell23_5207841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_5207841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207841 prefixEnd_5207841 := by exact prefixLift 5207841
  have htrace : WordTrace (prefixWord ++ tailWord_5207841) baseStart_5207841 baseEnd_5207841 := by
    simpa [prefixWord, tailWord_5207841, baseEnd_5207841] using wordTrace_append hprefix tailTrace_5207841
  have hstable : (prefixWord ++ tailWord_5207841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207841).length < 2 ^ (prefixWord ++ tailWord_5207841).sum := by decide
  have hdescent : baseEnd_5207841 < baseStart_5207841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207881 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 3, 4, 3]
def baseStart_5207881 : Nat := 118140960795 + 5207881 * 2 ^ 59
def prefixEnd_5207881 : Nat := 4983230072969 + 3 ^ 40 * 5207881 * 2
def baseEnd_5207881 : Nat := 2674146144417843875336897

theorem tailTrace_5207881 : CollatzResearch.WordTrace tailWord_5207881 prefixEnd_5207881 2674146144417843875336897 := by
  unfold tailWord_5207881
  simp only [CollatzResearch.WordTrace]
  refine ⟨189947024845744047108351497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126631349897162698072234331 189947024845744047108351497)
  ·
    refine ⟨142460268634308035331263623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189947024845744047108351497 142460268634308035331263623)
    ·
      refine ⟨213690402951462052996895435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142460268634308035331263623 213690402951462052996895435)
      ·
        refine ⟨320535604427193079495343153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213690402951462052996895435 320535604427193079495343153)
        ·
          refine ⟨240401703320394809621507365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320535604427193079495343153 240401703320394809621507365)
          ·
            refine ⟨45075319372574026804032631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 240401703320394809621507365 45075319372574026804032631)
            ·
              refine ⟨67612979058861040206048947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45075319372574026804032631 67612979058861040206048947)
              ·
                refine ⟨101419468588291560309073421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67612979058861040206048947 101419468588291560309073421)
                ·
                  refine ⟨38032300720609335115902533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101419468588291560309073421 38032300720609335115902533)
                  ·
                    refine ⟨7131056385114250334231725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38032300720609335115902533 7131056385114250334231725)
                    ·
                      refine ⟨2674146144417843875336897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7131056385114250334231725 2674146144417843875336897)
                      ·
                        rfl

theorem cell23_5207881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 4, 3].length) (baseStart_5207881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207881 prefixEnd_5207881 := by exact prefixLift 5207881
  have htrace : WordTrace (prefixWord ++ tailWord_5207881) baseStart_5207881 baseEnd_5207881 := by
    simpa [prefixWord, tailWord_5207881, baseEnd_5207881] using wordTrace_append hprefix tailTrace_5207881
  have hstable : (prefixWord ++ tailWord_5207881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207881).length < 2 ^ (prefixWord ++ tailWord_5207881).sum := by decide
  have hdescent : baseEnd_5207881 < baseStart_5207881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207898 : List Nat := [3, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3]
def baseStart_5207898 : Nat := 118140960795 + 5207898 * 2 ^ 59
def prefixEnd_5207898 : Nat := 4983230072969 + 3 ^ 40 * 5207898 * 2
def baseEnd_5207898 : Nat := 2674154873588970308824319

theorem tailTrace_5207898 : CollatzResearch.WordTrace tailWord_5207898 prefixEnd_5207898 2674154873588970308824319 := by
  unfold tailWord_5207898
  simp only [CollatzResearch.WordTrace]
  refine ⟨47486911221670614752930087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126631763257788306007813565 47486911221670614752930087)
  ·
    refine ⟨71230366832505922129395131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47486911221670614752930087 71230366832505922129395131)
    ·
      refine ⟨106845550248758883194092697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71230366832505922129395131 106845550248758883194092697)
      ·
        refine ⟨80134162686569162395569523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106845550248758883194092697 80134162686569162395569523)
        ·
          refine ⟨120201244029853743593354285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80134162686569162395569523 120201244029853743593354285)
          ·
            refine ⟨45075466511195153847507857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120201244029853743593354285 45075466511195153847507857)
            ·
              refine ⟨33806599883396365385630893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45075466511195153847507857 33806599883396365385630893)
              ·
                refine ⟨12677474956273637019611585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33806599883396365385630893 12677474956273637019611585)
                ·
                  refine ⟨9508106217205227764708689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12677474956273637019611585 9508106217205227764708689)
                  ·
                    refine ⟨7131079662903920823531517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9508106217205227764708689 7131079662903920823531517)
                    ·
                      refine ⟨2674154873588970308824319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7131079662903920823531517 2674154873588970308824319)
                      ·
                        rfl

theorem cell23_5207898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_5207898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207898 prefixEnd_5207898 := by exact prefixLift 5207898
  have htrace : WordTrace (prefixWord ++ tailWord_5207898) baseStart_5207898 baseEnd_5207898 := by
    simpa [prefixWord, tailWord_5207898, baseEnd_5207898] using wordTrace_append hprefix tailTrace_5207898
  have hstable : (prefixWord ++ tailWord_5207898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207898).length < 2 ^ (prefixWord ++ tailWord_5207898).sum := by decide
  have hdescent : baseEnd_5207898 < baseStart_5207898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207918 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 8]
def baseStart_5207918 : Nat := 118140960795 + 5207918 * 2 ^ 59
def prefixEnd_5207918 : Nat := 4983230072969 + 3 ^ 40 * 5207918 * 2
def baseEnd_5207918 : Nat := 297129460355784470063803

theorem tailTrace_5207918 : CollatzResearch.WordTrace tailWord_5207918 prefixEnd_5207918 297129460355784470063803 := by
  unfold tailWord_5207918
  simp only [CollatzResearch.WordTrace]
  refine ⟨23743546793326250303431051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126632249564406668284965605 23743546793326250303431051)
  ·
    refine ⟨35615320189989375455146577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23743546793326250303431051 35615320189989375455146577)
    ·
      refine ⟨26711490142492031591359933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35615320189989375455146577 26711490142492031591359933)
      ·
        refine ⟨10016808803434511846759975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26711490142492031591359933 10016808803434511846759975)
        ·
          refine ⟨15025213205151767770139963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10016808803434511846759975 15025213205151767770139963)
          ·
            refine ⟨22537819807727651655209945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15025213205151767770139963 22537819807727651655209945)
            ·
              refine ⟨16903364855795738741407459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22537819807727651655209945 16903364855795738741407459)
              ·
                refine ⟨25355047283693608112111189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16903364855795738741407459 25355047283693608112111189)
                ·
                  refine ⟨297129460355784470063803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25355047283693608112111189 297129460355784470063803)
                  ·
                    rfl

theorem cell23_5207918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_5207918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207918 prefixEnd_5207918 := by exact prefixLift 5207918
  have htrace : WordTrace (prefixWord ++ tailWord_5207918) baseStart_5207918 baseEnd_5207918 := by
    simpa [prefixWord, tailWord_5207918, baseEnd_5207918] using wordTrace_append hprefix tailTrace_5207918
  have hstable : (prefixWord ++ tailWord_5207918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207918).length < 2 ^ (prefixWord ++ tailWord_5207918).sum := by decide
  have hdescent : baseEnd_5207918 < baseStart_5207918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207931 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 3, 5]
def baseStart_5207931 : Nat := 118140960795 + 5207931 * 2 ^ 59
def prefixEnd_5207931 : Nat := 4983230072969 + 3 ^ 40 * 5207931 * 2
def baseEnd_5207931 : Nat := 891390606150189559903889

theorem tailTrace_5207931 : CollatzResearch.WordTrace tailWord_5207931 prefixEnd_5207931 891390606150189559903889 := by
  unfold tailWord_5207931
  simp only [CollatzResearch.WordTrace]
  refine ⟨189948848495562905647671647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126632565663708603765114431 189948848495562905647671647)
  ·
    refine ⟨284923272743344358471507471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189948848495562905647671647 284923272743344358471507471)
    ·
      refine ⟨427384909115016537707261207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284923272743344358471507471 427384909115016537707261207)
      ·
        refine ⟨641077363672524806560891811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427384909115016537707261207 641077363672524806560891811)
        ·
          refine ⟨961616045508787209841337717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 641077363672524806560891811 961616045508787209841337717)
          ·
            refine ⟨90151504266448800922625411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 961616045508787209841337717 90151504266448800922625411)
            ·
              refine ⟨135227256399673201383938117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90151504266448800922625411 135227256399673201383938117)
              ·
                refine ⟨25355110574938725259488397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135227256399673201383938117 25355110574938725259488397)
                ·
                  refine ⟨9508166465602021972308149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25355110574938725259488397 9508166465602021972308149)
                  ·
                    refine ⟨891390606150189559903889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9508166465602021972308149 891390606150189559903889)
                    ·
                      rfl

theorem cell23_5207931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 5].length) (baseStart_5207931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207931 prefixEnd_5207931 := by exact prefixLift 5207931
  have htrace : WordTrace (prefixWord ++ tailWord_5207931) baseStart_5207931 baseEnd_5207931 := by
    simpa [prefixWord, tailWord_5207931, baseEnd_5207931] using wordTrace_append hprefix tailTrace_5207931
  have hstable : (prefixWord ++ tailWord_5207931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207931).length < 2 ^ (prefixWord ++ tailWord_5207931).sum := by decide
  have hdescent : baseEnd_5207931 < baseStart_5207931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5207961 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 3, 6]
def baseStart_5207961 : Nat := 118140960795 + 5207961 * 2 ^ 59
def prefixEnd_5207961 : Nat := 4983230072969 + 3 ^ 40 * 5207961 * 2
def baseEnd_5207961 : Nat := 891395740956734520778843

theorem tailTrace_5207961 : CollatzResearch.WordTrace tailWord_5207961 prefixEnd_5207961 891395740956734520778843 := by
  unfold tailWord_5207961
  simp only [CollatzResearch.WordTrace]
  refine ⟨189949942685454220771263737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126633295123636147180842491 189949942685454220771263737)
  ·
    refine ⟨142462457014090665578447803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189949942685454220771263737 142462457014090665578447803)
    ·
      refine ⟨213693685521135998367671705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142462457014090665578447803 213693685521135998367671705)
      ·
        refine ⟨160270264140851998775753779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213693685521135998367671705 160270264140851998775753779)
        ·
          refine ⟨240405396211277998163630669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160270264140851998775753779 240405396211277998163630669)
          ·
            refine ⟨90152023579229249311361501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240405396211277998163630669 90152023579229249311361501)
            ·
              refine ⟨33807008842210968491760563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90152023579229249311361501 33807008842210968491760563)
              ·
                refine ⟨50710513263316452737640845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33807008842210968491760563 50710513263316452737640845)
                ·
                  refine ⟨19016442473743669776615317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50710513263316452737640845 19016442473743669776615317)
                  ·
                    refine ⟨891395740956734520778843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19016442473743669776615317 891395740956734520778843)
                    ·
                      rfl

theorem cell23_5207961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 6].length) (baseStart_5207961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5207961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5207961 prefixEnd_5207961 := by exact prefixLift 5207961
  have htrace : WordTrace (prefixWord ++ tailWord_5207961) baseStart_5207961 baseEnd_5207961 := by
    simpa [prefixWord, tailWord_5207961, baseEnd_5207961] using wordTrace_append hprefix tailTrace_5207961
  have hstable : (prefixWord ++ tailWord_5207961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5207961).length < 2 ^ (prefixWord ++ tailWord_5207961).sum := by decide
  have hdescent : baseEnd_5207961 < baseStart_5207961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5207961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208029 : List Nat := [1, 4, 3, 1, 3, 2, 1, 2, 2, 4]
def baseStart_5208029 : Nat := 118140960795 + 5208029 * 2 ^ 59
def prefixEnd_5208029 : Nat := 4983230072969 + 3 ^ 40 * 5208029 * 2
def baseEnd_5208029 : Nat := 891407379851569765428739

theorem tailTrace_5208029 : CollatzResearch.WordTrace tailWord_5208029 prefixEnd_5208029 891407379851569765428739 := by
  unfold tailWord_5208029
  simp only [CollatzResearch.WordTrace]
  refine ⟨189952422849207868384739141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126634948566138578923159427 189952422849207868384739141)
  ·
    refine ⟨35616079284226475322138589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189952422849207868384739141 35616079284226475322138589)
    ·
      refine ⟨13356029731584928245801971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35616079284226475322138589 13356029731584928245801971)
      ·
        refine ⟨20034044597377392368702957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13356029731584928245801971 20034044597377392368702957)
        ·
          refine ⟨7512766724016522138263609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20034044597377392368702957 7512766724016522138263609)
          ·
            refine ⟨5634575043012391603697707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7512766724016522138263609 5634575043012391603697707)
            ·
              refine ⟨8451862564518587405546561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5634575043012391603697707 8451862564518587405546561)
              ·
                refine ⟨6338896923388940554159921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8451862564518587405546561 6338896923388940554159921)
                ·
                  refine ⟨4754172692541705415619941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6338896923388940554159921 4754172692541705415619941)
                  ·
                    refine ⟨891407379851569765428739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4754172692541705415619941 891407379851569765428739)
                    ·
                      rfl

theorem cell23_5208029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_5208029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208029 prefixEnd_5208029 := by exact prefixLift 5208029
  have htrace : WordTrace (prefixWord ++ tailWord_5208029) baseStart_5208029 baseEnd_5208029 := by
    simpa [prefixWord, tailWord_5208029, baseEnd_5208029] using wordTrace_append hprefix tailTrace_5208029
  have hstable : (prefixWord ++ tailWord_5208029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208029).length < 2 ^ (prefixWord ++ tailWord_5208029).sum := by decide
  have hdescent : baseEnd_5208029 < baseStart_5208029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208075 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 3, 4, 2]
def baseStart_5208075 : Nat := 118140960795 + 5208075 * 2 ^ 59
def prefixEnd_5208075 : Nat := 4983230072969 + 3 ^ 40 * 5208075 * 2
def baseEnd_5208075 : Nat := 2674245759664816116311005

theorem tailTrace_5208075 : CollatzResearch.WordTrace tailWord_5208075 prefixEnd_5208075 2674245759664816116311005 := by
  unfold tailWord_5208075
  simp only [CollatzResearch.WordTrace]
  refine ⟨189954100607041218240913679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126636067071360812160609119 189954100607041218240913679)
  ·
    refine ⟨284931150910561827361370519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189954100607041218240913679 284931150910561827361370519)
    ·
      refine ⟨427396726365842741042055779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284931150910561827361370519 427396726365842741042055779)
      ·
        refine ⟨641095089548764111563083669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427396726365842741042055779 641095089548764111563083669)
        ·
          refine ⟨30051332322598317729519547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 641095089548764111563083669 30051332322598317729519547)
          ·
            refine ⟨45076998483897476594279321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30051332322598317729519547 45076998483897476594279321)
            ·
              refine ⟨33807748862923107445709491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45076998483897476594279321 33807748862923107445709491)
              ·
                refine ⟨50711623294384661168564237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33807748862923107445709491 50711623294384661168564237)
                ·
                  refine ⟨19016858735394247938211589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50711623294384661168564237 19016858735394247938211589)
                  ·
                    refine ⟨3565661012886421488414673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19016858735394247938211589 3565661012886421488414673)
                    ·
                      refine ⟨2674245759664816116311005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3565661012886421488414673 2674245759664816116311005)
                      ·
                        rfl

theorem cell23_5208075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 4, 2].length) (baseStart_5208075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208075 prefixEnd_5208075 := by exact prefixLift 5208075
  have htrace : WordTrace (prefixWord ++ tailWord_5208075) baseStart_5208075 baseEnd_5208075 := by
    simpa [prefixWord, tailWord_5208075, baseEnd_5208075] using wordTrace_append hprefix tailTrace_5208075
  have hstable : (prefixWord ++ tailWord_5208075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208075).length < 2 ^ (prefixWord ++ tailWord_5208075).sum := by decide
  have hdescent : baseEnd_5208075 < baseStart_5208075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208103 : List Nat := [1, 1, 7, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_5208103 : Nat := 118140960795 + 5208103 * 2 ^ 59
def prefixEnd_5208103 : Nat := 4983230072969 + 3 ^ 40 * 5208103 * 2
def baseEnd_5208103 : Nat := 2674260137123142006760877

theorem tailTrace_5208103 : CollatzResearch.WordTrace tailWord_5208103 prefixEnd_5208103 2674260137123142006760877 := by
  unfold tailWord_5208103
  simp only [CollatzResearch.WordTrace]
  refine ⟨189955121850939779022932963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126636747900626519348621975 189955121850939779022932963)
  ·
    refine ⟨284932682776409668534399445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189955121850939779022932963 284932682776409668534399445)
    ·
      refine ⟨6678109752572101606274987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 284932682776409668534399445 6678109752572101606274987)
      ·
        refine ⟨10017164628858152409412481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6678109752572101606274987 10017164628858152409412481)
        ·
          refine ⟨7512873471643614307059361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10017164628858152409412481 7512873471643614307059361)
          ·
            refine ⟨5634655103732710730294521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7512873471643614307059361 5634655103732710730294521)
            ·
              refine ⟨4225991327799533047720891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5634655103732710730294521 4225991327799533047720891)
              ·
                refine ⟨6338986991699299571581337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4225991327799533047720891 6338986991699299571581337)
                ·
                  refine ⟨4754240243774474678686003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6338986991699299571581337 4754240243774474678686003)
                  ·
                    refine ⟨7131360365661712018029005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4754240243774474678686003 7131360365661712018029005)
                    ·
                      refine ⟨2674260137123142006760877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7131360365661712018029005 2674260137123142006760877)
                      ·
                        rfl

theorem cell23_5208103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_5208103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208103 prefixEnd_5208103 := by exact prefixLift 5208103
  have htrace : WordTrace (prefixWord ++ tailWord_5208103) baseStart_5208103 baseEnd_5208103 := by
    simpa [prefixWord, tailWord_5208103, baseEnd_5208103] using wordTrace_append hprefix tailTrace_5208103
  have hstable : (prefixWord ++ tailWord_5208103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208103).length < 2 ^ (prefixWord ++ tailWord_5208103).sum := by decide
  have hdescent : baseEnd_5208103 < baseStart_5208103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208149 : List Nat := [1, 3, 2, 2, 1, 5, 2, 2, 5]
def baseStart_5208149 : Nat := 118140960795 + 5208149 * 2 ^ 59
def prefixEnd_5208149 : Nat := 4983230072969 + 3 ^ 40 * 5208149 * 2
def baseEnd_5208149 : Nat := 297142639692583202976185

theorem tailTrace_5208149 : CollatzResearch.WordTrace tailWord_5208149 prefixEnd_5208149 297142639692583202976185 := by
  unfold tailWord_5208149
  simp only [CollatzResearch.WordTrace]
  refine ⟨189956799608773128879107501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126637866405848752586071667 189956799608773128879107501)
  ·
    refine ⟨71233799853289923329665313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189956799608773128879107501 71233799853289923329665313)
    ·
      refine ⟨53425349889967442497248985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71233799853289923329665313 53425349889967442497248985)
      ·
        refine ⟨40069012417475581872936739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53425349889967442497248985 40069012417475581872936739)
        ·
          refine ⟨60103518626213372809405109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40069012417475581872936739 60103518626213372809405109)
          ·
            refine ⟨5634704871207503700881729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60103518626213372809405109 5634704871207503700881729)
            ·
              refine ⟨4226028653405627775661297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5634704871207503700881729 4226028653405627775661297)
              ·
                refine ⟨3169521490054220831745973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4226028653405627775661297 3169521490054220831745973)
                ·
                  refine ⟨297142639692583202976185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3169521490054220831745973 297142639692583202976185)
                  ·
                    rfl

theorem cell23_5208149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 5].length) (baseStart_5208149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208149 prefixEnd_5208149 := by exact prefixLift 5208149
  have htrace : WordTrace (prefixWord ++ tailWord_5208149) baseStart_5208149 baseEnd_5208149 := by
    simpa [prefixWord, tailWord_5208149, baseEnd_5208149] using wordTrace_append hprefix tailTrace_5208149
  have hstable : (prefixWord ++ tailWord_5208149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208149).length < 2 ^ (prefixWord ++ tailWord_5208149).sum := by decide
  have hdescent : baseEnd_5208149 < baseStart_5208149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208175 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 5, 4]
def baseStart_5208175 : Nat := 118140960795 + 5208175 * 2 ^ 59
def prefixEnd_5208175 : Nat := 4983230072969 + 3 ^ 40 * 5208175 * 2
def baseEnd_5208175 : Nat := 891432369243421908353515

theorem tailTrace_5208175 : CollatzResearch.WordTrace tailWord_5208175 prefixEnd_5208175 891432369243421908353515 := by
  unfold tailWord_5208175
  simp only [CollatzResearch.WordTrace]
  refine ⟨189957747906678935319553979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126638498604452623546369319 189957747906678935319553979)
  ·
    refine ⟨284936621860018402979330969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189957747906678935319553979 284936621860018402979330969)
    ·
      refine ⟨213702466395013802234498227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284936621860018402979330969 213702466395013802234498227)
      ·
        refine ⟨320553699592520703351747341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213702466395013802234498227 320553699592520703351747341)
        ·
          refine ⟨120207637347195263756905253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320553699592520703351747341 120207637347195263756905253)
          ·
            refine ⟨22538932002599111954419735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120207637347195263756905253 22538932002599111954419735)
            ·
              refine ⟨33808398003898667931629603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22538932002599111954419735 33808398003898667931629603)
              ·
                refine ⟨50712597005848001897444405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33808398003898667931629603 50712597005848001897444405)
                ·
                  refine ⟨4754305969298250177885413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50712597005848001897444405 4754305969298250177885413)
                  ·
                    refine ⟨891432369243421908353515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4754305969298250177885413 891432369243421908353515)
                    ·
                      rfl

theorem cell23_5208175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 4].length) (baseStart_5208175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208175 prefixEnd_5208175 := by exact prefixLift 5208175
  have htrace : WordTrace (prefixWord ++ tailWord_5208175) baseStart_5208175 baseEnd_5208175 := by
    simpa [prefixWord, tailWord_5208175, baseEnd_5208175] using wordTrace_append hprefix tailTrace_5208175
  have hstable : (prefixWord ++ tailWord_5208175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208175).length < 2 ^ (prefixWord ++ tailWord_5208175).sum := by decide
  have hdescent : baseEnd_5208175 < baseStart_5208175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208182 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_5208182 : Nat := 118140960795 + 5208182 * 2 ^ 59
def prefixEnd_5208182 : Nat := 4983230072969 + 3 ^ 40 * 5208182 * 2
def baseEnd_5208182 : Nat := 2674300702094847197673013

theorem tailTrace_5208182 : CollatzResearch.WordTrace tailWord_5208182 prefixEnd_5208182 2674300702094847197673013 := by
  unfold tailWord_5208182
  simp only [CollatzResearch.WordTrace]
  refine ⟨11872375201103348469691175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126638668811769050343372533 11872375201103348469691175)
  ·
    refine ⟨17808562801655022704536763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11872375201103348469691175 17808562801655022704536763)
    ·
      refine ⟨26712844202482534056805145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17808562801655022704536763 26712844202482534056805145)
      ·
        refine ⟨20034633151861900542603859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26712844202482534056805145 20034633151861900542603859)
        ·
          refine ⟨30051949727792850813905789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20034633151861900542603859 30051949727792850813905789)
          ·
            refine ⟨11269481147922319055214671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30051949727792850813905789 11269481147922319055214671)
            ·
              refine ⟨16904221721883478582822007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11269481147922319055214671 16904221721883478582822007)
              ·
                refine ⟨25356332582825217874233011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16904221721883478582822007 25356332582825217874233011)
                ·
                  refine ⟨38034498874237826811349517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25356332582825217874233011 38034498874237826811349517)
                  ·
                    refine ⟨14262937077839185054256069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38034498874237826811349517 14262937077839185054256069)
                    ·
                      refine ⟨2674300702094847197673013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14262937077839185054256069 2674300702094847197673013)
                      ·
                        rfl

theorem cell23_5208182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_5208182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208182 prefixEnd_5208182 := by exact prefixLift 5208182
  have htrace : WordTrace (prefixWord ++ tailWord_5208182) baseStart_5208182 baseEnd_5208182 := by
    simpa [prefixWord, tailWord_5208182, baseEnd_5208182] using wordTrace_append hprefix tailTrace_5208182
  have hstable : (prefixWord ++ tailWord_5208182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208182).length < 2 ^ (prefixWord ++ tailWord_5208182).sum := by decide
  have hdescent : baseEnd_5208182 < baseStart_5208182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208208 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 8]
def baseStart_5208208 : Nat := 118140960795 + 5208208 * 2 ^ 59
def prefixEnd_5208208 : Nat := 4983230072969 + 3 ^ 40 * 5208208 * 2
def baseEnd_5208208 : Nat := 2674314052591864095947893

theorem tailTrace_5208208 : CollatzResearch.WordTrace tailWord_5208208 prefixEnd_5208208 2674314052591864095947893 := by
  unfold tailWord_5208208
  simp only [CollatzResearch.WordTrace]
  refine ⟨94979475757779690977752639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126639301010372921303670185 94979475757779690977752639)
  ·
    refine ⟨142469213636669536466628959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94979475757779690977752639 142469213636669536466628959)
    ·
      refine ⟨213703820455004304699943439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142469213636669536466628959 213703820455004304699943439)
      ·
        refine ⟨320555730682506457049915159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213703820455004304699943439 320555730682506457049915159)
        ·
          refine ⟨480833596023759685574872739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320555730682506457049915159 480833596023759685574872739)
          ·
            refine ⟨721250394035639528362309109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480833596023759685574872739 721250394035639528362309109)
            ·
              refine ⟨67617224440841205783966479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 721250394035639528362309109 67617224440841205783966479)
              ·
                refine ⟨101425836661261808675949719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67617224440841205783966479 101425836661261808675949719)
                ·
                  refine ⟨152138754991892713013924579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101425836661261808675949719 152138754991892713013924579)
                  ·
                    refine ⟨228208132487839069520886869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 152138754991892713013924579 228208132487839069520886869)
                    ·
                      refine ⟨2674314052591864095947893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 228208132487839069520886869 2674314052591864095947893)
                      ·
                        rfl

theorem cell23_5208208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_5208208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208208 prefixEnd_5208208 := by exact prefixLift 5208208
  have htrace : WordTrace (prefixWord ++ tailWord_5208208) baseStart_5208208 baseEnd_5208208 := by
    simpa [prefixWord, tailWord_5208208, baseEnd_5208208] using wordTrace_append hprefix tailTrace_5208208
  have hstable : (prefixWord ++ tailWord_5208208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208208).length < 2 ^ (prefixWord ++ tailWord_5208208).sum := by decide
  have hdescent : baseEnd_5208208 < baseStart_5208208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208242 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2]
def baseStart_5208242 : Nat := 118140960795 + 5208242 * 2 ^ 59
def prefixEnd_5208242 : Nat := 4983230072969 + 3 ^ 40 * 5208242 * 2
def baseEnd_5208242 : Nat := 2674331510934116962922737

theorem tailTrace_5208242 : CollatzResearch.WordTrace tailWord_5208242 prefixEnd_5208242 2674331510934116962922737 := by
  unfold tailWord_5208242
  simp only [CollatzResearch.WordTrace]
  refine ⟨47490047899359051440560745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126640127731624137174828653 47490047899359051440560745)
  ·
    refine ⟨35617535924519288580420559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47490047899359051440560745 35617535924519288580420559)
    ·
      refine ⟨53426303886778932870630839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35617535924519288580420559 53426303886778932870630839)
      ·
        refine ⟨80139455830168399305946259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53426303886778932870630839 80139455830168399305946259)
        ·
          refine ⟨120209183745252598958919389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80139455830168399305946259 120209183745252598958919389)
          ·
            refine ⟨45078443904469724609594771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120209183745252598958919389 45078443904469724609594771)
            ·
              refine ⟨67617665856704586914392157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45078443904469724609594771 67617665856704586914392157)
              ·
                refine ⟨25356624696264220092897059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67617665856704586914392157 25356624696264220092897059)
                ·
                  refine ⟨38034937044396330139345589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25356624696264220092897059 38034937044396330139345589)
                  ·
                    refine ⟨3565775347912155950563649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38034937044396330139345589 3565775347912155950563649)
                    ·
                      refine ⟨2674331510934116962922737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3565775347912155950563649 2674331510934116962922737)
                      ·
                        rfl

theorem cell23_5208242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2].length) (baseStart_5208242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208242 prefixEnd_5208242 := by exact prefixLift 5208242
  have htrace : WordTrace (prefixWord ++ tailWord_5208242) baseStart_5208242 baseEnd_5208242 := by
    simpa [prefixWord, tailWord_5208242, baseEnd_5208242] using wordTrace_append hprefix tailTrace_5208242
  have hstable : (prefixWord ++ tailWord_5208242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208242).length < 2 ^ (prefixWord ++ tailWord_5208242).sum := by decide
  have hdescent : baseEnd_5208242 < baseStart_5208242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208255 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 4]
def baseStart_5208255 : Nat := 118140960795 + 5208255 * 2 ^ 59
def prefixEnd_5208255 : Nat := 4983230072969 + 3 ^ 40 * 5208255 * 2
def baseEnd_5208255 : Nat := 2674338186182625412060177

theorem tailTrace_5208255 : CollatzResearch.WordTrace tailWord_5208255 prefixEnd_5208255 2674338186182625412060177 := by
  unfold tailWord_5208255
  simp only [CollatzResearch.WordTrace]
  refine ⟨189960665746389108982466219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126640443830926072654977479 189960665746389108982466219)
  ·
    refine ⟨284940998619583663473699329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189960665746389108982466219 284940998619583663473699329)
    ·
      refine ⟨213705748964687747605274497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284940998619583663473699329 213705748964687747605274497)
      ·
        refine ⟨160279311723515810703955873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213705748964687747605274497 160279311723515810703955873)
        ·
          refine ⟨120209483792636858027966905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160279311723515810703955873 120209483792636858027966905)
          ·
            refine ⟨90157112844477643520975179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120209483792636858027966905 90157112844477643520975179)
            ·
              refine ⟨135235669266716465281462769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90157112844477643520975179 135235669266716465281462769)
              ·
                refine ⟨101426751950037348961097077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135235669266716465281462769 101426751950037348961097077)
                ·
                  refine ⟨9508757995316001465102851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101426751950037348961097077 9508757995316001465102851)
                  ·
                    refine ⟨14263136992974002197654277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9508757995316001465102851 14263136992974002197654277)
                    ·
                      refine ⟨2674338186182625412060177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14263136992974002197654277 2674338186182625412060177)
                      ·
                        rfl

theorem cell23_5208255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_5208255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208255 prefixEnd_5208255 := by exact prefixLift 5208255
  have htrace : WordTrace (prefixWord ++ tailWord_5208255) baseStart_5208255 baseEnd_5208255 := by
    simpa [prefixWord, tailWord_5208255, baseEnd_5208255] using wordTrace_append hprefix tailTrace_5208255
  have hstable : (prefixWord ++ tailWord_5208255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208255).length < 2 ^ (prefixWord ++ tailWord_5208255).sum := by decide
  have hdescent : baseEnd_5208255 < baseStart_5208255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208289 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 5, 2, 2]
def baseStart_5208289 : Nat := 118140960795 + 5208289 * 2 ^ 59
def prefixEnd_5208289 : Nat := 4983230072969 + 3 ^ 40 * 5208289 * 2
def baseEnd_5208289 : Nat := 2674355644524878279035021

theorem tailTrace_5208289 : CollatzResearch.WordTrace tailWord_5208289 prefixEnd_5208289 2674355644524878279035021 := by
  unfold tailWord_5208289
  simp only [CollatzResearch.WordTrace]
  refine ⟨189961905828265932789203921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126641270552177288526135947 189961905828265932789203921)
  ·
    refine ⟨142471429371199449591902941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189961905828265932789203921 142471429371199449591902941)
    ·
      refine ⟨53426786014199793596963603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142471429371199449591902941 53426786014199793596963603)
      ·
        refine ⟨80140179021299690395445405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53426786014199793596963603 80140179021299690395445405)
        ·
          refine ⟨30052567132987383898292027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80140179021299690395445405 30052567132987383898292027)
          ·
            refine ⟨45078850699481075847438041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30052567132987383898292027 45078850699481075847438041)
            ·
              refine ⟨33809138024610806885578531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45078850699481075847438041 33809138024610806885578531)
              ·
                refine ⟨50713707036916210328367797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33809138024610806885578531 50713707036916210328367797)
                ·
                  refine ⟨4754410034710894718284481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50713707036916210328367797 4754410034710894718284481)
                  ·
                    refine ⟨3565807526033171038713361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4754410034710894718284481 3565807526033171038713361)
                    ·
                      refine ⟨2674355644524878279035021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3565807526033171038713361 2674355644524878279035021)
                      ·
                        rfl

theorem cell23_5208289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 2, 2].length) (baseStart_5208289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208289 prefixEnd_5208289 := by exact prefixLift 5208289
  have htrace : WordTrace (prefixWord ++ tailWord_5208289) baseStart_5208289 baseEnd_5208289 := by
    simpa [prefixWord, tailWord_5208289, baseEnd_5208289] using wordTrace_append hprefix tailTrace_5208289
  have hstable : (prefixWord ++ tailWord_5208289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208289).length < 2 ^ (prefixWord ++ tailWord_5208289).sum := by decide
  have hdescent : baseEnd_5208289 < baseStart_5208289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208306 : List Nat := [3, 2, 1, 3, 2, 2, 3, 1, 1, 1, 4]
def baseStart_5208306 : Nat := 118140960795 + 5208306 * 2 ^ 59
def prefixEnd_5208306 : Nat := 4983230072969 + 3 ^ 40 * 5208306 * 2
def baseEnd_5208306 : Nat := 2674364373696004712522443

theorem tailTrace_5208306 : CollatzResearch.WordTrace tailWord_5208306 prefixEnd_5208306 2674364373696004712522443 := by
  unfold tailWord_5208306
  simp only [CollatzResearch.WordTrace]
  refine ⟨47490631467301086173143193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126641683912802896461715181 47490631467301086173143193)
  ·
    refine ⟨35617973600475814629857395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47490631467301086173143193 35617973600475814629857395)
    ·
      refine ⟨53426960400713721944786093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35617973600475814629857395 53426960400713721944786093)
      ·
        refine ⟨20035110150267645729294785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53426960400713721944786093 20035110150267645729294785)
        ·
          refine ⟨15026332612700734296971089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20035110150267645729294785 15026332612700734296971089)
          ·
            refine ⟨11269749459525550722728317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15026332612700734296971089 11269749459525550722728317)
            ·
              refine ⟨4226156047322081521023119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11269749459525550722728317 4226156047322081521023119)
              ·
                refine ⟨6339234070983122281534679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4226156047322081521023119 6339234070983122281534679)
                ·
                  refine ⟨9508851106474683422302019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6339234070983122281534679 9508851106474683422302019)
                  ·
                    refine ⟨14263276659712025133453029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9508851106474683422302019 14263276659712025133453029)
                    ·
                      refine ⟨2674364373696004712522443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14263276659712025133453029 2674364373696004712522443)
                      ·
                        rfl

theorem cell23_5208306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_5208306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208306 prefixEnd_5208306 := by exact prefixLift 5208306
  have htrace : WordTrace (prefixWord ++ tailWord_5208306) baseStart_5208306 baseEnd_5208306 := by
    simpa [prefixWord, tailWord_5208306, baseEnd_5208306] using wordTrace_append hprefix tailTrace_5208306
  have hstable : (prefixWord ++ tailWord_5208306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208306).length < 2 ^ (prefixWord ++ tailWord_5208306).sum := by decide
  have hdescent : baseEnd_5208306 < baseStart_5208306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208355 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 1, 8]
def baseStart_5208355 : Nat := 118140960795 + 5208355 * 2 ^ 59
def prefixEnd_5208355 : Nat := 4983230072969 + 3 ^ 40 * 5208355 * 2
def baseEnd_5208355 : Nat := 891463178082691673603239

theorem tailTrace_5208355 : CollatzResearch.WordTrace tailWord_5208355 prefixEnd_5208355 891463178082691673603239 := by
  unfold tailWord_5208355
  simp only [CollatzResearch.WordTrace]
  refine ⟨189964313046026826061106519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126642875364017884040737679 189964313046026826061106519)
  ·
    refine ⟨284946469569040239091659779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189964313046026826061106519 284946469569040239091659779)
    ·
      refine ⟨427419704353560358637489669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284946469569040239091659779 427419704353560358637489669)
      ·
        refine ⟨80141194566292567244529313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 427419704353560358637489669 80141194566292567244529313)
        ·
          refine ⟨60105895924719425433396985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80141194566292567244529313 60105895924719425433396985)
          ·
            refine ⟨45079421943539569075047739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60105895924719425433396985 45079421943539569075047739)
            ·
              refine ⟨67619132915309353612571609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45079421943539569075047739 67619132915309353612571609)
              ·
                refine ⟨50714349686482015209428707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67619132915309353612571609 50714349686482015209428707)
                ·
                  refine ⟨76071524529723022814143061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50714349686482015209428707 76071524529723022814143061)
                  ·
                    refine ⟨891463178082691673603239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76071524529723022814143061 891463178082691673603239)
                    ·
                      rfl

theorem cell23_5208355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 8].length) (baseStart_5208355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208355 prefixEnd_5208355 := by exact prefixLift 5208355
  have htrace : WordTrace (prefixWord ++ tailWord_5208355) baseStart_5208355 baseEnd_5208355 := by
    simpa [prefixWord, tailWord_5208355, baseEnd_5208355] using wordTrace_append hprefix tailTrace_5208355
  have hstable : (prefixWord ++ tailWord_5208355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208355).length < 2 ^ (prefixWord ++ tailWord_5208355).sum := by decide
  have hdescent : baseEnd_5208355 < baseStart_5208355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208360 : List Nat := [2, 1, 5, 1, 4, 1, 2, 1, 1, 2, 3]
def baseStart_5208360 : Nat := 118140960795 + 5208360 * 2 ^ 59
def prefixEnd_5208360 : Nat := 4983230072969 + 3 ^ 40 * 5208360 * 2
def baseEnd_5208360 : Nat := 2674392101651347501247195

theorem tailTrace_5208360 : CollatzResearch.WordTrace tailWord_5208360 prefixEnd_5208360 2674392101651347501247195 := by
  unfold tailWord_5208360
  simp only [CollatzResearch.WordTrace]
  refine ⟨94982247705504355957519267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126642996940672474610025689 94982247705504355957519267)
  ·
    refine ⟨142473371558256533936278901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94982247705504355957519267 142473371558256533936278901)
    ·
      refine ⟨13356878583586550056526147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142473371558256533936278901 13356878583586550056526147)
      ·
        refine ⟨20035317875379825084789221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13356878583586550056526147 20035317875379825084789221)
        ·
          refine ⟨3756622101633717203397979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20035317875379825084789221 3756622101633717203397979)
          ·
            refine ⟨5634933152450575805096969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3756622101633717203397979 5634933152450575805096969)
            ·
              refine ⟨4226199864337931853822727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5634933152450575805096969 4226199864337931853822727)
              ·
                refine ⟨6339299796506897780734091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4226199864337931853822727 6339299796506897780734091)
                ·
                  refine ⟨9508949694760346671101137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6339299796506897780734091 9508949694760346671101137)
                  ·
                    refine ⟨7131712271070260003325853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9508949694760346671101137 7131712271070260003325853)
                    ·
                      refine ⟨2674392101651347501247195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7131712271070260003325853 2674392101651347501247195)
                      ·
                        rfl

theorem cell23_5208360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_5208360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208360 prefixEnd_5208360 := by exact prefixLift 5208360
  have htrace : WordTrace (prefixWord ++ tailWord_5208360) baseStart_5208360 baseEnd_5208360 := by
    simpa [prefixWord, tailWord_5208360, baseEnd_5208360] using wordTrace_append hprefix tailTrace_5208360
  have hstable : (prefixWord ++ tailWord_5208360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208360).length < 2 ^ (prefixWord ++ tailWord_5208360).sum := by decide
  have hdescent : baseEnd_5208360 < baseStart_5208360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208392 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 2, 2, 4]
def baseStart_5208392 : Nat := 118140960795 + 5208392 * 2 ^ 59
def prefixEnd_5208392 : Nat := 4983230072969 + 3 ^ 40 * 5208392 * 2
def baseEnd_5208392 : Nat := 2674408533032291376047047

theorem tailTrace_5208392 : CollatzResearch.WordTrace tailWord_5208392 prefixEnd_5208392 2674408533032291376047047 := by
  unfold tailWord_5208392
  simp only [CollatzResearch.WordTrace]
  refine ⟨94982831273446390690101715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126643775031261854253468953 94982831273446390690101715)
  ·
    refine ⟨142474246910169586035152573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94982831273446390690101715 142474246910169586035152573)
    ·
      refine ⟨53427842591313594763182215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142474246910169586035152573 53427842591313594763182215)
      ·
        refine ⟨80141763886970392144773323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53427842591313594763182215 80141763886970392144773323)
        ·
          refine ⟨120212645830455588217159985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80141763886970392144773323 120212645830455588217159985)
          ·
            refine ⟨90159484372841691162869989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120212645830455588217159985 90159484372841691162869989)
            ·
              refine ⟨16904903319907817093038123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90159484372841691162869989 16904903319907817093038123)
              ·
                refine ⟨25357354979861725639557185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16904903319907817093038123 25357354979861725639557185)
                ·
                  refine ⟨19018016234896294229667889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25357354979861725639557185 19018016234896294229667889)
                  ·
                    refine ⟨14263512176172220672250917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19018016234896294229667889 14263512176172220672250917)
                    ·
                      refine ⟨2674408533032291376047047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14263512176172220672250917 2674408533032291376047047)
                      ·
                        rfl

theorem cell23_5208392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_5208392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208392 prefixEnd_5208392 := by exact prefixLift 5208392
  have htrace : WordTrace (prefixWord ++ tailWord_5208392) baseStart_5208392 baseEnd_5208392 := by
    simpa [prefixWord, tailWord_5208392, baseEnd_5208392] using wordTrace_append hprefix tailTrace_5208392
  have hstable : (prefixWord ++ tailWord_5208392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208392).length < 2 ^ (prefixWord ++ tailWord_5208392).sum := by decide
  have hdescent : baseEnd_5208392 < baseStart_5208392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208402 : List Nat := [3, 2, 2, 1, 1, 1, 4, 2, 7]
def baseStart_5208402 : Nat := 118140960795 + 5208402 * 2 ^ 59
def prefixEnd_5208402 : Nat := 4983230072969 + 3 ^ 40 * 5208402 * 2
def baseEnd_5208402 : Nat := 297157074204315148546889

theorem tailTrace_5208402 : CollatzResearch.WordTrace tailWord_5208402 prefixEnd_5208402 297157074204315148546889 := by
  unfold tailWord_5208402
  simp only [CollatzResearch.WordTrace]
  refine ⟨47491506819214138272016865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126644018184571035392044973 47491506819214138272016865)
  ·
    refine ⟨35618630114410603704012649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47491506819214138272016865 35618630114410603704012649)
    ·
      refine ⟨26713972585807952778009487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35618630114410603704012649 26713972585807952778009487)
      ·
        refine ⟨40070958878711929167014231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26713972585807952778009487 40070958878711929167014231)
        ·
          refine ⟨60106438318067893750521347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40070958878711929167014231 60106438318067893750521347)
          ·
            refine ⟨90159657477101840625782021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60106438318067893750521347 90159657477101840625782021)
            ·
              refine ⟨16904935776956595117334129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90159657477101840625782021 16904935776956595117334129)
              ·
                refine ⟨12678701832717446338000597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16904935776956595117334129 12678701832717446338000597)
                ·
                  refine ⟨297157074204315148546889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12678701832717446338000597 297157074204315148546889)
                  ·
                    rfl

theorem cell23_5208402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_5208402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208402 prefixEnd_5208402 := by exact prefixLift 5208402
  have htrace : WordTrace (prefixWord ++ tailWord_5208402) baseStart_5208402 baseEnd_5208402 := by
    simpa [prefixWord, tailWord_5208402, baseEnd_5208402] using wordTrace_append hprefix tailTrace_5208402
  have hstable : (prefixWord ++ tailWord_5208402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208402).length < 2 ^ (prefixWord ++ tailWord_5208402).sum := by decide
  have hdescent : baseEnd_5208402 < baseStart_5208402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208432 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 4, 5]
def baseStart_5208432 : Nat := 118140960795 + 5208432 * 2 ^ 59
def prefixEnd_5208432 : Nat := 4983230072969 + 3 ^ 40 * 5208432 * 2
def baseEnd_5208432 : Nat := 891476357419490406515621

theorem tailTrace_5208432 : CollatzResearch.WordTrace tailWord_5208432 prefixEnd_5208432 891476357419490406515621 := by
  unfold tailWord_5208432
  simp only [CollatzResearch.WordTrace]
  refine ⟨94983560733373934105829775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126644747644498578807773033 94983560733373934105829775)
  ·
    refine ⟨142475341100060901158744663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94983560733373934105829775 142475341100060901158744663)
    ·
      refine ⟨213713011650091351738116995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142475341100060901158744663 213713011650091351738116995)
      ·
        refine ⟨320569517475137027607175493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213713011650091351738116995 320569517475137027607175493)
        ·
          refine ⟨60106784526588192676345405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 320569517475137027607175493 60106784526588192676345405)
          ·
            refine ⟨22540044197470572253629527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60106784526588192676345405 22540044197470572253629527)
            ·
              refine ⟨33810066296205858380444291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22540044197470572253629527 33810066296205858380444291)
              ·
                refine ⟨50715099444308787570666437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33810066296205858380444291 50715099444308787570666437)
                ·
                  refine ⟨9509081145807897669499957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50715099444308787570666437 9509081145807897669499957)
                  ·
                    refine ⟨891476357419490406515621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9509081145807897669499957 891476357419490406515621)
                    ·
                      rfl

theorem cell23_5208432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 4, 5].length) (baseStart_5208432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208432 prefixEnd_5208432 := by exact prefixLift 5208432
  have htrace : WordTrace (prefixWord ++ tailWord_5208432) baseStart_5208432 baseEnd_5208432 := by
    simpa [prefixWord, tailWord_5208432, baseEnd_5208432] using wordTrace_append hprefix tailTrace_5208432
  have hstable : (prefixWord ++ tailWord_5208432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208432).length < 2 ^ (prefixWord ++ tailWord_5208432).sum := by decide
  have hdescent : baseEnd_5208432 < baseStart_5208432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208469 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 4, 4, 2]
def baseStart_5208469 : Nat := 118140960795 + 5208469 * 2 ^ 59
def prefixEnd_5208469 : Nat := 4983230072969 + 3 ^ 40 * 5208469 * 2
def baseEnd_5208469 : Nat := 2674448071042687574784193

theorem tailTrace_5208469 : CollatzResearch.WordTrace tailWord_5208469 prefixEnd_5208469 2674448071042687574784193 := by
  unfold tailWord_5208469
  simp only [CollatzResearch.WordTrace]
  refine ⟨189968470967613823530756461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126645647311742549020504307 189968470967613823530756461)
  ·
    refine ⟨71238176612855183824033673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189968470967613823530756461 71238176612855183824033673)
    ·
      refine ⟨53428632459641387868025255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71238176612855183824033673 53428632459641387868025255)
      ·
        refine ⟨80142948689462081802037883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53428632459641387868025255 80142948689462081802037883)
        ·
          refine ⟨120214423034193122703056825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80142948689462081802037883 120214423034193122703056825)
          ·
            refine ⟨90160817275644842027292619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120214423034193122703056825 90160817275644842027292619)
            ·
              refine ⟨135241225913467263040938929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90160817275644842027292619 135241225913467263040938929)
              ·
                refine ⟨101430919435100447280704197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135241225913467263040938929 101430919435100447280704197)
                ·
                  refine ⟨19018297394081333865132037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101430919435100447280704197 19018297394081333865132037)
                  ·
                    refine ⟨3565930761390250099712257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19018297394081333865132037 3565930761390250099712257)
                    ·
                      refine ⟨2674448071042687574784193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3565930761390250099712257 2674448071042687574784193)
                      ·
                        rfl

theorem cell23_5208469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 4, 2].length) (baseStart_5208469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208469 prefixEnd_5208469 := by exact prefixLift 5208469
  have htrace : WordTrace (prefixWord ++ tailWord_5208469) baseStart_5208469 baseEnd_5208469 := by
    simpa [prefixWord, tailWord_5208469, baseEnd_5208469] using wordTrace_append hprefix tailTrace_5208469
  have hstable : (prefixWord ++ tailWord_5208469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208469).length < 2 ^ (prefixWord ++ tailWord_5208469).sum := by decide
  have hdescent : baseEnd_5208469 < baseStart_5208469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208509 : List Nat := [1, 4, 1, 2, 2, 2, 2, 3, 6]
def baseStart_5208509 : Nat := 118140960795 + 5208509 * 2 ^ 59
def prefixEnd_5208509 : Nat := 4983230072969 + 3 ^ 40 * 5208509 * 2
def baseEnd_5208509 : Nat := 297163178918763046476001

theorem tailTrace_5208509 : CollatzResearch.WordTrace tailWord_5208509 prefixEnd_5208509 297163178918763046476001 := by
  unfold tailWord_5208509
  simp only [CollatzResearch.WordTrace]
  refine ⟨189969929887468910362212581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126646619924979273574808387 189969929887468910362212581)
  ·
    refine ⟨35619361853900420692914859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189969929887468910362212581 35619361853900420692914859)
    ·
      refine ⟨53429042780850631039372289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35619361853900420692914859 53429042780850631039372289)
      ·
        refine ⟨40071782085637973279529217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53429042780850631039372289 40071782085637973279529217)
        ·
          refine ⟨30053836564228479959646913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40071782085637973279529217 30053836564228479959646913)
          ·
            refine ⟨22540377423171359969735185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30053836564228479959646913 22540377423171359969735185)
            ·
              refine ⟨16905283067378519977301389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22540377423171359969735185 16905283067378519977301389)
              ·
                refine ⟨6339481150266944991488021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16905283067378519977301389 6339481150266944991488021)
                ·
                  refine ⟨297163178918763046476001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6339481150266944991488021 297163178918763046476001)
                  ·
                    rfl

theorem cell23_5208509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_5208509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208509 prefixEnd_5208509 := by exact prefixLift 5208509
  have htrace : WordTrace (prefixWord ++ tailWord_5208509) baseStart_5208509 baseEnd_5208509 := by
    simpa [prefixWord, tailWord_5208509, baseEnd_5208509] using wordTrace_append hprefix tailTrace_5208509
  have hstable : (prefixWord ++ tailWord_5208509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208509).length < 2 ^ (prefixWord ++ tailWord_5208509).sum := by decide
  have hdescent : baseEnd_5208509 < baseStart_5208509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208569 : List Nat := [1, 2, 1, 3, 1, 2, 5, 1, 1, 6]
def baseStart_5208569 : Nat := 118140960795 + 5208569 * 2 ^ 59
def prefixEnd_5208569 : Nat := 4983230072969 + 3 ^ 40 * 5208569 * 2
def baseEnd_5208569 : Nat := 891499806369379061177911

theorem tailTrace_5208569 : CollatzResearch.WordTrace tailWord_5208569 prefixEnd_5208569 891499806369379061177911 := by
  unfold tailWord_5208569
  simp only [CollatzResearch.WordTrace]
  refine ⟨189972118267251540609396761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126648078844834360406264507 189972118267251540609396761)
  ·
    refine ⟨142479088700438655457047571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189972118267251540609396761 142479088700438655457047571)
    ·
      refine ⟨213718633050657983185571357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142479088700438655457047571 213718633050657983185571357)
      ·
        refine ⟨80144487393996743694589259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213718633050657983185571357 80144487393996743694589259)
        ·
          refine ⟨120216731090995115541883889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80144487393996743694589259 120216731090995115541883889)
          ·
            refine ⟨90162548318246336656412917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120216731090995115541883889 90162548318246336656412917)
            ·
              refine ⟨8452738904835594061538711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90162548318246336656412917 8452738904835594061538711)
              ·
                refine ⟨12679108357253391092308067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8452738904835594061538711 12679108357253391092308067)
                ·
                  refine ⟨19018662535880086638462101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12679108357253391092308067 19018662535880086638462101)
                  ·
                    refine ⟨891499806369379061177911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19018662535880086638462101 891499806369379061177911)
                    ·
                      rfl

theorem cell23_5208569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 6].length) (baseStart_5208569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208569 prefixEnd_5208569 := by exact prefixLift 5208569
  have htrace : WordTrace (prefixWord ++ tailWord_5208569) baseStart_5208569 baseEnd_5208569 := by
    simpa [prefixWord, tailWord_5208569, baseEnd_5208569] using wordTrace_append hprefix tailTrace_5208569
  have hstable : (prefixWord ++ tailWord_5208569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208569).length < 2 ^ (prefixWord ++ tailWord_5208569).sum := by decide
  have hdescent : baseEnd_5208569 < baseStart_5208569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208592 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 7]
def baseStart_5208592 : Nat := 118140960795 + 5208592 * 2 ^ 59
def prefixEnd_5208592 : Nat := 4983230072969 + 3 ^ 40 * 5208592 * 2
def baseEnd_5208592 : Nat := 2674511229163190593546127

theorem tailTrace_5208592 : CollatzResearch.WordTrace tailWord_5208592 prefixEnd_5208592 2674511229163190593546127 := by
  unfold tailWord_5208592
  simp only [CollatzResearch.WordTrace]
  refine ⟨94986478573084107768742015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126648638097445477024989353 94986478573084107768742015)
  ·
    refine ⟨142479717859626161653113023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94986478573084107768742015 142479717859626161653113023)
    ·
      refine ⟨213719576789439242479669535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142479717859626161653113023 213719576789439242479669535)
      ·
        refine ⟨320579365184158863719504303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213719576789439242479669535 320579365184158863719504303)
        ·
          refine ⟨480869047776238295579256455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320579365184158863719504303 480869047776238295579256455)
          ·
            refine ⟨721303571664357443368884683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480869047776238295579256455 721303571664357443368884683)
            ·
              refine ⟨1081955357496536165053327025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 721303571664357443368884683 1081955357496536165053327025)
              ·
                refine ⟨811466518122402123789995269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081955357496536165053327025 811466518122402123789995269)
                ·
                  refine ⟨152149972147950398210624113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 811466518122402123789995269 152149972147950398210624113)
                  ·
                    refine ⟨114112479110962798657968085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 152149972147950398210624113 114112479110962798657968085)
                    ·
                      refine ⟨2674511229163190593546127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114112479110962798657968085 2674511229163190593546127)
                      ·
                        rfl

theorem cell23_5208592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_5208592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208592 prefixEnd_5208592 := by exact prefixLift 5208592
  have htrace : WordTrace (prefixWord ++ tailWord_5208592) baseStart_5208592 baseEnd_5208592 := by
    simpa [prefixWord, tailWord_5208592, baseEnd_5208592] using wordTrace_append hprefix tailTrace_5208592
  have hstable : (prefixWord ++ tailWord_5208592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208592).length < 2 ^ (prefixWord ++ tailWord_5208592).sum := by decide
  have hdescent : baseEnd_5208592 < baseStart_5208592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208616 : List Nat := [2, 1, 5, 2, 1, 2, 2, 8]
def baseStart_5208616 : Nat := 118140960795 + 5208616 * 2 ^ 59
def prefixEnd_5208616 : Nat := 4983230072969 + 3 ^ 40 * 5208616 * 2
def baseEnd_5208616 : Nat := 99056427877736981468371

theorem tailTrace_5208616 : CollatzResearch.WordTrace tailWord_5208616 prefixEnd_5208616 99056427877736981468371 := by
  unfold tailWord_5208616
  simp only [CollatzResearch.WordTrace]
  refine ⟨94986916249040633818178851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126649221665387511757571801 94986916249040633818178851)
  ·
    refine ⟨142480374373560950727268277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94986916249040633818178851 142480374373560950727268277)
    ·
      refine ⟨13357535097521339130681401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142480374373560950727268277 13357535097521339130681401)
      ·
        refine ⟨10018151323141004348011051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13357535097521339130681401 10018151323141004348011051)
        ·
          refine ⟨15027226984711506522016577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10018151323141004348011051 15027226984711506522016577)
          ·
            refine ⟨11270420238533629891512433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15027226984711506522016577 11270420238533629891512433)
            ·
              refine ⟨8452815178900222418634325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11270420238533629891512433 8452815178900222418634325)
              ·
                refine ⟨99056427877736981468371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8452815178900222418634325 99056427877736981468371)
                ·
                  rfl

theorem cell23_5208616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 8].length) (baseStart_5208616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208616 prefixEnd_5208616 := by exact prefixLift 5208616
  have htrace : WordTrace (prefixWord ++ tailWord_5208616) baseStart_5208616 baseEnd_5208616 := by
    simpa [prefixWord, tailWord_5208616, baseEnd_5208616] using wordTrace_append hprefix tailTrace_5208616
  have hstable : (prefixWord ++ tailWord_5208616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208616).length < 2 ^ (prefixWord ++ tailWord_5208616).sum := by decide
  have hdescent : baseEnd_5208616 < baseStart_5208616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208630 : List Nat := [5, 1, 2, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_5208630 : Nat := 118140960795 + 5208630 * 2 ^ 59
def prefixEnd_5208630 : Nat := 4983230072969 + 3 ^ 40 * 5208630 * 2
def baseEnd_5208630 : Nat := 2674530741428061444870953

theorem tailTrace_5208630 : CollatzResearch.WordTrace tailWord_5208630 prefixEnd_5208630 2674530741428061444870953 := by
  unfold tailWord_5208630
  simp only [CollatzResearch.WordTrace]
  refine ⟨11873396445001909251710459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126649562080020365351578229 11873396445001909251710459)
  ·
    refine ⟨17810094667502863877565689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11873396445001909251710459 17810094667502863877565689)
    ·
      refine ⟨13357571000627147908174267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17810094667502863877565689 13357571000627147908174267)
      ·
        refine ⟨20036356500940721862261401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13357571000627147908174267 20036356500940721862261401)
        ·
          refine ⟨15027267375705541396696051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20036356500940721862261401 15027267375705541396696051)
          ·
            refine ⟨22540901063558312095044077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15027267375705541396696051 22540901063558312095044077)
            ·
              refine ⟨8452837898834367035641529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22540901063558312095044077 8452837898834367035641529)
              ·
                refine ⟨6339628424125775276731147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8452837898834367035641529 6339628424125775276731147)
                ·
                  refine ⟨9509442636188662915096721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6339628424125775276731147 9509442636188662915096721)
                  ·
                    refine ⟨7132081977141497186322541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9509442636188662915096721 7132081977141497186322541)
                    ·
                      refine ⟨2674530741428061444870953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7132081977141497186322541 2674530741428061444870953)
                      ·
                        rfl

theorem cell23_5208630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_5208630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208630 prefixEnd_5208630 := by exact prefixLift 5208630
  have htrace : WordTrace (prefixWord ++ tailWord_5208630) baseStart_5208630 baseEnd_5208630 := by
    simpa [prefixWord, tailWord_5208630, baseEnd_5208630] using wordTrace_append hprefix tailTrace_5208630
  have hstable : (prefixWord ++ tailWord_5208630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208630).length < 2 ^ (prefixWord ++ tailWord_5208630).sum := by decide
  have hdescent : baseEnd_5208630 < baseStart_5208630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208644 : List Nat := [2, 3, 5, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_5208644 : Nat := 118140960795 + 5208644 * 2 ^ 59
def prefixEnd_5208644 : Nat := 4983230072969 + 3 ^ 40 * 5208644 * 2
def baseEnd_5208644 : Nat := 2674537930157224390095889

theorem tailTrace_5208644 : CollatzResearch.WordTrace tailWord_5208644 prefixEnd_5208644 2674537930157224390095889 := by
  unfold tailWord_5208644
  simp only [CollatzResearch.WordTrace]
  refine ⟨94987426870989914209188493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126649902494653218945584657 94987426870989914209188493)
  ·
    refine ⟨35620285076621217828445685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94987426870989914209188493 35620285076621217828445685)
    ·
      refine ⟨3339401725933239171416783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35620285076621217828445685 3339401725933239171416783)
      ·
        refine ⟨5009102588899858757125175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3339401725933239171416783 5009102588899858757125175)
        ·
          refine ⟨7513653883349788135687763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5009102588899858757125175 7513653883349788135687763)
          ·
            refine ⟨11270480825024682203531645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7513653883349788135687763 11270480825024682203531645)
            ·
              refine ⟨4226430309384255826324367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11270480825024682203531645 4226430309384255826324367)
              ·
                refine ⟨6339645464076383739486551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4226430309384255826324367 6339645464076383739486551)
                ·
                  refine ⟨9509468196114575609229827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6339645464076383739486551 9509468196114575609229827)
                  ·
                    refine ⟨14264202294171863413844741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9509468196114575609229827 14264202294171863413844741)
                    ·
                      refine ⟨2674537930157224390095889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14264202294171863413844741 2674537930157224390095889)
                      ·
                        rfl

theorem cell23_5208644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_5208644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208644 prefixEnd_5208644 := by exact prefixLift 5208644
  have htrace : WordTrace (prefixWord ++ tailWord_5208644) baseStart_5208644 baseEnd_5208644 := by
    simpa [prefixWord, tailWord_5208644, baseEnd_5208644] using wordTrace_append hprefix tailTrace_5208644
  have hstable : (prefixWord ++ tailWord_5208644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208644).length < 2 ^ (prefixWord ++ tailWord_5208644).sum := by decide
  have hdescent : baseEnd_5208644 < baseStart_5208644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208660 : List Nat := [2, 4, 1, 1, 1, 4, 2, 2, 2, 1, 3]
def baseStart_5208660 : Nat := 118140960795 + 5208660 * 2 ^ 59
def prefixEnd_5208660 : Nat := 4983230072969 + 3 ^ 40 * 5208660 * 2
def baseEnd_5208660 : Nat := 2674546145847696327495815

theorem tailTrace_5208660 : CollatzResearch.WordTrace tailWord_5208660 prefixEnd_5208660 2674546145847696327495815 := by
  unfold tailWord_5208660
  simp only [CollatzResearch.WordTrace]
  refine ⟨94987718654960931575479717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126650291539947908767306289 94987718654960931575479717)
  ·
    refine ⟨17810197247805174670402447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94987718654960931575479717 17810197247805174670402447)
    ·
      refine ⟨26715295871707762005603671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17810197247805174670402447 26715295871707762005603671)
      ·
        refine ⟨40072943807561643008405507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26715295871707762005603671 40072943807561643008405507)
        ·
          refine ⟨60109415711342464512608261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40072943807561643008405507 60109415711342464512608261)
          ·
            refine ⟨11270515445876712096114049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60109415711342464512608261 11270515445876712096114049)
            ·
              refine ⟨8452886584407534072085537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11270515445876712096114049 8452886584407534072085537)
              ·
                refine ⟨6339664938305650554064153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8452886584407534072085537 6339664938305650554064153)
                ·
                  refine ⟨4754748703729237915548115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6339664938305650554064153 4754748703729237915548115)
                  ·
                    refine ⟨7132123055593856873322173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4754748703729237915548115 7132123055593856873322173)
                    ·
                      refine ⟨2674546145847696327495815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7132123055593856873322173 2674546145847696327495815)
                      ·
                        rfl

theorem cell23_5208660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_5208660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208660 prefixEnd_5208660 := by exact prefixLift 5208660
  have htrace : WordTrace (prefixWord ++ tailWord_5208660) baseStart_5208660 baseEnd_5208660 := by
    simpa [prefixWord, tailWord_5208660, baseEnd_5208660] using wordTrace_append hprefix tailTrace_5208660
  have hstable : (prefixWord ++ tailWord_5208660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208660).length < 2 ^ (prefixWord ++ tailWord_5208660).sum := by decide
  have hdescent : baseEnd_5208660 < baseStart_5208660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208729 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 1, 1, 7]
def baseStart_5208729 : Nat := 118140960795 + 5208729 * 2 ^ 59
def prefixEnd_5208729 : Nat := 4983230072969 + 3 ^ 40 * 5208729 * 2
def baseEnd_5208729 : Nat := 2674581576012856557532997

theorem tailTrace_5208729 : CollatzResearch.WordTrace tailWord_5208729 prefixEnd_5208729 2674581576012856557532997 := by
  unfold tailWord_5208729
  simp only [CollatzResearch.WordTrace]
  refine ⟨189977953946671887935221241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126651969297781258623480827 189977953946671887935221241)
  ·
    refine ⟨142483465460003915951415931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189977953946671887935221241 142483465460003915951415931)
    ·
      refine ⟨213725198190005873927123897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142483465460003915951415931 213725198190005873927123897)
      ·
        refine ⟨160293898642504405445342923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213725198190005873927123897 160293898642504405445342923)
        ·
          refine ⟨240440847963756608168014385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160293898642504405445342923 240440847963756608168014385)
          ·
            refine ⟨180330635972817456126010789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240440847963756608168014385 180330635972817456126010789)
            ·
              refine ⟨33811994244903273023627023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 180330635972817456126010789 33811994244903273023627023)
              ·
                refine ⟨50717991367354909535440535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33811994244903273023627023 50717991367354909535440535)
                ·
                  refine ⟨76076987051032364303160803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50717991367354909535440535 76076987051032364303160803)
                  ·
                    refine ⟨114115480576548546454741205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76076987051032364303160803 114115480576548546454741205)
                    ·
                      refine ⟨2674581576012856557532997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114115480576548546454741205 2674581576012856557532997)
                      ·
                        rfl

theorem cell23_5208729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_5208729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208729 prefixEnd_5208729 := by exact prefixLift 5208729
  have htrace : WordTrace (prefixWord ++ tailWord_5208729) baseStart_5208729 baseEnd_5208729 := by
    simpa [prefixWord, tailWord_5208729, baseEnd_5208729] using wordTrace_append hprefix tailTrace_5208729
  have hstable : (prefixWord ++ tailWord_5208729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208729).length < 2 ^ (prefixWord ++ tailWord_5208729).sum := by decide
  have hdescent : baseEnd_5208729 < baseStart_5208729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208734 : List Nat := [4, 3, 1, 1, 1, 1, 5, 1, 2, 2, 2]
def baseStart_5208734 : Nat := 118140960795 + 5208734 * 2 ^ 59
def prefixEnd_5208734 : Nat := 4983230072969 + 3 ^ 40 * 5208734 * 2
def baseEnd_5208734 : Nat := 2674584143416129037970475

theorem tailTrace_5208734 : CollatzResearch.WordTrace tailWord_5208734 prefixEnd_5208734 2674584143416129037970475 := by
  unfold tailWord_5208734
  simp only [CollatzResearch.WordTrace]
  refine ⟨23747267038956721723644157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126652090874435849192768837 23747267038956721723644157)
  ·
    refine ⟨8905225139608770646366559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23747267038956721723644157 8905225139608770646366559)
    ·
      refine ⟨13357837709413155969549839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8905225139608770646366559 13357837709413155969549839)
      ·
        refine ⟨20036756564119733954324759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13357837709413155969549839 20036756564119733954324759)
        ·
          refine ⟨30055134846179600931487139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20036756564119733954324759 30055134846179600931487139)
          ·
            refine ⟨45082702269269401397230709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30055134846179600931487139 45082702269269401397230709)
            ·
              refine ⟨4226503337744006380990379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45082702269269401397230709 4226503337744006380990379)
              ·
                refine ⟨6339755006616009571485569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4226503337744006380990379 6339755006616009571485569)
                ·
                  refine ⟨4754816254962007178614177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6339755006616009571485569 4754816254962007178614177)
                  ·
                    refine ⟨3566112191221505383960633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4754816254962007178614177 3566112191221505383960633)
                    ·
                      refine ⟨2674584143416129037970475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3566112191221505383960633 2674584143416129037970475)
                      ·
                        rfl

theorem cell23_5208734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_5208734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208734 prefixEnd_5208734 := by exact prefixLift 5208734
  have htrace : WordTrace (prefixWord ++ tailWord_5208734) baseStart_5208734 baseEnd_5208734 := by
    simpa [prefixWord, tailWord_5208734, baseEnd_5208734] using wordTrace_append hprefix tailTrace_5208734
  have hstable : (prefixWord ++ tailWord_5208734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208734).length < 2 ^ (prefixWord ++ tailWord_5208734).sum := by decide
  have hdescent : baseEnd_5208734 < baseStart_5208734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208774 : List Nat := [6, 1, 2, 1, 3, 1, 1, 1, 7]
def baseStart_5208774 : Nat := 118140960795 + 5208774 * 2 ^ 59
def prefixEnd_5208774 : Nat := 4983230072969 + 3 ^ 40 * 5208774 * 2
def baseEnd_5208774 : Nat := 297178298071367653496699

theorem tailTrace_5208774 : CollatzResearch.WordTrace tailWord_5208774 prefixEnd_5208774 297178298071367653496699 := by
  unfold tailWord_5208774
  simp only [CollatzResearch.WordTrace]
  refine ⟨5936862350984651894394043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 126653063487672573747072917 5936862350984651894394043)
  ·
    refine ⟨8905293526476977841591065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5936862350984651894394043 8905293526476977841591065)
    ·
      refine ⟨6678970144857733381193299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8905293526476977841591065 6678970144857733381193299)
      ·
        refine ⟨10018455217286600071789949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6678970144857733381193299 10018455217286600071789949)
        ·
          refine ⟨3756920706482475026921231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10018455217286600071789949 3756920706482475026921231)
          ·
            refine ⟨5635381059723712540381847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3756920706482475026921231 5635381059723712540381847)
            ·
              refine ⟨8453071589585568810572771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5635381059723712540381847 8453071589585568810572771)
              ·
                refine ⟨12679607384378353215859157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8453071589585568810572771 12679607384378353215859157)
                ·
                  refine ⟨297178298071367653496699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12679607384378353215859157 297178298071367653496699)
                  ·
                    rfl

theorem cell23_5208774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_5208774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208774 prefixEnd_5208774 := by exact prefixLift 5208774
  have htrace : WordTrace (prefixWord ++ tailWord_5208774) baseStart_5208774 baseEnd_5208774 := by
    simpa [prefixWord, tailWord_5208774, baseEnd_5208774] using wordTrace_append hprefix tailTrace_5208774
  have hstable : (prefixWord ++ tailWord_5208774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208774).length < 2 ^ (prefixWord ++ tailWord_5208774).sum := by decide
  have hdescent : baseEnd_5208774 < baseStart_5208774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208830 : List Nat := [4, 2, 2, 1, 2, 2, 2, 2, 6]
def baseStart_5208830 : Nat := 118140960795 + 5208830 * 2 ^ 59
def prefixEnd_5208830 : Nat := 4983230072969 + 3 ^ 40 * 5208830 * 2
def baseEnd_5208830 : Nat := 297181493062106740263337

theorem tailTrace_5208830 : CollatzResearch.WordTrace tailWord_5208830 prefixEnd_5208830 297181493062106740263337 := by
  unfold tailWord_5208830
  simp only [CollatzResearch.WordTrace]
  refine ⟨23747704714913247773080993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126654425146203988123098629 23747704714913247773080993)
  ·
    refine ⟨17810778536184935829810745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23747704714913247773080993 17810778536184935829810745)
    ·
      refine ⟨13358083902138701872358059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17810778536184935829810745 13358083902138701872358059)
      ·
        refine ⟨20037125853208052808537089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13358083902138701872358059 20037125853208052808537089)
        ·
          refine ⟨15027844389906039606402817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20037125853208052808537089 15027844389906039606402817)
          ·
            refine ⟨11270883292429529704802113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15027844389906039606402817 11270883292429529704802113)
            ·
              refine ⟨8453162469322147278601585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11270883292429529704802113 8453162469322147278601585)
              ·
                refine ⟨6339871851991610458951189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8453162469322147278601585 6339871851991610458951189)
                ·
                  refine ⟨297181493062106740263337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6339871851991610458951189 297181493062106740263337)
                  ·
                    rfl

theorem cell23_5208830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_5208830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208830 prefixEnd_5208830 := by exact prefixLift 5208830
  have htrace : WordTrace (prefixWord ++ tailWord_5208830) baseStart_5208830 baseEnd_5208830 := by
    simpa [prefixWord, tailWord_5208830, baseEnd_5208830] using wordTrace_append hprefix tailTrace_5208830
  have hstable : (prefixWord ++ tailWord_5208830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208830).length < 2 ^ (prefixWord ++ tailWord_5208830).sum := by decide
  have hdescent : baseEnd_5208830 < baseStart_5208830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208833 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 3, 5, 2]
def baseStart_5208833 : Nat := 118140960795 + 5208833 * 2 ^ 59
def prefixEnd_5208833 : Nat := 4983230072969 + 3 ^ 40 * 5208833 * 2
def baseEnd_5208833 : Nat := 2674634978000924150632519

theorem tailTrace_5208833 : CollatzResearch.WordTrace tailWord_5208833 prefixEnd_5208833 2674634978000924150632519 := by
  unfold tailWord_5208833
  simp only [CollatzResearch.WordTrace]
  refine ⟨189981747138295113697007153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126654498092196742464671435 189981747138295113697007153)
  ·
    refine ⟨142486310353721335272755365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189981747138295113697007153 142486310353721335272755365)
    ·
      refine ⟨26716183191322750363641631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142486310353721335272755365 26716183191322750363641631)
      ·
        refine ⟨40074274786984125545462447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26716183191322750363641631 40074274786984125545462447)
        ·
          refine ⟨60111412180476188318193671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40074274786984125545462447 60111412180476188318193671)
          ·
            refine ⟨90167118270714282477290507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60111412180476188318193671 90167118270714282477290507)
            ·
              refine ⟨135250677406071423715935761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90167118270714282477290507 135250677406071423715935761)
              ·
                refine ⟨101438008054553567786951821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135250677406071423715935761 101438008054553567786951821)
                ·
                  refine ⟨38039253020457587920106933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101438008054553567786951821 38039253020457587920106933)
                  ·
                    refine ⟨3566179970667898867510025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38039253020457587920106933 3566179970667898867510025)
                    ·
                      refine ⟨2674634978000924150632519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3566179970667898867510025 2674634978000924150632519)
                      ·
                        rfl

theorem cell23_5208833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_5208833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208833 prefixEnd_5208833 := by exact prefixLift 5208833
  have htrace : WordTrace (prefixWord ++ tailWord_5208833) baseStart_5208833 baseEnd_5208833 := by
    simpa [prefixWord, tailWord_5208833, baseEnd_5208833] using wordTrace_append hprefix tailTrace_5208833
  have hstable : (prefixWord ++ tailWord_5208833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208833).length < 2 ^ (prefixWord ++ tailWord_5208833).sum := by decide
  have hdescent : baseEnd_5208833 < baseStart_5208833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208834 : List Nat := [3, 4, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_5208834 : Nat := 118140960795 + 5208834 * 2 ^ 59
def prefixEnd_5208834 : Nat := 4983230072969 + 3 ^ 40 * 5208834 * 2
def baseEnd_5208834 : Nat := 891545163827192882240005

theorem tailTrace_5208834 : CollatzResearch.WordTrace tailWord_5208834 prefixEnd_5208834 891545163827192882240005 := by
  unfold tailWord_5208834
  simp only [CollatzResearch.WordTrace]
  refine ⟨47495445902822872716948389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126654522407527660578529037 47495445902822872716948389)
  ·
    refine ⟨8905396106779288634427823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47495445902822872716948389 8905396106779288634427823)
    ·
      refine ⟨13358094160168932951641735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8905396106779288634427823 13358094160168932951641735)
      ·
        refine ⟨20037141240253399427462603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13358094160168932951641735 20037141240253399427462603)
        ·
          refine ⟨30055711860380099141193905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20037141240253399427462603 30055711860380099141193905)
          ·
            refine ⟨22541783895285074355895429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30055711860380099141193905 22541783895285074355895429)
            ·
              refine ⟨4226584480365951441730393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22541783895285074355895429 4226584480365951441730393)
              ·
                refine ⟨3169938360274463581297795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4226584480365951441730393 3169938360274463581297795)
                ·
                  refine ⟨4754907540411695371946693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3169938360274463581297795 4754907540411695371946693)
                  ·
                    refine ⟨891545163827192882240005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4754907540411695371946693 891545163827192882240005)
                    ·
                      rfl

theorem cell23_5208834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_5208834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208834 prefixEnd_5208834 := by exact prefixLift 5208834
  have htrace : WordTrace (prefixWord ++ tailWord_5208834) baseStart_5208834 baseEnd_5208834 := by
    simpa [prefixWord, tailWord_5208834, baseEnd_5208834] using wordTrace_append hprefix tailTrace_5208834
  have hstable : (prefixWord ++ tailWord_5208834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208834).length < 2 ^ (prefixWord ++ tailWord_5208834).sum := by decide
  have hdescent : baseEnd_5208834 < baseStart_5208834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208863 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 4]
def baseStart_5208863 : Nat := 118140960795 + 5208863 * 2 ^ 59
def prefixEnd_5208863 : Nat := 4983230072969 + 3 ^ 40 * 5208863 * 2
def baseEnd_5208863 : Nat := 2674650382420559033257381

theorem tailTrace_5208863 : CollatzResearch.WordTrace tailWord_5208863 prefixEnd_5208863 2674650382420559033257381 := by
  unfold tailWord_5208863
  simp only [CollatzResearch.WordTrace]
  refine ⟨189982841328186428820599243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126655227552124285880399495 189982841328186428820599243)
  ·
    refine ⟨284974261992279643230898865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189982841328186428820599243 284974261992279643230898865)
    ·
      refine ⟨213730696494209732423174149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284974261992279643230898865 213730696494209732423174149)
      ·
        refine ⟨40074505592664324829345153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213730696494209732423174149 40074505592664324829345153)
        ·
          refine ⟨30055879194498243622008865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40074505592664324829345153 30055879194498243622008865)
          ·
            refine ⟨22541909395873682716506649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30055879194498243622008865 22541909395873682716506649)
            ·
              refine ⟨16906432046905262037379987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22541909395873682716506649 16906432046905262037379987)
              ·
                refine ⟨25359648070357893056069981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16906432046905262037379987 25359648070357893056069981)
                ·
                  refine ⟨9509868026384209896026243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25359648070357893056069981 9509868026384209896026243)
                  ·
                    refine ⟨14264802039576314844039365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9509868026384209896026243 14264802039576314844039365)
                    ·
                      refine ⟨2674650382420559033257381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14264802039576314844039365 2674650382420559033257381)
                      ·
                        rfl

theorem cell23_5208863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_5208863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208863 prefixEnd_5208863 := by exact prefixLift 5208863
  have htrace : WordTrace (prefixWord ++ tailWord_5208863) baseStart_5208863 baseEnd_5208863 := by
    simpa [prefixWord, tailWord_5208863, baseEnd_5208863] using wordTrace_append hprefix tailTrace_5208863
  have hstable : (prefixWord ++ tailWord_5208863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208863).length < 2 ^ (prefixWord ++ tailWord_5208863).sum := by decide
  have hdescent : baseEnd_5208863 < baseStart_5208863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208890 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 4, 4]
def baseStart_5208890 : Nat := 118140960795 + 5208890 * 2 ^ 59
def prefixEnd_5208890 : Nat := 4983230072969 + 3 ^ 40 * 5208890 * 2
def baseEnd_5208890 : Nat := 891554748799410142539919

theorem tailTrace_5208890 : CollatzResearch.WordTrace tailWord_5208890 prefixEnd_5208890 891554748799410142539919 := by
  unfold tailWord_5208890
  simp only [CollatzResearch.WordTrace]
  refine ⟨47495956524772153107958031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126655884066059074954554749 47495956524772153107958031)
  ·
    refine ⟨71243934787158229661937047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47495956524772153107958031 71243934787158229661937047)
    ·
      refine ⟨106865902180737344492905571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71243934787158229661937047 106865902180737344492905571)
      ·
        refine ⟨160298853271106016739358357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106865902180737344492905571 160298853271106016739358357)
        ·
          refine ⟨7514008747083094534657423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 160298853271106016739358357 7514008747083094534657423)
          ·
            refine ⟨11271013120624641801986135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7514008747083094534657423 11271013120624641801986135)
            ·
              refine ⟨16906519680936962702979203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11271013120624641801986135 16906519680936962702979203)
              ·
                refine ⟨25359779521405444054468805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16906519680936962702979203 25359779521405444054468805)
                ·
                  refine ⟨4754958660263520760212901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25359779521405444054468805 4754958660263520760212901)
                  ·
                    refine ⟨891554748799410142539919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4754958660263520760212901 891554748799410142539919)
                    ·
                      rfl

theorem cell23_5208890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 4, 4].length) (baseStart_5208890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208890 prefixEnd_5208890 := by exact prefixLift 5208890
  have htrace : WordTrace (prefixWord ++ tailWord_5208890) baseStart_5208890 baseEnd_5208890 := by
    simpa [prefixWord, tailWord_5208890, baseEnd_5208890] using wordTrace_append hprefix tailTrace_5208890
  have hstable : (prefixWord ++ tailWord_5208890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208890).length < 2 ^ (prefixWord ++ tailWord_5208890).sum := by decide
  have hdescent : baseEnd_5208890 < baseStart_5208890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208906 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 1, 4, 6]
def baseStart_5208906 : Nat := 118140960795 + 5208906 * 2 ^ 59
def prefixEnd_5208906 : Nat := 4983230072969 + 3 ^ 40 * 5208906 * 2
def baseEnd_5208906 : Nat := 2674672462088702365019683

theorem tailTrace_5208906 : CollatzResearch.WordTrace tailWord_5208906 prefixEnd_5208906 2674672462088702365019683 := by
  unfold tailWord_5208906
  simp only [CollatzResearch.WordTrace]
  refine ⟨47496102416757661791103643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126656273111353764776276381 47496102416757661791103643)
  ·
    refine ⟨71244153625136492686655465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47496102416757661791103643 71244153625136492686655465)
    ·
      refine ⟨53433115218852369514991599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71244153625136492686655465 53433115218852369514991599)
      ·
        refine ⟨80149672828278554272487399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53433115218852369514991599 80149672828278554272487399)
        ·
          refine ⟨120224509242417831408731099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80149672828278554272487399 120224509242417831408731099)
          ·
            refine ⟨180336763863626747113096649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120224509242417831408731099 180336763863626747113096649)
            ·
              refine ⟨135252572897720060334822487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180336763863626747113096649 135252572897720060334822487)
              ·
                refine ⟨202878859346580090502233731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135252572897720060334822487 202878859346580090502233731)
                ·
                  refine ⟨304318289019870135753350597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202878859346580090502233731 304318289019870135753350597)
                  ·
                    refine ⟨57059679191225650453753237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 304318289019870135753350597 57059679191225650453753237)
                    ·
                      refine ⟨2674672462088702365019683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57059679191225650453753237 2674672462088702365019683)
                      ·
                        rfl

theorem cell23_5208906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_5208906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208906 prefixEnd_5208906 := by exact prefixLift 5208906
  have htrace : WordTrace (prefixWord ++ tailWord_5208906) baseStart_5208906 baseEnd_5208906 := by
    simpa [prefixWord, tailWord_5208906, baseEnd_5208906] using wordTrace_append hprefix tailTrace_5208906
  have hstable : (prefixWord ++ tailWord_5208906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208906).length < 2 ^ (prefixWord ++ tailWord_5208906).sum := by decide
  have hdescent : baseEnd_5208906 < baseStart_5208906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208931 : List Nat := [1, 1, 1, 5, 3, 3, 1, 3, 1, 2, 2]
def baseStart_5208931 : Nat := 118140960795 + 5208931 * 2 ^ 59
def prefixEnd_5208931 : Nat := 4983230072969 + 3 ^ 40 * 5208931 * 2
def baseEnd_5208931 : Nat := 2674685299105064767207069

theorem tailTrace_5208931 : CollatzResearch.WordTrace tailWord_5208931 prefixEnd_5208931 2674685299105064767207069 := by
  unfold tailWord_5208931
  simp only [CollatzResearch.WordTrace]
  refine ⟨189985321491940076434074647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126656880994626717622716431 189985321491940076434074647)
  ·
    refine ⟨284977982237910114651111971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189985321491940076434074647 284977982237910114651111971)
    ·
      refine ⟨427466973356865171976667957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284977982237910114651111971 427466973356865171976667957)
      ·
        refine ⟨40075028752206109872812621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 427466973356865171976667957 40075028752206109872812621)
        ·
          refine ⟨15028135782077291202304733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40075028752206109872812621 15028135782077291202304733)
          ·
            refine ⟨5635550918278984200864275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15028135782077291202304733 5635550918278984200864275)
            ·
              refine ⟨8453326377418476301296413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5635550918278984200864275 8453326377418476301296413)
              ·
                refine ⟨3169997391531928612986155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8453326377418476301296413 3169997391531928612986155)
                ·
                  refine ⟨4754996087297892919479233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3169997391531928612986155 4754996087297892919479233)
                  ·
                    refine ⟨3566247065473419689609425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4754996087297892919479233 3566247065473419689609425)
                    ·
                      refine ⟨2674685299105064767207069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3566247065473419689609425 2674685299105064767207069)
                      ·
                        rfl

theorem cell23_5208931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_5208931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208931 prefixEnd_5208931 := by exact prefixLift 5208931
  have htrace : WordTrace (prefixWord ++ tailWord_5208931) baseStart_5208931 baseEnd_5208931 := by
    simpa [prefixWord, tailWord_5208931, baseEnd_5208931] using wordTrace_append hprefix tailTrace_5208931
  have hstable : (prefixWord ++ tailWord_5208931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208931).length < 2 ^ (prefixWord ++ tailWord_5208931).sum := by decide
  have hdescent : baseEnd_5208931 < baseStart_5208931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5208958 : List Nat := [4, 2, 3, 1, 3, 1, 2, 1, 2, 4]
def baseStart_5208958 : Nat := 118140960795 + 5208958 * 2 ^ 59
def prefixEnd_5208958 : Nat := 4983230072969 + 3 ^ 40 * 5208958 * 2
def baseEnd_5208958 : Nat := 891566387694245387189815

theorem tailTrace_5208958 : CollatzResearch.WordTrace tailWord_5208958 prefixEnd_5208958 891566387694245387189815 := by
  unfold tailWord_5208958
  simp only [CollatzResearch.WordTrace]
  refine ⟨23748288282855282505663441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126657537508561506696871685 23748288282855282505663441)
  ·
    refine ⟨17811216212141461879247581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23748288282855282505663441 17811216212141461879247581)
    ·
      refine ⟨6679206079553048204717843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17811216212141461879247581 6679206079553048204717843)
      ·
        refine ⟨10018809119329572307076765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6679206079553048204717843 10018809119329572307076765)
        ·
          refine ⟨3757053419748589615153787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10018809119329572307076765 3757053419748589615153787)
          ·
            refine ⟨5635580129622884422730681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3757053419748589615153787 5635580129622884422730681)
            ·
              refine ⟨4226685097217163317048011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5635580129622884422730681 4226685097217163317048011)
              ·
                refine ⟨6340027645825744975572017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4226685097217163317048011 6340027645825744975572017)
                ·
                  refine ⟨4755020734369308731679013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6340027645825744975572017 4755020734369308731679013)
                  ·
                    refine ⟨891566387694245387189815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4755020734369308731679013 891566387694245387189815)
                    ·
                      rfl

theorem cell23_5208958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_5208958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5208958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5208958 prefixEnd_5208958 := by exact prefixLift 5208958
  have htrace : WordTrace (prefixWord ++ tailWord_5208958) baseStart_5208958 baseEnd_5208958 := by
    simpa [prefixWord, tailWord_5208958, baseEnd_5208958] using wordTrace_append hprefix tailTrace_5208958
  have hstable : (prefixWord ++ tailWord_5208958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5208958).length < 2 ^ (prefixWord ++ tailWord_5208958).sum := by decide
  have hdescent : baseEnd_5208958 < baseStart_5208958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5208958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209003 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 3]
def baseStart_5209003 : Nat := 118140960795 + 5209003 * 2 ^ 59
def prefixEnd_5209003 : Nat := 4983230072969 + 3 ^ 40 * 5209003 * 2
def baseEnd_5209003 : Nat := 2674722269712188485506737

theorem tailTrace_5209003 : CollatzResearch.WordTrace tailWord_5209003 prefixEnd_5209003 2674722269712188485506737 := by
  unfold tailWord_5209003
  simp only [CollatzResearch.WordTrace]
  refine ⟨189987947547679232730695663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126658631698452821820463775 189987947547679232730695663)
  ·
    refine ⟨284981921321518849096043495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189987947547679232730695663 284981921321518849096043495)
    ·
      refine ⟨427472881982278273644065243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284981921321518849096043495 427472881982278273644065243)
      ·
        refine ⟨641209322973417410466097865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427472881982278273644065243 641209322973417410466097865)
        ·
          refine ⟨480906992230063057849573399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 641209322973417410466097865 480906992230063057849573399)
          ·
            refine ⟨721360488345094586774360099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480906992230063057849573399 721360488345094586774360099)
            ·
              refine ⟨1082040732517641880161540149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 721360488345094586774360099 1082040732517641880161540149)
              ·
                refine ⟨101441318673528926265144389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1082040732517641880161540149 101441318673528926265144389)
                ·
                  refine ⟨19020247251286673674714573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101441318673528926265144389 19020247251286673674714573)
                  ·
                    refine ⟨7132592719232502628017965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19020247251286673674714573 7132592719232502628017965)
                    ·
                      refine ⟨2674722269712188485506737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7132592719232502628017965 2674722269712188485506737)
                      ·
                        rfl

theorem cell23_5209003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 3].length) (baseStart_5209003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209003 prefixEnd_5209003 := by exact prefixLift 5209003
  have htrace : WordTrace (prefixWord ++ tailWord_5209003) baseStart_5209003 baseEnd_5209003 := by
    simpa [prefixWord, tailWord_5209003, baseEnd_5209003] using wordTrace_append hprefix tailTrace_5209003
  have hstable : (prefixWord ++ tailWord_5209003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209003).length < 2 ^ (prefixWord ++ tailWord_5209003).sum := by decide
  have hdescent : baseEnd_5209003 < baseStart_5209003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209121 : List Nat := [1, 2, 3, 2, 3, 2, 3, 2, 1, 4]
def baseStart_5209121 : Nat := 118140960795 + 5209121 * 2 ^ 59
def prefixEnd_5209121 : Nat := 4983230072969 + 3 ^ 40 * 5209121 * 2
def baseEnd_5209121 : Nat := 891594286809806341277065

theorem tailTrace_5209121 : CollatzResearch.WordTrace tailWord_5209121 prefixEnd_5209121 891594286809806341277065 := by
  unfold tailWord_5209121
  simp only [CollatzResearch.WordTrace]
  refine ⟨189992251361251738883491217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126661500907501159255660811 189992251361251738883491217)
  ·
    refine ⟨142494188520938804162618413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189992251361251738883491217 142494188520938804162618413)
    ·
      refine ⟨53435320695352051560981905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142494188520938804162618413 53435320695352051560981905)
      ·
        refine ⟨40076490521514038670736429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53435320695352051560981905 40076490521514038670736429)
        ·
          refine ⟨15028683945567764501526161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40076490521514038670736429 15028683945567764501526161)
          ·
            refine ⟨11271512959175823376144621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15028683945567764501526161 11271512959175823376144621)
            ·
              refine ⟨4226817359690933766054233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11271512959175823376144621 4226817359690933766054233)
              ·
                refine ⟨3170113019768200324540675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4226817359690933766054233 3170113019768200324540675)
                ·
                  refine ⟨4755169529652300486811013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3170113019768200324540675 4755169529652300486811013)
                  ·
                    refine ⟨891594286809806341277065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4755169529652300486811013 891594286809806341277065)
                    ·
                      rfl

theorem cell23_5209121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_5209121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209121 prefixEnd_5209121 := by exact prefixLift 5209121
  have htrace : WordTrace (prefixWord ++ tailWord_5209121) baseStart_5209121 baseEnd_5209121 := by
    simpa [prefixWord, tailWord_5209121, baseEnd_5209121] using wordTrace_append hprefix tailTrace_5209121
  have hstable : (prefixWord ++ tailWord_5209121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209121).length < 2 ^ (prefixWord ++ tailWord_5209121).sum := by decide
  have hdescent : baseEnd_5209121 < baseStart_5209121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209137 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 4, 3, 2]
def baseStart_5209137 : Nat := 118140960795 + 5209137 * 2 ^ 59
def prefixEnd_5209137 : Nat := 4983230072969 + 3 ^ 40 * 5209137 * 2
def baseEnd_5209137 : Nat := 2674791076119890961231121

theorem tailTrace_5209137 : CollatzResearch.WordTrace tailWord_5209137 prefixEnd_5209137 2674791076119890961231121 := by
  unfold tailWord_5209137
  simp only [CollatzResearch.WordTrace]
  refine ⟨189992834929193773616073665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126661889952795849077382443 189992834929193773616073665)
  ·
    refine ⟨142494626196895330212055249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189992834929193773616073665 142494626196895330212055249)
    ·
      refine ⟨106870969647671497659041437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142494626196895330212055249 106870969647671497659041437)
      ·
        refine ⟨40076613617876811622140539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106870969647671497659041437 40076613617876811622140539)
        ·
          refine ⟨60114920426815217433210809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40076613617876811622140539 60114920426815217433210809)
          ·
            refine ⟨45086190320111413074908107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60114920426815217433210809 45086190320111413074908107)
            ·
              refine ⟨67629285480167119612362161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45086190320111413074908107 67629285480167119612362161)
              ·
                refine ⟨50721964110125339709271621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67629285480167119612362161 50721964110125339709271621)
                ·
                  refine ⟨9510368270648501195488429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50721964110125339709271621 9510368270648501195488429)
                  ·
                    refine ⟨3566388101493187948308161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9510368270648501195488429 3566388101493187948308161)
                    ·
                      refine ⟨2674791076119890961231121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3566388101493187948308161 2674791076119890961231121)
                      ·
                        rfl

theorem cell23_5209137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_5209137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209137 prefixEnd_5209137 := by exact prefixLift 5209137
  have htrace : WordTrace (prefixWord ++ tailWord_5209137) baseStart_5209137 baseEnd_5209137 := by
    simpa [prefixWord, tailWord_5209137, baseEnd_5209137] using wordTrace_append hprefix tailTrace_5209137
  have hstable : (prefixWord ++ tailWord_5209137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209137).length < 2 ^ (prefixWord ++ tailWord_5209137).sum := by decide
  have hdescent : baseEnd_5209137 < baseStart_5209137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209160 : List Nat := [2, 1, 3, 1, 1, 1, 5, 2, 1, 6]
def baseStart_5209160 : Nat := 118140960795 + 5209160 * 2 ^ 59
def prefixEnd_5209160 : Nat := 4983230072969 + 3 ^ 40 * 5209160 * 2
def baseEnd_5209160 : Nat := 891600962058314790414505

theorem tailTrace_5209160 : CollatzResearch.WordTrace tailWord_5209160 prefixEnd_5209160 891600962058314790414505 := by
  unfold tailWord_5209160
  simp only [CollatzResearch.WordTrace]
  refine ⟨94996836904055224272080467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126662449205406965696107289 94996836904055224272080467)
  ·
    refine ⟨142495255356082836408120701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94996836904055224272080467 142495255356082836408120701)
    ·
      refine ⟨53435720758531063653045263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142495255356082836408120701 53435720758531063653045263)
      ·
        refine ⟨80153581137796595479567895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53435720758531063653045263 80153581137796595479567895)
        ·
          refine ⟨120230371706694893219351843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80153581137796595479567895 120230371706694893219351843)
          ·
            refine ⟨180345557560042339829027765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120230371706694893219351843 180345557560042339829027765)
            ·
              refine ⟨16907396021253969358971353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 180345557560042339829027765 16907396021253969358971353)
              ·
                refine ⟨12680547015940477019228515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16907396021253969358971353 12680547015940477019228515)
                ·
                  refine ⟨19020820523910715528842773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12680547015940477019228515 19020820523910715528842773)
                  ·
                    refine ⟨891600962058314790414505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19020820523910715528842773 891600962058314790414505)
                    ·
                      rfl

theorem cell23_5209160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_5209160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209160 prefixEnd_5209160 := by exact prefixLift 5209160
  have htrace : WordTrace (prefixWord ++ tailWord_5209160) baseStart_5209160 baseEnd_5209160 := by
    simpa [prefixWord, tailWord_5209160, baseEnd_5209160] using wordTrace_append hprefix tailTrace_5209160
  have hstable : (prefixWord ++ tailWord_5209160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209160).length < 2 ^ (prefixWord ++ tailWord_5209160).sum := by decide
  have hdescent : baseEnd_5209160 < baseStart_5209160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209184 : List Nat := [2, 1, 1, 3, 2, 2, 2, 3, 3, 2, 2]
def baseStart_5209184 : Nat := 118140960795 + 5209184 * 2 ^ 59
def prefixEnd_5209184 : Nat := 4983230072969 + 3 ^ 40 * 5209184 * 2
def baseEnd_5209184 : Nat := 2674815209710652277343405

theorem tailTrace_5209184 : CollatzResearch.WordTrace tailWord_5209184 prefixEnd_5209184 2674815209710652277343405 := by
  unfold tailWord_5209184
  simp only [CollatzResearch.WordTrace]
  refine ⟨94997274580011750321517303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126663032773349000428689737 94997274580011750321517303)
  ·
    refine ⟨142495911870017625482275955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94997274580011750321517303 142495911870017625482275955)
    ·
      refine ⟨213743867805026438223413933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142495911870017625482275955 213743867805026438223413933)
      ·
        refine ⟨80153950426884914333780225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213743867805026438223413933 80153950426884914333780225)
        ·
          refine ⟨60115462820163685750335169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80153950426884914333780225 60115462820163685750335169)
          ·
            refine ⟨45086597115122764312751377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60115462820163685750335169 45086597115122764312751377)
            ·
              refine ⟨33814947836342073234563533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45086597115122764312751377 33814947836342073234563533)
              ·
                refine ⟨12680605438628277462961325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33814947836342073234563533 12680605438628277462961325)
                ·
                  refine ⟨4755227039485604048610497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12680605438628277462961325 4755227039485604048610497)
                  ·
                    refine ⟨3566420279614203036457873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4755227039485604048610497 3566420279614203036457873)
                    ·
                      refine ⟨2674815209710652277343405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3566420279614203036457873 2674815209710652277343405)
                      ·
                        rfl

theorem cell23_5209184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 3, 2, 2].length) (baseStart_5209184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209184 prefixEnd_5209184 := by exact prefixLift 5209184
  have htrace : WordTrace (prefixWord ++ tailWord_5209184) baseStart_5209184 baseEnd_5209184 := by
    simpa [prefixWord, tailWord_5209184, baseEnd_5209184] using wordTrace_append hprefix tailTrace_5209184
  have hstable : (prefixWord ++ tailWord_5209184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209184).length < 2 ^ (prefixWord ++ tailWord_5209184).sum := by decide
  have hdescent : baseEnd_5209184 < baseStart_5209184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209194 : List Nat := [3, 1, 3, 2, 2, 1, 2, 3, 2, 4]
def baseStart_5209194 : Nat := 118140960795 + 5209194 * 2 ^ 59
def prefixEnd_5209194 : Nat := 4983230072969 + 3 ^ 40 * 5209194 * 2
def baseEnd_5209194 : Nat := 891606781505732412739453

theorem tailTrace_5209194 : CollatzResearch.WordTrace tailWord_5209194 prefixEnd_5209194 891606781505732412739453 := by
  unfold tailWord_5209194
  simp only [CollatzResearch.WordTrace]
  refine ⟨47498728472496818087724659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126663275926658181567265757 47498728472496818087724659)
  ·
    refine ⟨71248092708745227131586989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47498728472496818087724659 71248092708745227131586989)
    ·
      refine ⟨26718034765779460174345121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71248092708745227131586989 26718034765779460174345121)
      ·
        refine ⟨20038526074334595130758841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26718034765779460174345121 20038526074334595130758841)
        ·
          refine ⟨15028894555750946348069131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20038526074334595130758841 15028894555750946348069131)
          ·
            refine ⟨22543341833626419522103697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15028894555750946348069131 22543341833626419522103697)
            ·
              refine ⟨16907506375219814641577773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22543341833626419522103697 16907506375219814641577773)
              ·
                refine ⟨6340314890707430490591665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16907506375219814641577773 6340314890707430490591665)
                ·
                  refine ⟨4755236168030572867943749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6340314890707430490591665 4755236168030572867943749)
                  ·
                    refine ⟨891606781505732412739453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4755236168030572867943749 891606781505732412739453)
                    ·
                      rfl

theorem cell23_5209194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_5209194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209194 prefixEnd_5209194 := by exact prefixLift 5209194
  have htrace : WordTrace (prefixWord ++ tailWord_5209194) baseStart_5209194 baseEnd_5209194 := by
    simpa [prefixWord, tailWord_5209194, baseEnd_5209194] using wordTrace_append hprefix tailTrace_5209194
  have hstable : (prefixWord ++ tailWord_5209194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209194).length < 2 ^ (prefixWord ++ tailWord_5209194).sum := by decide
  have hdescent : baseEnd_5209194 < baseStart_5209194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209197 : List Nat := [1, 5, 1, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_5209197 : Nat := 118140960795 + 5209197 * 2 ^ 59
def prefixEnd_5209197 : Nat := 4983230072969 + 3 ^ 40 * 5209197 * 2
def baseEnd_5209197 : Nat := 2674821884959160726480845

theorem tailTrace_5209197 : CollatzResearch.WordTrace tailWord_5209197 prefixEnd_5209197 2674821884959160726480845 := by
  unfold tailWord_5209197
  simp only [CollatzResearch.WordTrace]
  refine ⟨189995023308976403863257845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126663348872650935908838563 189995023308976403863257845)
  ·
    refine ⟨17812033435216537862180423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 189995023308976403863257845 17812033435216537862180423)
    ·
      refine ⟨26718050152824806793270635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17812033435216537862180423 26718050152824806793270635)
      ·
        refine ⟨40077075229237210189905953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26718050152824806793270635 40077075229237210189905953)
        ·
          refine ⟨30057806421927907642429465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40077075229237210189905953 30057806421927907642429465)
          ·
            refine ⟨22543354816445930731822099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30057806421927907642429465 22543354816445930731822099)
            ·
              refine ⟨33815032224668896097733149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22543354816445930731822099 33815032224668896097733149)
              ·
                refine ⟨12680637084250836036649931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33815032224668896097733149 12680637084250836036649931)
                ·
                  refine ⟨19020955626376254054974897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12680637084250836036649931 19020955626376254054974897)
                  ·
                    refine ⟨14265716719782190541231173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19020955626376254054974897 14265716719782190541231173)
                    ·
                      refine ⟨2674821884959160726480845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14265716719782190541231173 2674821884959160726480845)
                      ·
                        rfl

theorem cell23_5209197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_5209197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209197 prefixEnd_5209197 := by exact prefixLift 5209197
  have htrace : WordTrace (prefixWord ++ tailWord_5209197) baseStart_5209197 baseEnd_5209197 := by
    simpa [prefixWord, tailWord_5209197, baseEnd_5209197] using wordTrace_append hprefix tailTrace_5209197
  have hstable : (prefixWord ++ tailWord_5209197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209197).length < 2 ^ (prefixWord ++ tailWord_5209197).sum := by decide
  have hdescent : baseEnd_5209197 < baseStart_5209197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209205 : List Nat := [1, 3, 4, 3, 2, 1, 1, 1, 2, 3, 2]
def baseStart_5209205 : Nat := 118140960795 + 5209205 * 2 ^ 59
def prefixEnd_5209205 : Nat := 4983230072969 + 3 ^ 40 * 5209205 * 2
def baseEnd_5209205 : Nat := 2674825992804396695180809

theorem tailTrace_5209205 : CollatzResearch.WordTrace tailWord_5209205 prefixEnd_5209205 2674825992804396695180809 := by
  unfold tailWord_5209205
  simp only [CollatzResearch.WordTrace]
  refine ⟨189995315092947421229549069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126663543395298280819699379 189995315092947421229549069)
  ·
    refine ⟨71248243159855282961080901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189995315092947421229549069 71248243159855282961080901)
    ·
      refine ⟨13359045592472865555202669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71248243159855282961080901 13359045592472865555202669)
      ·
        refine ⟨5009642097177324583201001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13359045592472865555202669 5009642097177324583201001)
        ·
          refine ⟨3757231572882993437400751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5009642097177324583201001 3757231572882993437400751)
          ·
            refine ⟨5635847359324490156101127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3757231572882993437400751 5635847359324490156101127)
            ·
              refine ⟨8453771038986735234151691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5635847359324490156101127 8453771038986735234151691)
              ·
                refine ⟨12680656558480102851227537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8453771038986735234151691 12680656558480102851227537)
                ·
                  refine ⟨9510492418860077138420653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12680656558480102851227537 9510492418860077138420653)
                  ·
                    refine ⟨3566434657072528926907745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9510492418860077138420653 3566434657072528926907745)
                    ·
                      refine ⟨2674825992804396695180809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3566434657072528926907745 2674825992804396695180809)
                      ·
                        rfl

theorem cell23_5209205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_5209205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209205 prefixEnd_5209205 := by exact prefixLift 5209205
  have htrace : WordTrace (prefixWord ++ tailWord_5209205) baseStart_5209205 baseEnd_5209205 := by
    simpa [prefixWord, tailWord_5209205, baseEnd_5209205] using wordTrace_append hprefix tailTrace_5209205
  have hstable : (prefixWord ++ tailWord_5209205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209205).length < 2 ^ (prefixWord ++ tailWord_5209205).sum := by decide
  have hdescent : baseEnd_5209205 < baseStart_5209205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209257 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 7, 4, 2]
def baseStart_5209257 : Nat := 118140960795 + 5209257 * 2 ^ 59
def prefixEnd_5209257 : Nat := 4983230072969 + 3 ^ 40 * 5209257 * 2
def baseEnd_5209257 : Nat := 2674852693798430491730569

theorem tailTrace_5209257 : CollatzResearch.WordTrace tailWord_5209257 prefixEnd_5209257 2674852693798430491730569 := by
  unfold tailWord_5209257
  simp only [CollatzResearch.WordTrace]
  refine ⟨189997211688759034110442025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126664807792506022740294683 189997211688759034110442025)
  ·
    refine ⟨142497908766569275582831519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189997211688759034110442025 142497908766569275582831519)
    ·
      refine ⟨213746863149853913374247279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142497908766569275582831519 213746863149853913374247279)
      ·
        refine ⟨320620294724780870061370919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213746863149853913374247279 320620294724780870061370919)
        ·
          refine ⟨480930442087171305092056379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320620294724780870061370919 480930442087171305092056379)
          ·
            refine ⟨721395663130756957638084569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480930442087171305092056379 721395663130756957638084569)
            ·
              refine ⟨541046747348067718228563427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 721395663130756957638084569 541046747348067718228563427)
              ·
                refine ⟨811570121022101577342845141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541046747348067718228563427 811570121022101577342845141)
                ·
                  refine ⟨19021174711455505718972933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 811570121022101577342845141 19021174711455505718972933)
                  ·
                    refine ⟨3566470258397907322307425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19021174711455505718972933 3566470258397907322307425)
                    ·
                      refine ⟨2674852693798430491730569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3566470258397907322307425 2674852693798430491730569)
                      ·
                        rfl

theorem cell23_5209257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 4, 2].length) (baseStart_5209257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209257 prefixEnd_5209257 := by exact prefixLift 5209257
  have htrace : WordTrace (prefixWord ++ tailWord_5209257) baseStart_5209257 baseEnd_5209257 := by
    simpa [prefixWord, tailWord_5209257, baseEnd_5209257] using wordTrace_append hprefix tailTrace_5209257
  have hstable : (prefixWord ++ tailWord_5209257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209257).length < 2 ^ (prefixWord ++ tailWord_5209257).sum := by decide
  have hdescent : baseEnd_5209257 < baseStart_5209257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209286 : List Nat := [6, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_5209286 : Nat := 118140960795 + 5209286 * 2 ^ 59
def prefixEnd_5209286 : Nat := 4983230072969 + 3 ^ 40 * 5209286 * 2
def baseEnd_5209286 : Nat := 2674867584737410878267937

theorem tailTrace_5209286 : CollatzResearch.WordTrace tailWord_5209286 prefixEnd_5209286 2674867584737410878267937 := by
  unfold tailWord_5209286
  simp only [CollatzResearch.WordTrace]
  refine ⟨5937445918926686626976491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 126665512937102648042165141 5937445918926686626976491)
  ·
    refine ⟨8906168878390029940464737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5937445918926686626976491 8906168878390029940464737)
    ·
      refine ⟨6679626658792522455348553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8906168878390029940464737 6679626658792522455348553)
      ·
        refine ⟨5009719994094391841511415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6679626658792522455348553 5009719994094391841511415)
        ·
          refine ⟨7514579991141587762267123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5009719994094391841511415 7514579991141587762267123)
          ·
            refine ⟨11271869986712381643400685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7514579991141587762267123 11271869986712381643400685)
            ·
              refine ⟨4226951245017143116275257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11271869986712381643400685 4226951245017143116275257)
              ·
                refine ⟨3170213433762857337206443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4226951245017143116275257 3170213433762857337206443)
                ·
                  refine ⟨4755320150644286005809665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3170213433762857337206443 4755320150644286005809665)
                  ·
                    refine ⟨3566490112983214504357249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4755320150644286005809665 3566490112983214504357249)
                    ·
                      refine ⟨2674867584737410878267937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3566490112983214504357249 2674867584737410878267937)
                      ·
                        rfl

theorem cell23_5209286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_5209286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209286 prefixEnd_5209286 := by exact prefixLift 5209286
  have htrace : WordTrace (prefixWord ++ tailWord_5209286) baseStart_5209286 baseEnd_5209286 := by
    simpa [prefixWord, tailWord_5209286, baseEnd_5209286] using wordTrace_append hprefix tailTrace_5209286
  have hstable : (prefixWord ++ tailWord_5209286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209286).length < 2 ^ (prefixWord ++ tailWord_5209286).sum := by decide
  have hdescent : baseEnd_5209286 < baseStart_5209286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209302 : List Nat := [5, 2, 1, 2, 2, 2, 2, 1, 2, 1, 3]
def baseStart_5209302 : Nat := 118140960795 + 5209302 * 2 ^ 59
def prefixEnd_5209302 : Nat := 4983230072969 + 3 ^ 40 * 5209302 * 2
def baseEnd_5209302 : Nat := 2674875800427882815667863

theorem tailTrace_5209302 : CollatzResearch.WordTrace tailWord_5209302 prefixEnd_5209302 2674875800427882815667863 := by
  unfold tailWord_5209302
  simp only [CollatzResearch.WordTrace]
  refine ⟨11874928310849750424739385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126665901982397337863886773 11874928310849750424739385)
  ·
    refine ⟨8906196233137312818554539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11874928310849750424739385 8906196233137312818554539)
    ·
      refine ⟨13359294349705969227831809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8906196233137312818554539 13359294349705969227831809)
      ·
        refine ⟨10019470762279476920873857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13359294349705969227831809 10019470762279476920873857)
        ·
          refine ⟨7514603071709607690655393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10019470762279476920873857 7514603071709607690655393)
          ·
            refine ⟨5635952303782205767991545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7514603071709607690655393 5635952303782205767991545)
            ·
              refine ⟨4226964227836654325993659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5635952303782205767991545 4226964227836654325993659)
              ·
                refine ⟨6340446341754981488990489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4226964227836654325993659 6340446341754981488990489)
                ·
                  refine ⟨4755334756316236116742867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6340446341754981488990489 4755334756316236116742867)
                  ·
                    refine ⟨7133002134474354175114301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4755334756316236116742867 7133002134474354175114301)
                    ·
                      refine ⟨2674875800427882815667863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7133002134474354175114301 2674875800427882815667863)
                      ·
                        rfl

theorem cell23_5209302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_5209302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209302 prefixEnd_5209302 := by exact prefixLift 5209302
  have htrace : WordTrace (prefixWord ++ tailWord_5209302) baseStart_5209302 baseEnd_5209302 := by
    simpa [prefixWord, tailWord_5209302, baseEnd_5209302] using wordTrace_append hprefix tailTrace_5209302
  have hstable : (prefixWord ++ tailWord_5209302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209302).length < 2 ^ (prefixWord ++ tailWord_5209302).sum := by decide
  have hdescent : baseEnd_5209302 < baseStart_5209302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209348 : List Nat := [2, 3, 2, 2, 2, 3, 2, 2, 5]
def baseStart_5209348 : Nat := 118140960795 + 5209348 * 2 ^ 59
def prefixEnd_5209348 : Nat := 4983230072969 + 3 ^ 40 * 5209348 * 2
def baseEnd_5209348 : Nat := 297211046726443292854739

theorem tailTrace_5209348 : CollatzResearch.WordTrace tailWord_5209348 prefixEnd_5209348 297211046726443292854739 := by
  unfold tailWord_5209348
  simp only [CollatzResearch.WordTrace]
  refine ⟨95000265365714678326002349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126667020487619571101336465 95000265365714678326002349)
  ·
    refine ⟨35625099512143004372250881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95000265365714678326002349 35625099512143004372250881)
    ·
      refine ⟨26718824634107253279188161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35625099512143004372250881 26718824634107253279188161)
      ·
        refine ⟨20039118475580439959391121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26718824634107253279188161 20039118475580439959391121)
        ·
          refine ⟨15029338856685329969543341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20039118475580439959391121 15029338856685329969543341)
          ·
            refine ⟨5636002071256998738578753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15029338856685329969543341 5636002071256998738578753)
            ·
              refine ⟨4227001553442749053934065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5636002071256998738578753 4227001553442749053934065)
              ·
                refine ⟨3170251165082061790450549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4227001553442749053934065 3170251165082061790450549)
                ·
                  refine ⟨297211046726443292854739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3170251165082061790450549 297211046726443292854739)
                  ·
                    rfl

theorem cell23_5209348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_5209348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209348 prefixEnd_5209348 := by exact prefixLift 5209348
  have htrace : WordTrace (prefixWord ++ tailWord_5209348) baseStart_5209348 baseEnd_5209348 := by
    simpa [prefixWord, tailWord_5209348, baseEnd_5209348] using wordTrace_append hprefix tailTrace_5209348
  have hstable : (prefixWord ++ tailWord_5209348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209348).length < 2 ^ (prefixWord ++ tailWord_5209348).sum := by decide
  have hdescent : baseEnd_5209348 < baseStart_5209348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209378 : List Nat := [3, 3, 1, 1, 5, 1, 1, 1, 2, 5]
def baseStart_5209378 : Nat := 118140960795 + 5209378 * 2 ^ 59
def prefixEnd_5209378 : Nat := 4983230072969 + 3 ^ 40 * 5209378 * 2
def baseEnd_5209378 : Nat := 891638274985874839439171

theorem tailTrace_5209378 : CollatzResearch.WordTrace tailWord_5209378 prefixEnd_5209378 891638274985874839439171 := by
  unfold tailWord_5209378
  simp only [CollatzResearch.WordTrace]
  refine ⟨47500406230330167943899197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126667749947547114517064525 47500406230330167943899197)
  ·
    refine ⟨17812652336373812978962199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47500406230330167943899197 17812652336373812978962199)
    ·
      refine ⟨26718978504560719468443299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17812652336373812978962199 26718978504560719468443299)
      ·
        refine ⟨40078467756841079202664949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26718978504560719468443299 40078467756841079202664949)
        ·
          refine ⟨3757356352203851175249839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40078467756841079202664949 3757356352203851175249839)
          ·
            refine ⟨5636034528305776762874759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3757356352203851175249839 5636034528305776762874759)
            ·
              refine ⟨8454051792458665144312139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5636034528305776762874759 8454051792458665144312139)
              ·
                refine ⟨12681077688687997716468209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8454051792458665144312139 12681077688687997716468209)
                ·
                  refine ⟨9510808266515998287351157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12681077688687997716468209 9510808266515998287351157)
                  ·
                    refine ⟨891638274985874839439171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9510808266515998287351157 891638274985874839439171)
                    ·
                      rfl

theorem cell23_5209378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_5209378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209378 prefixEnd_5209378 := by exact prefixLift 5209378
  have htrace : WordTrace (prefixWord ++ tailWord_5209378) baseStart_5209378 baseEnd_5209378 := by
    simpa [prefixWord, tailWord_5209378, baseEnd_5209378] using wordTrace_append hprefix tailTrace_5209378
  have hstable : (prefixWord ++ tailWord_5209378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209378).length < 2 ^ (prefixWord ++ tailWord_5209378).sum := by decide
  have hdescent : baseEnd_5209378 < baseStart_5209378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209381 : List Nat := [1, 3, 1, 2, 4, 3, 1, 1, 2, 1, 4]
def baseStart_5209381 : Nat := 118140960795 + 5209381 * 2 ^ 59
def prefixEnd_5209381 : Nat := 4983230072969 + 3 ^ 40 * 5209381 * 2
def baseEnd_5209381 : Nat := 2674916365399588006579999

theorem tailTrace_5209381 : CollatzResearch.WordTrace tailWord_5209381 prefixEnd_5209381 2674916365399588006579999 := by
  unfold tailWord_5209381
  simp only [CollatzResearch.WordTrace]
  refine ⟨190001734340309803287955997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126667822893539868858637331 190001734340309803287955997)
  ·
    refine ⟨71250650377616176232983499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190001734340309803287955997 71250650377616176232983499)
    ·
      refine ⟨106875975566424264349475249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71250650377616176232983499 106875975566424264349475249)
      ·
        refine ⟨80156981674818198262106437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106875975566424264349475249 80156981674818198262106437)
        ·
          refine ⟨15029434064028412174144957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80156981674818198262106437 15029434064028412174144957)
          ·
            refine ⟨5636037774010654565304359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15029434064028412174144957 5636037774010654565304359)
            ·
              refine ⟨8454056661015981847956539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5636037774010654565304359 8454056661015981847956539)
              ·
                refine ⟨12681084991523972771934809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8454056661015981847956539 12681084991523972771934809)
                ·
                  refine ⟨9510813743642979578951107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12681084991523972771934809 9510813743642979578951107)
                  ·
                    refine ⟨14266220615464469368426661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9510813743642979578951107 14266220615464469368426661)
                    ·
                      refine ⟨2674916365399588006579999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14266220615464469368426661 2674916365399588006579999)
                      ·
                        rfl

theorem cell23_5209381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_5209381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209381 prefixEnd_5209381 := by exact prefixLift 5209381
  have htrace : WordTrace (prefixWord ++ tailWord_5209381) baseStart_5209381 baseEnd_5209381 := by
    simpa [prefixWord, tailWord_5209381, baseEnd_5209381] using wordTrace_append hprefix tailTrace_5209381
  have hstable : (prefixWord ++ tailWord_5209381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209381).length < 2 ^ (prefixWord ++ tailWord_5209381).sum := by decide
  have hdescent : baseEnd_5209381 < baseStart_5209381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209404 : List Nat := [2, 2, 2, 2, 1, 3, 3, 2, 6]
def baseStart_5209404 : Nat := 118140960795 + 5209404 * 2 ^ 59
def prefixEnd_5209404 : Nat := 4983230072969 + 3 ^ 40 * 5209404 * 2
def baseEnd_5209404 : Nat := 297214241717182379621377

theorem tailTrace_5209404 : CollatzResearch.WordTrace tailWord_5209404 prefixEnd_5209404 297214241717182379621377 := by
  unfold tailWord_5209404
  simp only [CollatzResearch.WordTrace]
  refine ⟨95001286609613239108021633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126668382146150985477362177 95001286609613239108021633)
  ·
    refine ⟨71250964957209929331016225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95001286609613239108021633 71250964957209929331016225)
    ·
      refine ⟨53438223717907446998262169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71250964957209929331016225 53438223717907446998262169)
      ·
        refine ⟨40078667788430585248696627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53438223717907446998262169 40078667788430585248696627)
        ·
          refine ⟨60118001682645877873044941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40078667788430585248696627 60118001682645877873044941)
          ·
            refine ⟨22544250630992204202391853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60118001682645877873044941 22544250630992204202391853)
            ·
              refine ⟨8454093986622076575896945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22544250630992204202391853 8454093986622076575896945)
              ·
                refine ⟨6340570489966557431922709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8454093986622076575896945 6340570489966557431922709)
                ·
                  refine ⟨297214241717182379621377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6340570489966557431922709 297214241717182379621377)
                  ·
                    rfl

theorem cell23_5209404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 6].length) (baseStart_5209404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209404 prefixEnd_5209404 := by exact prefixLift 5209404
  have htrace : WordTrace (prefixWord ++ tailWord_5209404) baseStart_5209404 baseEnd_5209404 := by
    simpa [prefixWord, tailWord_5209404, baseEnd_5209404] using wordTrace_append hprefix tailTrace_5209404
  have hstable : (prefixWord ++ tailWord_5209404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209404).length < 2 ^ (prefixWord ++ tailWord_5209404).sum := by decide
  have hdescent : baseEnd_5209404 < baseStart_5209404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209407 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 6]
def baseStart_5209407 : Nat := 118140960795 + 5209407 * 2 ^ 59
def prefixEnd_5209407 : Nat := 4983230072969 + 3 ^ 40 * 5209407 * 2
def baseEnd_5209407 : Nat := 2674929715896604904854879

theorem tailTrace_5209407 : CollatzResearch.WordTrace tailWord_5209407 prefixEnd_5209407 2674929715896604904854879 := by
  unfold tailWord_5209407
  simp only [CollatzResearch.WordTrace]
  refine ⟨190002682638215609728402475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126668455092143739818934983 190002682638215609728402475)
  ·
    refine ⟨285004023957323414592603713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190002682638215609728402475 285004023957323414592603713)
    ·
      refine ⟨213753017967992560944452785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285004023957323414592603713 213753017967992560944452785)
      ·
        refine ⟨160314763475994420708339589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213753017967992560944452785 160314763475994420708339589)
        ·
          refine ⟨30059018151748953882813673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160314763475994420708339589 30059018151748953882813673)
          ·
            refine ⟨22544263613811715412110255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30059018151748953882813673 22544263613811715412110255)
            ·
              refine ⟨33816395420717573118165383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22544263613811715412110255 33816395420717573118165383)
              ·
                refine ⟨50724593131076359677248075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33816395420717573118165383 50724593131076359677248075)
                ·
                  refine ⟨76086889696614539515872113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50724593131076359677248075 76086889696614539515872113)
                  ·
                    refine ⟨57065167272460904636904085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76086889696614539515872113 57065167272460904636904085)
                    ·
                      refine ⟨2674929715896604904854879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57065167272460904636904085 2674929715896604904854879)
                      ·
                        rfl

theorem cell23_5209407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_5209407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209407 prefixEnd_5209407 := by exact prefixLift 5209407
  have htrace : WordTrace (prefixWord ++ tailWord_5209407) baseStart_5209407 baseEnd_5209407 := by
    simpa [prefixWord, tailWord_5209407, baseEnd_5209407] using wordTrace_append hprefix tailTrace_5209407
  have hstable : (prefixWord ++ tailWord_5209407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209407).length < 2 ^ (prefixWord ++ tailWord_5209407).sum := by decide
  have hdescent : baseEnd_5209407 < baseStart_5209407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209417 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 5, 5]
def baseStart_5209417 : Nat := 118140960795 + 5209417 * 2 ^ 59
def prefixEnd_5209417 : Nat := 4983230072969 + 3 ^ 40 * 5209417 * 2
def baseEnd_5209417 : Nat := 891644950234383288576611

theorem tailTrace_5209417 : CollatzResearch.WordTrace tailWord_5209417 prefixEnd_5209417 891644950234383288576611 := by
  unfold tailWord_5209417
  simp only [CollatzResearch.WordTrace]
  refine ⟨190003047368179381436266505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126668698245452920957511003 190003047368179381436266505)
  ·
    refine ⟨142502285526134536077199879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190003047368179381436266505 142502285526134536077199879)
    ·
      refine ⟨213753428289201804115799819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142502285526134536077199879 213753428289201804115799819)
      ·
        refine ⟨320630142433802706173699729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213753428289201804115799819 320630142433802706173699729)
        ·
          refine ⟨240472606825352029630274797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320630142433802706173699729 240472606825352029630274797)
          ·
            refine ⟨90177227559507011111353049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240472606825352029630274797 90177227559507011111353049)
            ·
              refine ⟨67632920669630258333514787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90177227559507011111353049 67632920669630258333514787)
              ·
                refine ⟨101449381004445387500272181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67632920669630258333514787 101449381004445387500272181)
                ·
                  refine ⟨9510879469166755078150517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101449381004445387500272181 9510879469166755078150517)
                  ·
                    refine ⟨891644950234383288576611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9510879469166755078150517 891644950234383288576611)
                    ·
                      rfl

theorem cell23_5209417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 5].length) (baseStart_5209417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209417 prefixEnd_5209417 := by exact prefixLift 5209417
  have htrace : WordTrace (prefixWord ++ tailWord_5209417) baseStart_5209417 baseEnd_5209417 := by
    simpa [prefixWord, tailWord_5209417, baseEnd_5209417] using wordTrace_append hprefix tailTrace_5209417
  have hstable : (prefixWord ++ tailWord_5209417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209417).length < 2 ^ (prefixWord ++ tailWord_5209417).sum := by decide
  have hdescent : baseEnd_5209417 < baseStart_5209417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209424 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 3, 5, 2]
def baseStart_5209424 : Nat := 118140960795 + 5209424 * 2 ^ 59
def prefixEnd_5209424 : Nat := 4983230072969 + 3 ^ 40 * 5209424 * 2
def baseEnd_5209424 : Nat := 2674938445067731338342301

theorem tailTrace_5209424 : CollatzResearch.WordTrace tailWord_5209424 prefixEnd_5209424 2674938445067731338342301 := by
  unfold tailWord_5209424
  simp only [CollatzResearch.WordTrace]
  refine ⟨95001651339577010815885663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126668868452769347754514217 95001651339577010815885663)
  ·
    refine ⟨142502477009365516223828495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95001651339577010815885663 142502477009365516223828495)
    ·
      refine ⟨213753715514048274335742743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142502477009365516223828495 213753715514048274335742743)
      ·
        refine ⟨320630573271072411503614115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213753715514048274335742743 320630573271072411503614115)
        ·
          refine ⟨480945859906608617255421173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320630573271072411503614115 480945859906608617255421173)
          ·
            refine ⟨45088674366244557867695735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 480945859906608617255421173 45088674366244557867695735)
            ·
              refine ⟨67633011549366836801543603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45088674366244557867695735 67633011549366836801543603)
              ·
                refine ⟨101449517324050255202315405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67633011549366836801543603 101449517324050255202315405)
                ·
                  refine ⟨38043568996518845700868277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101449517324050255202315405 38043568996518845700868277)
                  ·
                    refine ⟨3566584593423641784456401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38043568996518845700868277 3566584593423641784456401)
                    ·
                      refine ⟨2674938445067731338342301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3566584593423641784456401 2674938445067731338342301)
                      ·
                        rfl

theorem cell23_5209424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 3, 5, 2].length) (baseStart_5209424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209424 prefixEnd_5209424 := by exact prefixLift 5209424
  have htrace : WordTrace (prefixWord ++ tailWord_5209424) baseStart_5209424 baseEnd_5209424 := by
    simpa [prefixWord, tailWord_5209424, baseEnd_5209424] using wordTrace_append hprefix tailTrace_5209424
  have hstable : (prefixWord ++ tailWord_5209424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209424).length < 2 ^ (prefixWord ++ tailWord_5209424).sum := by decide
  have hdescent : baseEnd_5209424 < baseStart_5209424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209431 : List Nat := [1, 1, 3, 2, 3, 2, 2, 2, 3, 1, 3]
def baseStart_5209431 : Nat := 118140960795 + 5209431 * 2 ^ 59
def prefixEnd_5209431 : Nat := 4983230072969 + 3 ^ 40 * 5209431 * 2
def baseEnd_5209431 : Nat := 2674942039432312810954769

theorem tailTrace_5209431 : CollatzResearch.WordTrace tailWord_5209431 prefixEnd_5209431 2674942039432312810954769 := by
  unfold tailWord_5209431
  simp only [CollatzResearch.WordTrace]
  refine ⟨190003557990128661827276147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126669038660085774551517431 190003557990128661827276147)
  ·
    refine ⟨285005336985192992740914221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190003557990128661827276147 285005336985192992740914221)
    ·
      refine ⟨106877001369447372277842833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285005336985192992740914221 106877001369447372277842833)
      ·
        refine ⟨80157751027085529208382125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106877001369447372277842833 80157751027085529208382125)
        ·
          refine ⟨30059156635157073453143297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80157751027085529208382125 30059156635157073453143297)
          ·
            refine ⟨22544367476367805089857473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30059156635157073453143297 22544367476367805089857473)
            ·
              refine ⟨16908275607275853817393105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22544367476367805089857473 16908275607275853817393105)
              ·
                refine ⟨12681206705456890363044829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16908275607275853817393105 12681206705456890363044829)
                ·
                  refine ⟨4755452514546333886141811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12681206705456890363044829 4755452514546333886141811)
                  ·
                    refine ⟨7133178771819500829212717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4755452514546333886141811 7133178771819500829212717)
                    ·
                      refine ⟨2674942039432312810954769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7133178771819500829212717 2674942039432312810954769)
                      ·
                        rfl

theorem cell23_5209431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_5209431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209431 prefixEnd_5209431 := by exact prefixLift 5209431
  have htrace : WordTrace (prefixWord ++ tailWord_5209431) baseStart_5209431 baseEnd_5209431 := by
    simpa [prefixWord, tailWord_5209431, baseEnd_5209431] using wordTrace_append hprefix tailTrace_5209431
  have hstable : (prefixWord ++ tailWord_5209431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209431).length < 2 ^ (prefixWord ++ tailWord_5209431).sum := by decide
  have hdescent : baseEnd_5209431 < baseStart_5209431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209434 : List Nat := [3, 1, 1, 2, 1, 2, 3, 4, 1, 5]
def baseStart_5209434 : Nat := 118140960795 + 5209434 * 2 ^ 59
def prefixEnd_5209434 : Nat := 4983230072969 + 3 ^ 40 * 5209434 * 2
def baseEnd_5209434 : Nat := 891647859958092099739085

theorem tailTrace_5209434 : CollatzResearch.WordTrace tailWord_5209434 prefixEnd_5209434 891647859958092099739085 := by
  unfold tailWord_5209434
  simp only [CollatzResearch.WordTrace]
  refine ⟨47500916852279448334908839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126669111606078528893090237 47500916852279448334908839)
  ·
    refine ⟨71251375278419172502363259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47500916852279448334908839 71251375278419172502363259)
    ·
      refine ⟨106877062917628758753544889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71251375278419172502363259 106877062917628758753544889)
      ·
        refine ⟨80157797188221569065158667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106877062917628758753544889 80157797188221569065158667)
        ·
          refine ⟨120236695782332353597738001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80157797188221569065158667 120236695782332353597738001)
          ·
            refine ⟨90177521836749265198303501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120236695782332353597738001 90177521836749265198303501)
            ·
              refine ⟨33816570688780974449363813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90177521836749265198303501 33816570688780974449363813)
              ·
                refine ⟨6340607004146432709255715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33816570688780974449363813 6340607004146432709255715)
                ·
                  refine ⟨9510910506219649063883573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6340607004146432709255715 9510910506219649063883573)
                  ·
                    refine ⟨891647859958092099739085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9510910506219649063883573 891647859958092099739085)
                    ·
                      rfl

theorem cell23_5209434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 1, 5].length) (baseStart_5209434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209434 prefixEnd_5209434 := by exact prefixLift 5209434
  have htrace : WordTrace (prefixWord ++ tailWord_5209434) baseStart_5209434 baseEnd_5209434 := by
    simpa [prefixWord, tailWord_5209434, baseEnd_5209434] using wordTrace_append hprefix tailTrace_5209434
  have hstable : (prefixWord ++ tailWord_5209434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209434).length < 2 ^ (prefixWord ++ tailWord_5209434).sum := by decide
  have hdescent : baseEnd_5209434 < baseStart_5209434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209467 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 6]
def baseStart_5209467 : Nat := 118140960795 + 5209467 * 2 ^ 59
def prefixEnd_5209467 : Nat := 4983230072969 + 3 ^ 40 * 5209467 * 2
def baseEnd_5209467 : Nat := 2674960524735874670104603

theorem tailTrace_5209467 : CollatzResearch.WordTrace tailWord_5209467 prefixEnd_5209467 2674960524735874670104603 := by
  unfold tailWord_5209467
  simp only [CollatzResearch.WordTrace]
  refine ⟨190004871017998239975586655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126669914011998826650391103 190004871017998239975586655)
  ·
    refine ⟨285007306526997359963379983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190004871017998239975586655 285007306526997359963379983)
    ·
      refine ⟨427510959790496039945069975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285007306526997359963379983 427510959790496039945069975)
      ·
        refine ⟨641266439685744059917604963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427510959790496039945069975 641266439685744059917604963)
        ·
          refine ⟨961899659528616089876407445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 641266439685744059917604963 961899659528616089876407445)
          ·
            refine ⟨45089046540403879212956599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 961899659528616089876407445 45089046540403879212956599)
            ·
              refine ⟨67633569810605818819434899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45089046540403879212956599 67633569810605818819434899)
              ·
                refine ⟨101450354715908728229152349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67633569810605818819434899 101450354715908728229152349)
                ·
                  refine ⟨38043883018465773085932131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101450354715908728229152349 38043883018465773085932131)
                  ·
                    refine ⟨57065824527698659628898197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38043883018465773085932131 57065824527698659628898197)
                    ·
                      refine ⟨2674960524735874670104603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57065824527698659628898197 2674960524735874670104603)
                      ·
                        rfl

theorem cell23_5209467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 6].length) (baseStart_5209467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209467 prefixEnd_5209467 := by exact prefixLift 5209467
  have htrace : WordTrace (prefixWord ++ tailWord_5209467) baseStart_5209467 baseEnd_5209467 := by
    simpa [prefixWord, tailWord_5209467, baseEnd_5209467] using wordTrace_append hprefix tailTrace_5209467
  have hstable : (prefixWord ++ tailWord_5209467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209467).length < 2 ^ (prefixWord ++ tailWord_5209467).sum := by decide
  have hdescent : baseEnd_5209467 < baseStart_5209467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209477 : List Nat := [1, 3, 1, 1, 3, 1, 3, 10]
def baseStart_5209477 : Nat := 118140960795 + 5209477 * 2 ^ 59
def prefixEnd_5209477 : Nat := 4983230072969 + 3 ^ 40 * 5209477 * 2
def baseEnd_5209477 : Nat := 99072802205274801147391

theorem tailTrace_5209477 : CollatzResearch.WordTrace tailWord_5209477 prefixEnd_5209477 99072802205274801147391 := by
  unfold tailWord_5209477
  simp only [CollatzResearch.WordTrace]
  refine ⟨190005235747962011683450685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126670157165308007788967123 190005235747962011683450685)
  ·
    refine ⟨71251963405485754381294007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190005235747962011683450685 71251963405485754381294007)
    ·
      refine ⟨106877945108228631571941011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71251963405485754381294007 106877945108228631571941011)
      ·
        refine ⟨160316917662342947357911517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106877945108228631571941011 160316917662342947357911517)
        ·
          refine ⟨60118844123378605259216819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160316917662342947357911517 60118844123378605259216819)
          ·
            refine ⟨90178266185067907888825229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60118844123378605259216819 90178266185067907888825229)
            ·
              refine ⟨33816849819400465458309461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90178266185067907888825229 33816849819400465458309461)
              ·
                refine ⟨99072802205274801147391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33816849819400465458309461 99072802205274801147391)
                ·
                  rfl

theorem cell23_5209477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 10].length) (baseStart_5209477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209477 prefixEnd_5209477 := by exact prefixLift 5209477
  have htrace : WordTrace (prefixWord ++ tailWord_5209477) baseStart_5209477 baseEnd_5209477 := by
    simpa [prefixWord, tailWord_5209477, baseEnd_5209477] using wordTrace_append hprefix tailTrace_5209477
  have hstable : (prefixWord ++ tailWord_5209477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209477).length < 2 ^ (prefixWord ++ tailWord_5209477).sum := by decide
  have hdescent : baseEnd_5209477 < baseStart_5209477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209484 : List Nat := [2, 2, 1, 2, 1, 3, 2, 3, 1, 2, 4]
def baseStart_5209484 : Nat := 118140960795 + 5209484 * 2 ^ 59
def prefixEnd_5209484 : Nat := 4983230072969 + 3 ^ 40 * 5209484 * 2
def baseEnd_5209484 : Nat := 2674969253907001103592025

theorem tailTrace_5209484 : CollatzResearch.WordTrace tailWord_5209484 prefixEnd_5209484 2674969253907001103592025 := by
  unfold tailWord_5209484
  simp only [CollatzResearch.WordTrace]
  refine ⟨95002745529468325939477753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126670327372624434585970337 95002745529468325939477753)
  ·
    refine ⟨71252059147101244454608315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95002745529468325939477753 71252059147101244454608315)
    ·
      refine ⟨106878088720651866681912473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71252059147101244454608315 106878088720651866681912473)
      ·
        refine ⟨80158566540488900011434355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106878088720651866681912473 80158566540488900011434355)
        ·
          refine ⟨120237849810733350017151533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80158566540488900011434355 120237849810733350017151533)
          ·
            refine ⟨45089193679025006256431825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120237849810733350017151533 45089193679025006256431825)
            ·
              refine ⟨33816895259268754692323869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45089193679025006256431825 33816895259268754692323869)
              ·
                refine ⟨12681335722225783009621451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33816895259268754692323869 12681335722225783009621451)
                ·
                  refine ⟨19022003583338674514432177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12681335722225783009621451 19022003583338674514432177)
                  ·
                    refine ⟨14266502687504005885824133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19022003583338674514432177 14266502687504005885824133)
                    ·
                      refine ⟨2674969253907001103592025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14266502687504005885824133 2674969253907001103592025)
                      ·
                        rfl

theorem cell23_5209484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_5209484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209484 prefixEnd_5209484 := by exact prefixLift 5209484
  have htrace : WordTrace (prefixWord ++ tailWord_5209484) baseStart_5209484 baseEnd_5209484 := by
    simpa [prefixWord, tailWord_5209484, baseEnd_5209484] using wordTrace_append hprefix tailTrace_5209484
  have hstable : (prefixWord ++ tailWord_5209484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209484).length < 2 ^ (prefixWord ++ tailWord_5209484).sum := by decide
  have hdescent : baseEnd_5209484 < baseStart_5209484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209501 : List Nat := [1, 4, 2, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_5209501 : Nat := 118140960795 + 5209501 * 2 ^ 59
def prefixEnd_5209501 : Nat := 4983230072969 + 3 ^ 40 * 5209501 * 2
def baseEnd_5209501 : Nat := 2674977983078127537079447

theorem tailTrace_5209501 : CollatzResearch.WordTrace tailWord_5209501 prefixEnd_5209501 2674977983078127537079447 := by
  unfold tailWord_5209501
  simp only [CollatzResearch.WordTrace]
  refine ⟨190006111099875063782324357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126670740733250042521549571 190006111099875063782324357)
  ·
    refine ⟨35626145831226574459185817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190006111099875063782324357 35626145831226574459185817)
    ·
      refine ⟨26719609373419930844389363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35626145831226574459185817 26719609373419930844389363)
      ·
        refine ⟨40079414060129896266584045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26719609373419930844389363 40079414060129896266584045)
        ·
          refine ⟨15029780272548711099969017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40079414060129896266584045 15029780272548711099969017)
          ·
            refine ⟨11272335204411533324976763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15029780272548711099969017 11272335204411533324976763)
            ·
              refine ⟨16908502806617299987465145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11272335204411533324976763 16908502806617299987465145)
              ·
                refine ⟨12681377104962974990598859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16908502806617299987465145 12681377104962974990598859)
                ·
                  refine ⟨19022065657444462485898289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12681377104962974990598859 19022065657444462485898289)
                  ·
                    refine ⟨14266549243083346864423717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19022065657444462485898289 14266549243083346864423717)
                    ·
                      refine ⟨2674977983078127537079447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14266549243083346864423717 2674977983078127537079447)
                      ·
                        rfl

theorem cell23_5209501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_5209501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209501 prefixEnd_5209501 := by exact prefixLift 5209501
  have htrace : WordTrace (prefixWord ++ tailWord_5209501) baseStart_5209501 baseEnd_5209501 := by
    simpa [prefixWord, tailWord_5209501, baseEnd_5209501] using wordTrace_append hprefix tailTrace_5209501
  have hstable : (prefixWord ++ tailWord_5209501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209501).length < 2 ^ (prefixWord ++ tailWord_5209501).sum := by decide
  have hdescent : baseEnd_5209501 < baseStart_5209501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209534 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_5209534 : Nat := 118140960795 + 5209534 * 2 ^ 59
def prefixEnd_5209534 : Nat := 4983230072969 + 3 ^ 40 * 5209534 * 2
def baseEnd_5209534 : Nat := 2674994927939725907966795

theorem tailTrace_5209534 : CollatzResearch.WordTrace tailWord_5209534 prefixEnd_5209534 2674994927939725907966795 := by
  unfold tailWord_5209534
  simp only [CollatzResearch.WordTrace]
  refine ⟨23750914338594438802284457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126671543139170340278850437 23750914338594438802284457)
  ·
    refine ⟨17813185753945829101713343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23750914338594438802284457 17813185753945829101713343)
    ·
      refine ⟨26719778630918743652570015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17813185753945829101713343 26719778630918743652570015)
      ·
        refine ⟨40079667946378115478855023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26719778630918743652570015 40079667946378115478855023)
        ·
          refine ⟨60119501919567173218282535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40079667946378115478855023 60119501919567173218282535)
          ·
            refine ⟨90179252879350759827423803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60119501919567173218282535 90179252879350759827423803)
            ·
              refine ⟨135268879319026139741135705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90179252879350759827423803 135268879319026139741135705)
              ·
                refine ⟨101451659489269604805851779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135268879319026139741135705 101451659489269604805851779)
                ·
                  refine ⟨152177489233904407208777669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101451659489269604805851779 152177489233904407208777669)
                  ·
                    refine ⟨28533279231357076351645813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 152177489233904407208777669 28533279231357076351645813)
                    ·
                      refine ⟨2674994927939725907966795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28533279231357076351645813 2674994927939725907966795)
                      ·
                        rfl

theorem cell23_5209534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_5209534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209534 prefixEnd_5209534 := by exact prefixLift 5209534
  have htrace : WordTrace (prefixWord ++ tailWord_5209534) baseStart_5209534 baseEnd_5209534 := by
    simpa [prefixWord, tailWord_5209534, baseEnd_5209534] using wordTrace_append hprefix tailTrace_5209534
  have hstable : (prefixWord ++ tailWord_5209534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209534).length < 2 ^ (prefixWord ++ tailWord_5209534).sum := by decide
  have hdescent : baseEnd_5209534 < baseStart_5209534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209544 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 2, 3, 4]
def baseStart_5209544 : Nat := 118140960795 + 5209544 * 2 ^ 59
def prefixEnd_5209544 : Nat := 4983230072969 + 3 ^ 40 * 5209544 * 2
def baseEnd_5209544 : Nat := 2675000062746270868841749

theorem tailTrace_5209544 : CollatzResearch.WordTrace tailWord_5209544 prefixEnd_5209544 2675000062746270868841749 := by
  unfold tailWord_5209544
  simp only [CollatzResearch.WordTrace]
  refine ⟨95003839719359641063069843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126671786292479521417426457 95003839719359641063069843)
  ·
    refine ⟨142505759579039461594604765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95003839719359641063069843 142505759579039461594604765)
    ·
      refine ⟨53439659842139798097976787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142505759579039461594604765 53439659842139798097976787)
      ·
        refine ⟨80159489763209697146965181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53439659842139798097976787 80159489763209697146965181)
        ·
          refine ⟨30059808661203636430111943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80159489763209697146965181 30059808661203636430111943)
          ·
            refine ⟨45089712991805454645167915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30059808661203636430111943 45089712991805454645167915)
            ·
              refine ⟨67634569487708181967751873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45089712991805454645167915 67634569487708181967751873)
              ·
                refine ⟨50725927115781136475813905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67634569487708181967751873 50725927115781136475813905)
                ·
                  refine ⟨38044445336835852356860429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50725927115781136475813905 38044445336835852356860429)
                  ·
                    refine ⟨14266667001313444633822661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38044445336835852356860429 14266667001313444633822661)
                    ·
                      refine ⟨2675000062746270868841749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14266667001313444633822661 2675000062746270868841749)
                      ·
                        rfl

theorem cell23_5209544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_5209544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209544 prefixEnd_5209544 := by exact prefixLift 5209544
  have htrace : WordTrace (prefixWord ++ tailWord_5209544) baseStart_5209544 baseEnd_5209544 := by
    simpa [prefixWord, tailWord_5209544, baseEnd_5209544] using wordTrace_append hprefix tailTrace_5209544
  have hstable : (prefixWord ++ tailWord_5209544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209544).length < 2 ^ (prefixWord ++ tailWord_5209544).sum := by decide
  have hdescent : baseEnd_5209544 < baseStart_5209544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209548 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 3, 3, 2]
def baseStart_5209548 : Nat := 118140960795 + 5209548 * 2 ^ 59
def prefixEnd_5209548 : Nat := 4983230072969 + 3 ^ 40 * 5209548 * 2
def baseEnd_5209548 : Nat := 2675002116668888853191731

theorem tailTrace_5209548 : CollatzResearch.WordTrace tailWord_5209548 prefixEnd_5209548 2675002116668888853191731 := by
  unfold tailWord_5209548
  simp only [CollatzResearch.WordTrace]
  refine ⟨95003912665352395404642649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126671883553803193872856865 95003912665352395404642649)
  ·
    refine ⟨71252934499014296553481987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95003912665352395404642649 71252934499014296553481987)
    ·
      refine ⟨106879401748521444830222981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71252934499014296553481987 106879401748521444830222981)
      ·
        refine ⟨20039887827847770905666809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106879401748521444830222981 20039887827847770905666809)
        ·
          refine ⟨15029915870885828179250107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20039887827847770905666809 15029915870885828179250107)
          ·
            refine ⟨22544873806328742268875161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15029915870885828179250107 22544873806328742268875161)
            ·
              refine ⟨16908655354746556701656371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22544873806328742268875161 16908655354746556701656371)
              ·
                refine ⟨25362983032119835052484557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16908655354746556701656371 25362983032119835052484557)
                ·
                  refine ⟨9511118637044938144681709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25362983032119835052484557 9511118637044938144681709)
                  ·
                    refine ⟨3566669488891851804255641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9511118637044938144681709 3566669488891851804255641)
                    ·
                      refine ⟨2675002116668888853191731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3566669488891851804255641 2675002116668888853191731)
                      ·
                        rfl

theorem cell23_5209548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_5209548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209548 prefixEnd_5209548 := by exact prefixLift 5209548
  have htrace : WordTrace (prefixWord ++ tailWord_5209548) baseStart_5209548 baseEnd_5209548 := by
    simpa [prefixWord, tailWord_5209548, baseEnd_5209548] using wordTrace_append hprefix tailTrace_5209548
  have hstable : (prefixWord ++ tailWord_5209548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209548).length < 2 ^ (prefixWord ++ tailWord_5209548).sum := by decide
  have hdescent : baseEnd_5209548 < baseStart_5209548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209565 : List Nat := [1, 4, 3, 1, 1, 3, 1, 3, 1, 3, 2]
def baseStart_5209565 : Nat := 118140960795 + 5209565 * 2 ^ 59
def prefixEnd_5209565 : Nat := 4983230072969 + 3 ^ 40 * 5209565 * 2
def baseEnd_5209565 : Nat := 2675010845840015286679153

theorem tailTrace_5209565 : CollatzResearch.WordTrace tailWord_5209565 prefixEnd_5209565 2675010845840015286679153 := by
  unfold tailWord_5209565
  simp only [CollatzResearch.WordTrace]
  refine ⟨190008445371643202712654149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126672296914428801808436099 190008445371643202712654149)
  ·
    refine ⟨35626583507183100508622653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190008445371643202712654149 35626583507183100508622653)
    ·
      refine ⟨13359968815193662690733495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35626583507183100508622653 13359968815193662690733495)
      ·
        refine ⟨20039953222790494036100243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13359968815193662690733495 20039953222790494036100243)
        ·
          refine ⟨30059929834185741054150365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20039953222790494036100243 30059929834185741054150365)
          ·
            refine ⟨11272473687819652895306387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30059929834185741054150365 11272473687819652895306387)
            ·
              refine ⟨16908710531729479342959581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11272473687819652895306387 16908710531729479342959581)
              ·
                refine ⟨6340766449398554753609843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16908710531729479342959581 6340766449398554753609843)
                ·
                  refine ⟨9511149674097832130414765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6340766449398554753609843 9511149674097832130414765)
                  ·
                    refine ⟨3566681127786687048905537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9511149674097832130414765 3566681127786687048905537)
                    ·
                      refine ⟨2675010845840015286679153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3566681127786687048905537 2675010845840015286679153)
                      ·
                        rfl

theorem cell23_5209565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_5209565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209565 prefixEnd_5209565 := by exact prefixLift 5209565
  have htrace : WordTrace (prefixWord ++ tailWord_5209565) baseStart_5209565 baseEnd_5209565 := by
    simpa [prefixWord, tailWord_5209565, baseEnd_5209565] using wordTrace_append hprefix tailTrace_5209565
  have hstable : (prefixWord ++ tailWord_5209565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209565).length < 2 ^ (prefixWord ++ tailWord_5209565).sum := by decide
  have hdescent : baseEnd_5209565 < baseStart_5209565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209584 : List Nat := [2, 1, 1, 1, 3, 4, 1, 3, 7]
def baseStart_5209584 : Nat := 118140960795 + 5209584 * 2 ^ 59
def prefixEnd_5209584 : Nat := 4983230072969 + 3 ^ 40 * 5209584 * 2
def baseEnd_5209584 : Nat := 297224511330272301371285

theorem tailTrace_5209584 : CollatzResearch.WordTrace tailWord_5209584 prefixEnd_5209584 297224511330272301371285 := by
  unfold tailWord_5209584
  simp only [CollatzResearch.WordTrace]
  refine ⟨95004569179287184478797903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126672758905716245971730537 95004569179287184478797903)
  ·
    refine ⟨142506853768930776718196855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95004569179287184478797903 142506853768930776718196855)
    ·
      refine ⟨213760280653396165077295283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142506853768930776718196855 213760280653396165077295283)
      ·
        refine ⟨320640420980094247615942925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213760280653396165077295283 320640420980094247615942925)
        ·
          refine ⟨120240157867535342855978597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320640420980094247615942925 120240157867535342855978597)
          ·
            refine ⟨22545029600162876785495987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120240157867535342855978597 22545029600162876785495987)
            ·
              refine ⟨33817544400244315178243981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22545029600162876785495987 33817544400244315178243981)
              ·
                refine ⟨12681579150091618191841493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33817544400244315178243981 12681579150091618191841493)
                ·
                  refine ⟨297224511330272301371285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12681579150091618191841493 297224511330272301371285)
                  ·
                    rfl

theorem cell23_5209584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 7].length) (baseStart_5209584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209584 prefixEnd_5209584 := by exact prefixLift 5209584
  have htrace : WordTrace (prefixWord ++ tailWord_5209584) baseStart_5209584 baseEnd_5209584 := by
    simpa [prefixWord, tailWord_5209584, baseEnd_5209584] using wordTrace_append hprefix tailTrace_5209584
  have hstable : (prefixWord ++ tailWord_5209584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209584).length < 2 ^ (prefixWord ++ tailWord_5209584).sum := by decide
  have hdescent : baseEnd_5209584 < baseStart_5209584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209635 : List Nat := [1, 1, 1, 4, 5, 1, 3, 2, 5]
def baseStart_5209635 : Nat := 118140960795 + 5209635 * 2 ^ 59
def prefixEnd_5209635 : Nat := 4983230072969 + 3 ^ 40 * 5209635 * 2
def baseEnd_5209635 : Nat := 297227421053981112533759

theorem tailTrace_5209635 : CollatzResearch.WordTrace tailWord_5209635 prefixEnd_5209635 297227421053981112533759 := by
  unfold tailWord_5209635
  simp only [CollatzResearch.WordTrace]
  refine ⟨190010998481389604667702359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126673998987593069778468239 190010998481389604667702359)
  ·
    refine ⟨285016497722084407001553539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190010998481389604667702359 285016497722084407001553539)
    ·
      refine ⟨427524746583126610502330309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285016497722084407001553539 427524746583126610502330309)
      ·
        refine ⟨80160889984336239469186933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 427524746583126610502330309 80160889984336239469186933)
        ·
          refine ⟨7515083436031522450236275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80160889984336239469186933 7515083436031522450236275)
          ·
            refine ⟨11272625154047283675354413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7515083436031522450236275 11272625154047283675354413)
            ·
              refine ⟨4227234432767731378257905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11272625154047283675354413 4227234432767731378257905)
              ·
                refine ⟨3170425824575798533693429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4227234432767731378257905 3170425824575798533693429)
                ·
                  refine ⟨297227421053981112533759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3170425824575798533693429 297227421053981112533759)
                  ·
                    rfl

theorem cell23_5209635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 5].length) (baseStart_5209635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209635 prefixEnd_5209635 := by exact prefixLift 5209635
  have htrace : WordTrace (prefixWord ++ tailWord_5209635) baseStart_5209635 baseEnd_5209635 := by
    simpa [prefixWord, tailWord_5209635, baseEnd_5209635] using wordTrace_append hprefix tailTrace_5209635
  have hstable : (prefixWord ++ tailWord_5209635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209635).length < 2 ^ (prefixWord ++ tailWord_5209635).sum := by decide
  have hdescent : baseEnd_5209635 < baseStart_5209635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209664 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 6]
def baseStart_5209664 : Nat := 118140960795 + 5209664 * 2 ^ 59
def prefixEnd_5209664 : Nat := 4983230072969 + 3 ^ 40 * 5209664 * 2
def baseEnd_5209664 : Nat := 2675061680424810399341197

theorem tailTrace_5209664 : CollatzResearch.WordTrace tailWord_5209664 prefixEnd_5209664 2675061680424810399341197 := by
  unfold tailWord_5209664
  simp only [CollatzResearch.WordTrace]
  refine ⟨95006028099142271310254023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126674704132189695080338697 95006028099142271310254023)
  ·
    refine ⟨142509042148713406965381035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95006028099142271310254023 142509042148713406965381035)
    ·
      refine ⟨213763563223070110448071553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142509042148713406965381035 213763563223070110448071553)
      ·
        refine ⟨160322672417302582836053665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213763563223070110448071553 160322672417302582836053665)
        ·
          refine ⟨120242004312976937127040249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160322672417302582836053665 120242004312976937127040249)
          ·
            refine ⟨90181503234732702845280187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120242004312976937127040249 90181503234732702845280187)
            ·
              refine ⟨135272254852099054267920281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90181503234732702845280187 135272254852099054267920281)
              ·
                refine ⟨101454191139074290700940211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135272254852099054267920281 101454191139074290700940211)
                ·
                  refine ⟨152181286708611436051410317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101454191139074290700940211 152181286708611436051410317)
                  ·
                    refine ⟨57067982515729288519278869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 152181286708611436051410317 57067982515729288519278869)
                    ·
                      refine ⟨2675061680424810399341197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57067982515729288519278869 2675061680424810399341197)
                      ·
                        rfl

theorem cell23_5209664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_5209664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209664 prefixEnd_5209664 := by exact prefixLift 5209664
  have htrace : WordTrace (prefixWord ++ tailWord_5209664) baseStart_5209664 baseEnd_5209664 := by
    simpa [prefixWord, tailWord_5209664, baseEnd_5209664] using wordTrace_append hprefix tailTrace_5209664
  have hstable : (prefixWord ++ tailWord_5209664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209664).length < 2 ^ (prefixWord ++ tailWord_5209664).sum := by decide
  have hdescent : baseEnd_5209664 < baseStart_5209664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209686 : List Nat := [5, 2, 2, 2, 1, 2, 2, 2, 5]
def baseStart_5209686 : Nat := 118140960795 + 5209686 * 2 ^ 59
def prefixEnd_5209686 : Nat := 4983230072969 + 3 ^ 40 * 5209686 * 2
def baseEnd_5209686 : Nat := 297230330777689923696233

theorem tailTrace_5209686 : CollatzResearch.WordTrace tailWord_5209686 prefixEnd_5209686 297230330777689923696233 := by
  unfold tailWord_5209686
  simp only [CollatzResearch.WordTrace]
  refine ⟨11875803662762802523613057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126675239069469893585205941 11875803662762802523613057)
  ·
    refine ⟨8906852747072101892709793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11875803662762802523613057 8906852747072101892709793)
    ·
      refine ⟨6680139560304076419532345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8906852747072101892709793 6680139560304076419532345)
      ·
        refine ⟨5010104670228057314649259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6680139560304076419532345 5010104670228057314649259)
        ·
          refine ⟨7515157005342085971973889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5010104670228057314649259 7515157005342085971973889)
          ·
            refine ⟨5636367754006564478980417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7515157005342085971973889 5636367754006564478980417)
            ·
              refine ⟨4227275815504923359235313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5636367754006564478980417 4227275815504923359235313)
              ·
                refine ⟨3170456861628692519426485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4227275815504923359235313 3170456861628692519426485)
                ·
                  refine ⟨297230330777689923696233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3170456861628692519426485 297230330777689923696233)
                  ·
                    rfl

theorem cell23_5209686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_5209686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209686 prefixEnd_5209686 := by exact prefixLift 5209686
  have htrace : WordTrace (prefixWord ++ tailWord_5209686) baseStart_5209686 baseEnd_5209686 := by
    simpa [prefixWord, tailWord_5209686, baseEnd_5209686] using wordTrace_append hprefix tailTrace_5209686
  have hstable : (prefixWord ++ tailWord_5209686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209686).length < 2 ^ (prefixWord ++ tailWord_5209686).sum := by decide
  have hdescent : baseEnd_5209686 < baseStart_5209686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209721 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 3, 5]
def baseStart_5209721 : Nat := 118140960795 + 5209721 * 2 ^ 59
def prefixEnd_5209721 : Nat := 4983230072969 + 3 ^ 40 * 5209721 * 2
def baseEnd_5209721 : Nat := 891696982940705558776145

theorem tailTrace_5209721 : CollatzResearch.WordTrace tailWord_5209721 prefixEnd_5209721 891696982940705558776145 := by
  unfold tailWord_5209721
  simp only [CollatzResearch.WordTrace]
  refine ⟨190014135159078041355333017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126676090106052027570222011 190014135159078041355333017)
  ·
    refine ⟨142510601369308531016499763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190014135159078041355333017 142510601369308531016499763)
    ·
      refine ⟨213765902053962796524749645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142510601369308531016499763 213765902053962796524749645)
      ·
        refine ⟨80162213270236048696781117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213765902053962796524749645 80162213270236048696781117)
        ·
          refine ⟨30060829976338518261292919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80162213270236048696781117 30060829976338518261292919)
          ·
            refine ⟨45091244964507777391939379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30060829976338518261292919 45091244964507777391939379)
            ·
              refine ⟨67636867446761666087909069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45091244964507777391939379 67636867446761666087909069)
              ·
                refine ⟨25363825292535624782965901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67636867446761666087909069 25363825292535624782965901)
                ·
                  refine ⟨9511434484700859293612213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25363825292535624782965901 9511434484700859293612213)
                  ·
                    refine ⟨891696982940705558776145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9511434484700859293612213 891696982940705558776145)
                    ·
                      rfl

theorem cell23_5209721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 5].length) (baseStart_5209721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209721 prefixEnd_5209721 := by exact prefixLift 5209721
  have htrace : WordTrace (prefixWord ++ tailWord_5209721) baseStart_5209721 baseEnd_5209721 := by
    simpa [prefixWord, tailWord_5209721, baseEnd_5209721] using wordTrace_append hprefix tailTrace_5209721
  have hstable : (prefixWord ++ tailWord_5209721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209721).length < 2 ^ (prefixWord ++ tailWord_5209721).sum := by decide
  have hdescent : baseEnd_5209721 < baseStart_5209721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209728 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 1, 5, 2]
def baseStart_5209728 : Nat := 118140960795 + 5209728 * 2 ^ 59
def prefixEnd_5209728 : Nat := 4983230072969 + 3 ^ 40 * 5209728 * 2
def baseEnd_5209728 : Nat := 2675094543186698148940903

theorem tailTrace_5209728 : CollatzResearch.WordTrace tailWord_5209728 prefixEnd_5209728 2675094543186698148940903 := by
  unfold tailWord_5209728
  simp only [CollatzResearch.WordTrace]
  refine ⟨95007195235026340775418919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126676260313368454367225225 95007195235026340775418919)
  ·
    refine ⟨142510792852539511163128379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95007195235026340775418919 142510792852539511163128379)
    ·
      refine ⟨213766189278809266744692569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142510792852539511163128379 213766189278809266744692569)
      ·
        refine ⟨160324641959106950058519427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213766189278809266744692569 160324641959106950058519427)
        ·
          refine ⟨240486962938660425087779141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160324641959106950058519427 240486962938660425087779141)
          ·
            refine ⟨45091305550998829703958589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 240486962938660425087779141 45091305550998829703958589)
            ·
              refine ⟨16909239581624561138984471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45091305550998829703958589 16909239581624561138984471)
              ·
                refine ⟨25363859372436841708476707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16909239581624561138984471 25363859372436841708476707)
                ·
                  refine ⟨38045789058655262562715061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25363859372436841708476707 38045789058655262562715061)
                  ·
                    refine ⟨3566792724248930865254537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38045789058655262562715061 3566792724248930865254537)
                    ·
                      refine ⟨2675094543186698148940903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3566792724248930865254537 2675094543186698148940903)
                      ·
                        rfl

theorem cell23_5209728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 1, 5, 2].length) (baseStart_5209728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209728 prefixEnd_5209728 := by exact prefixLift 5209728
  have htrace : WordTrace (prefixWord ++ tailWord_5209728) baseStart_5209728 baseEnd_5209728 := by
    simpa [prefixWord, tailWord_5209728, baseEnd_5209728] using wordTrace_append hprefix tailTrace_5209728
  have hstable : (prefixWord ++ tailWord_5209728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209728).length < 2 ^ (prefixWord ++ tailWord_5209728).sum := by decide
  have hdescent : baseEnd_5209728 < baseStart_5209728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209752 : List Nat := [2, 1, 2, 4, 1, 2, 2, 4, 1, 1, 3]
def baseStart_5209752 : Nat := 118140960795 + 5209752 * 2 ^ 59
def prefixEnd_5209752 : Nat := 4983230072969 + 3 ^ 40 * 5209752 * 2
def baseEnd_5209752 : Nat := 2675106866722406055040793

theorem tailTrace_5209752 : CollatzResearch.WordTrace tailWord_5209752 prefixEnd_5209752 2675106866722406055040793 := by
  unfold tailWord_5209752
  simp only [CollatzResearch.WordTrace]
  refine ⟨95007632910982866824855755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126676843881310489099807673 95007632910982866824855755)
  ·
    refine ⟨142511449366474300237283633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95007632910982866824855755 142511449366474300237283633)
    ·
      refine ⟨106883587024855725177962725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142511449366474300237283633 106883587024855725177962725)
      ·
        refine ⟨20040672567160448470868011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106883587024855725177962725 20040672567160448470868011)
        ·
          refine ⟨30061008850740672706302017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20040672567160448470868011 30061008850740672706302017)
          ·
            refine ⟨22545756638055504529726513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30061008850740672706302017 22545756638055504529726513)
            ·
              refine ⟨16909317478541628397294885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22545756638055504529726513 16909317478541628397294885)
              ·
                refine ⟨3170497027226555324492791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16909317478541628397294885 3170497027226555324492791)
                ·
                  refine ⟨4755745540839832986739187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3170497027226555324492791 4755745540839832986739187)
                  ·
                    refine ⟨7133618311259749480108781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4755745540839832986739187 7133618311259749480108781)
                    ·
                      refine ⟨2675106866722406055040793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7133618311259749480108781 2675106866722406055040793)
                      ·
                        rfl

theorem cell23_5209752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_5209752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209752 prefixEnd_5209752 := by exact prefixLift 5209752
  have htrace : WordTrace (prefixWord ++ tailWord_5209752) baseStart_5209752 baseEnd_5209752 := by
    simpa [prefixWord, tailWord_5209752, baseEnd_5209752] using wordTrace_append hprefix tailTrace_5209752
  have hstable : (prefixWord ++ tailWord_5209752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209752).length < 2 ^ (prefixWord ++ tailWord_5209752).sum := by decide
  have hdescent : baseEnd_5209752 < baseStart_5209752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209775 : List Nat := [1, 1, 2, 1, 2, 4, 1, 4, 3, 2, 2]
def baseStart_5209775 : Nat := 118140960795 + 5209775 * 2 ^ 59
def prefixEnd_5209775 : Nat := 4983230072969 + 3 ^ 40 * 5209775 * 2
def baseEnd_5209775 : Nat := 2675118676777459465053187

theorem tailTrace_5209775 : CollatzResearch.WordTrace tailWord_5209775 prefixEnd_5209775 2675118676777459465053187 := by
  unfold tailWord_5209775
  simp only [CollatzResearch.WordTrace]
  refine ⟨190016104700882408577798779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126677403133921605718532519 190016104700882408577798779)
  ·
    refine ⟨285024157051323612866698169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190016104700882408577798779 285024157051323612866698169)
    ·
      refine ⟨213768117788492709650023627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285024157051323612866698169 213768117788492709650023627)
      ·
        refine ⟨320652176682739064475035441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213768117788492709650023627 320652176682739064475035441)
        ·
          refine ⟨240489132512054298356276581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320652176682739064475035441 240489132512054298356276581)
          ·
            refine ⟨45091712346010180941801859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 240489132512054298356276581 45091712346010180941801859)
            ·
              refine ⟨67637568519015271412702789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45091712346010180941801859 67637568519015271412702789)
              ·
                refine ⟨12682044097315363389881773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67637568519015271412702789 12682044097315363389881773)
                ·
                  refine ⟨4755766536493261271205665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12682044097315363389881773 4755766536493261271205665)
                  ·
                    refine ⟨3566824902369945953404249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4755766536493261271205665 3566824902369945953404249)
                    ·
                      refine ⟨2675118676777459465053187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3566824902369945953404249 2675118676777459465053187)
                      ·
                        rfl

theorem cell23_5209775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 2, 2].length) (baseStart_5209775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209775 prefixEnd_5209775 := by exact prefixLift 5209775
  have htrace : WordTrace (prefixWord ++ tailWord_5209775) baseStart_5209775 baseEnd_5209775 := by
    simpa [prefixWord, tailWord_5209775, baseEnd_5209775] using wordTrace_append hprefix tailTrace_5209775
  have hstable : (prefixWord ++ tailWord_5209775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209775).length < 2 ^ (prefixWord ++ tailWord_5209775).sum := by decide
  have hdescent : baseEnd_5209775 < baseStart_5209775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209778 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3]
def baseStart_5209778 : Nat := 118140960795 + 5209778 * 2 ^ 59
def prefixEnd_5209778 : Nat := 4983230072969 + 3 ^ 40 * 5209778 * 2
def baseEnd_5209778 : Nat := 2675120217219422953315673

theorem tailTrace_5209778 : CollatzResearch.WordTrace tailWord_5209778 prefixEnd_5209778 2675120217219422953315673 := by
  unfold tailWord_5209778
  simp only [CollatzResearch.WordTrace]
  refine ⟨47504053529967885022539497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126677476079914360060105325 47504053529967885022539497)
  ·
    refine ⟨35628040147475913766904623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47504053529967885022539497 35628040147475913766904623)
    ·
      refine ⟨53442060221213870650356935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35628040147475913766904623 53442060221213870650356935)
      ·
        refine ⟨80163090331820805975535403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53442060221213870650356935 80163090331820805975535403)
        ·
          refine ⟨120244635497731208963303105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80163090331820805975535403 120244635497731208963303105)
          ·
            refine ⟨90183476623298406722477329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120244635497731208963303105 90183476623298406722477329)
            ·
              refine ⟨67637607467473805041857997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90183476623298406722477329 67637607467473805041857997)
              ·
                refine ⟨25364102800302676890696749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67637607467473805041857997 25364102800302676890696749)
                ·
                  refine ⟨9511538550113503834011281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25364102800302676890696749 9511538550113503834011281)
                  ·
                    refine ⟨7133653912585127875508461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9511538550113503834011281 7133653912585127875508461)
                    ·
                      refine ⟨2675120217219422953315673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7133653912585127875508461 2675120217219422953315673)
                      ·
                        rfl

theorem cell23_5209778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_5209778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209778 prefixEnd_5209778 := by exact prefixLift 5209778
  have htrace : WordTrace (prefixWord ++ tailWord_5209778) baseStart_5209778 baseEnd_5209778 := by
    simpa [prefixWord, tailWord_5209778, baseEnd_5209778] using wordTrace_append hprefix tailTrace_5209778
  have hstable : (prefixWord ++ tailWord_5209778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209778).length < 2 ^ (prefixWord ++ tailWord_5209778).sum := by decide
  have hdescent : baseEnd_5209778 < baseStart_5209778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209805 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_5209805 : Nat := 118140960795 + 5209805 * 2 ^ 59
def prefixEnd_5209805 : Nat := 4983230072969 + 3 ^ 40 * 5209805 * 2
def baseEnd_5209805 : Nat := 2675134081197094347678049

theorem tailTrace_5209805 : CollatzResearch.WordTrace tailWord_5209805 prefixEnd_5209805 2675134081197094347678049 := by
  unfold tailWord_5209805
  simp only [CollatzResearch.WordTrace]
  refine ⟨190017198890773723701390869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126678132593849149134260579 190017198890773723701390869)
  ·
    refine ⟨8907056198005018298502697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 190017198890773723701390869 8907056198005018298502697)
    ·
      refine ⟨6680292148503763723877023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8907056198005018298502697 6680292148503763723877023)
      ·
        refine ⟨10020438222755645585815535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6680292148503763723877023 10020438222755645585815535)
        ·
          refine ⟨15030657334133468378723303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10020438222755645585815535 15030657334133468378723303)
          ·
            refine ⟨22545986001200202568084955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15030657334133468378723303 22545986001200202568084955)
            ·
              refine ⟨33818979001800303852127433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22545986001200202568084955 33818979001800303852127433)
              ·
                refine ⟨25364234251350227889095575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33818979001800303852127433 25364234251350227889095575)
                ·
                  refine ⟨38046351377025341833643363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25364234251350227889095575 38046351377025341833643363)
                  ·
                    refine ⟨57069527065538012750465045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38046351377025341833643363 57069527065538012750465045)
                    ·
                      refine ⟨2675134081197094347678049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57069527065538012750465045 2675134081197094347678049)
                      ·
                        rfl

theorem cell23_5209805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_5209805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209805 prefixEnd_5209805 := by exact prefixLift 5209805
  have htrace : WordTrace (prefixWord ++ tailWord_5209805) baseStart_5209805 baseEnd_5209805 := by
    simpa [prefixWord, tailWord_5209805, baseEnd_5209805] using wordTrace_append hprefix tailTrace_5209805
  have hstable : (prefixWord ++ tailWord_5209805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209805).length < 2 ^ (prefixWord ++ tailWord_5209805).sum := by decide
  have hdescent : baseEnd_5209805 < baseStart_5209805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209851 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 5]
def baseStart_5209851 : Nat := 118140960795 + 5209851 * 2 ^ 59
def prefixEnd_5209851 : Nat := 4983230072969 + 3 ^ 40 * 5209851 * 2
def baseEnd_5209851 : Nat := 2675157701307201167702837

theorem tailTrace_5209851 : CollatzResearch.WordTrace tailWord_5209851 prefixEnd_5209851 2675157701307201167702837 := by
  unfold tailWord_5209851
  simp only [CollatzResearch.WordTrace]
  refine ⟨190018876648607073557565407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126679251099071382371710271 190018876648607073557565407)
  ·
    refine ⟨285028314972910610336348111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190018876648607073557565407 285028314972910610336348111)
    ·
      refine ⟨427542472459365915504522167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285028314972910610336348111 427542472459365915504522167)
      ·
        refine ⟨641313708689048873256783251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427542472459365915504522167 641313708689048873256783251)
        ·
          refine ⟨961970563033573309885174877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 641313708689048873256783251 961970563033573309885174877)
          ·
            refine ⟨360738961137589991206940579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 961970563033573309885174877 360738961137589991206940579)
            ·
              refine ⟨541108441706384986810410869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360738961137589991206940579 541108441706384986810410869)
              ·
                refine ⟨50728916409973592513476019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 541108441706384986810410869 50728916409973592513476019)
                ·
                  refine ⟨76093374614960388770214029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50728916409973592513476019 76093374614960388770214029)
                  ·
                    refine ⟨28535015480610145788830261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76093374614960388770214029 28535015480610145788830261)
                    ·
                      refine ⟨2675157701307201167702837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28535015480610145788830261 2675157701307201167702837)
                      ·
                        rfl

theorem cell23_5209851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 5].length) (baseStart_5209851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209851 prefixEnd_5209851 := by exact prefixLift 5209851
  have htrace : WordTrace (prefixWord ++ tailWord_5209851) baseStart_5209851 baseEnd_5209851 := by
    simpa [prefixWord, tailWord_5209851, baseEnd_5209851] using wordTrace_append hprefix tailTrace_5209851
  have hstable : (prefixWord ++ tailWord_5209851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209851).length < 2 ^ (prefixWord ++ tailWord_5209851).sum := by decide
  have hdescent : baseEnd_5209851 < baseStart_5209851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209861 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 1, 5, 6]
def baseStart_5209861 : Nat := 118140960795 + 5209861 * 2 ^ 59
def prefixEnd_5209861 : Nat := 4983230072969 + 3 ^ 40 * 5209861 * 2
def baseEnd_5209861 : Nat := 2675162836113746128577791

theorem tailTrace_5209861 : CollatzResearch.WordTrace tailWord_5209861 prefixEnd_5209861 2675162836113746128577791 := by
  unfold tailWord_5209861
  simp only [CollatzResearch.WordTrace]
  refine ⟨190019241378570845265429437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126679494252380563510286291 190019241378570845265429437)
  ·
    refine ⟨71257215516964066974536039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190019241378570845265429437 71257215516964066974536039)
    ·
      refine ⟨106885823275446100461804059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71257215516964066974536039 106885823275446100461804059)
      ·
        refine ⟨160328734913169150692706089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106885823275446100461804059 160328734913169150692706089)
        ·
          refine ⟨120246551184876863019529567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160328734913169150692706089 120246551184876863019529567)
          ·
            refine ⟨180369826777315294529294351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120246551184876863019529567 180369826777315294529294351)
            ·
              refine ⟨270554740165972941793941527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180369826777315294529294351 270554740165972941793941527)
              ·
                refine ⟨405832110248959412690912291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270554740165972941793941527 405832110248959412690912291)
                ·
                  refine ⟨608748165373439119036368437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 405832110248959412690912291 608748165373439119036368437)
                  ·
                    refine ⟨57070140503759917409659541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 608748165373439119036368437 57070140503759917409659541)
                    ·
                      refine ⟨2675162836113746128577791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57070140503759917409659541 2675162836113746128577791)
                      ·
                        rfl

theorem cell23_5209861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_5209861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209861 prefixEnd_5209861 := by exact prefixLift 5209861
  have htrace : WordTrace (prefixWord ++ tailWord_5209861) baseStart_5209861 baseEnd_5209861 := by
    simpa [prefixWord, tailWord_5209861, baseEnd_5209861] using wordTrace_append hprefix tailTrace_5209861
  have hstable : (prefixWord ++ tailWord_5209861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209861).length < 2 ^ (prefixWord ++ tailWord_5209861).sum := by decide
  have hdescent : baseEnd_5209861 < baseStart_5209861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209868 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 2, 4, 3]
def baseStart_5209868 : Nat := 118140960795 + 5209868 * 2 ^ 59
def prefixEnd_5209868 : Nat := 4983230072969 + 3 ^ 40 * 5209868 * 2
def baseEnd_5209868 : Nat := 2675166430478327601190259

theorem tailTrace_5209868 : CollatzResearch.WordTrace tailWord_5209868 prefixEnd_5209868 2675166430478327601190259 := by
  unfold tailWord_5209868
  simp only [CollatzResearch.WordTrace]
  refine ⟨95009748344772742730467129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126679664459696990307289505 95009748344772742730467129)
  ·
    refine ⟨71257311258579557047850347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95009748344772742730467129 71257311258579557047850347)
    ·
      refine ⟨106885966887869335571775521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71257311258579557047850347 106885966887869335571775521)
      ·
        refine ⟨80164475165902001678831641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106885966887869335571775521 80164475165902001678831641)
        ·
          refine ⟨60123356374426501259123731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80164475165902001678831641 60123356374426501259123731)
          ·
            refine ⟨90185034561639751888685597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60123356374426501259123731 90185034561639751888685597)
            ·
              refine ⟨33819387960614906958257099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90185034561639751888685597 33819387960614906958257099)
              ·
                refine ⟨50729081940922360437385649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33819387960614906958257099 50729081940922360437385649)
                ·
                  refine ⟨38046811455691770328039237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50729081940922360437385649 38046811455691770328039237)
                  ·
                    refine ⟨7133777147942206936507357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38046811455691770328039237 7133777147942206936507357)
                    ·
                      refine ⟨2675166430478327601190259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7133777147942206936507357 2675166430478327601190259)
                      ·
                        rfl

theorem cell23_5209868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_5209868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209868 prefixEnd_5209868 := by exact prefixLift 5209868
  have htrace : WordTrace (prefixWord ++ tailWord_5209868) baseStart_5209868 baseEnd_5209868 := by
    simpa [prefixWord, tailWord_5209868, baseEnd_5209868] using wordTrace_append hprefix tailTrace_5209868
  have hstable : (prefixWord ++ tailWord_5209868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209868).length < 2 ^ (prefixWord ++ tailWord_5209868).sum := by decide
  have hdescent : baseEnd_5209868 < baseStart_5209868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209876 : List Nat := [2, 4, 4, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_5209876 : Nat := 118140960795 + 5209876 * 2 ^ 59
def prefixEnd_5209876 : Nat := 4983230072969 + 3 ^ 40 * 5209876 * 2
def baseEnd_5209876 : Nat := 2675170538323563569890223

theorem tailTrace_5209876 : CollatzResearch.WordTrace tailWord_5209876 prefixEnd_5209876 2675170538323563569890223 := by
  unfold tailWord_5209876
  simp only [CollatzResearch.WordTrace]
  refine ⟨95009894236758251413612741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126679858982344335218150321 95009894236758251413612741)
  ·
    refine ⟨17814355169392172140052389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95009894236758251413612741 17814355169392172140052389)
    ·
      refine ⟨3340191594261032276259823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17814355169392172140052389 3340191594261032276259823)
      ·
        refine ⟨5010287391391548414389735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3340191594261032276259823 5010287391391548414389735)
        ·
          refine ⟨7515431087087322621584603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5010287391391548414389735 7515431087087322621584603)
          ·
            refine ⟨11273146630630983932376905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7515431087087322621584603 11273146630630983932376905)
            ·
              refine ⟨8454859972973237949282679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11273146630630983932376905 8454859972973237949282679)
              ·
                refine ⟨12682289959459856923924019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8454859972973237949282679 12682289959459856923924019)
                ·
                  refine ⟨19023434939189785385886029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12682289959459856923924019 19023434939189785385886029)
                  ·
                    refine ⟨7133788102196169519707261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19023434939189785385886029 7133788102196169519707261)
                    ·
                      refine ⟨2675170538323563569890223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7133788102196169519707261 2675170538323563569890223)
                      ·
                        rfl

theorem cell23_5209876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_5209876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209876 prefixEnd_5209876 := by exact prefixLift 5209876
  have htrace : WordTrace (prefixWord ++ tailWord_5209876) baseStart_5209876 baseEnd_5209876 := by
    simpa [prefixWord, tailWord_5209876, baseEnd_5209876] using wordTrace_append hprefix tailTrace_5209876
  have hstable : (prefixWord ++ tailWord_5209876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209876).length < 2 ^ (prefixWord ++ tailWord_5209876).sum := by decide
  have hdescent : baseEnd_5209876 < baseStart_5209876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209881 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 7]
def baseStart_5209881 : Nat := 118140960795 + 5209881 * 2 ^ 59
def prefixEnd_5209881 : Nat := 4983230072969 + 3 ^ 40 * 5209881 * 2
def baseEnd_5209881 : Nat := 2675173105726836050327699

theorem tailTrace_5209881 : CollatzResearch.WordTrace tailWord_5209881 prefixEnd_5209881 2675173105726836050327699 := by
  unfold tailWord_5209881
  simp only [CollatzResearch.WordTrace]
  refine ⟨190019970838498388681157497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126679980558998925787438331 190019970838498388681157497)
  ·
    refine ⟨142514978128873791510868123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190019970838498388681157497 142514978128873791510868123)
    ·
      refine ⟨213772467193310687266302185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142514978128873791510868123 213772467193310687266302185)
      ·
        refine ⟨160329350394983015449726639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213772467193310687266302185 160329350394983015449726639)
        ·
          refine ⟨240494025592474523174589959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160329350394983015449726639 240494025592474523174589959)
          ·
            refine ⟨360741038388711784761884939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240494025592474523174589959 360741038388711784761884939)
            ·
              refine ⟨541111557583067677142827409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360741038388711784761884939 541111557583067677142827409)
              ·
                refine ⟨405833668187300757857120557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 541111557583067677142827409 405833668187300757857120557)
                ·
                  refine ⟨152187625570237784196420209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 405833668187300757857120557 152187625570237784196420209)
                  ·
                    refine ⟨114140719177678338147315157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 152187625570237784196420209 114140719177678338147315157)
                    ·
                      refine ⟨2675173105726836050327699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114140719177678338147315157 2675173105726836050327699)
                      ·
                        rfl

theorem cell23_5209881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_5209881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209881 prefixEnd_5209881 := by exact prefixLift 5209881
  have htrace : WordTrace (prefixWord ++ tailWord_5209881) baseStart_5209881 baseEnd_5209881 := by
    simpa [prefixWord, tailWord_5209881, baseEnd_5209881] using wordTrace_append hprefix tailTrace_5209881
  have hstable : (prefixWord ++ tailWord_5209881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209881).length < 2 ^ (prefixWord ++ tailWord_5209881).sum := by decide
  have hdescent : baseEnd_5209881 < baseStart_5209881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209882 : List Nat := [3, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2]
def baseStart_5209882 : Nat := 118140960795 + 5209882 * 2 ^ 59
def prefixEnd_5209882 : Nat := 4983230072969 + 3 ^ 40 * 5209882 * 2
def baseEnd_5209882 : Nat := 2675173619207490546415195

theorem tailTrace_5209882 : CollatzResearch.WordTrace tailWord_5209882 prefixEnd_5209882 2675173619207490546415195 := by
  unfold tailWord_5209882
  simp only [CollatzResearch.WordTrace]
  refine ⟨47505001827873691462985975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126680004874329843901295933 47505001827873691462985975)
  ·
    refine ⟨71257502741810537194478963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47505001827873691462985975 71257502741810537194478963)
    ·
      refine ⟨106886254112715805791718445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71257502741810537194478963 106886254112715805791718445)
      ·
        refine ⟨40082345292268427171894417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106886254112715805791718445 40082345292268427171894417)
        ·
          refine ⟨30061758969201320378920813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40082345292268427171894417 30061758969201320378920813)
          ·
            refine ⟨11273159613450495142095305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30061758969201320378920813 11273159613450495142095305)
            ·
              refine ⟨8454869710087871356571479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11273159613450495142095305 8454869710087871356571479)
              ·
                refine ⟨12682304565131807034857219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8454869710087871356571479 12682304565131807034857219)
                ·
                  refine ⟨19023456847697710552285829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12682304565131807034857219 19023456847697710552285829)
                  ·
                    refine ⟨3566898158943320728553593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19023456847697710552285829 3566898158943320728553593)
                    ·
                      refine ⟨2675173619207490546415195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3566898158943320728553593 2675173619207490546415195)
                      ·
                        rfl

theorem cell23_5209882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_5209882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209882 prefixEnd_5209882 := by exact prefixLift 5209882
  have htrace : WordTrace (prefixWord ++ tailWord_5209882) baseStart_5209882 baseEnd_5209882 := by
    simpa [prefixWord, tailWord_5209882, baseEnd_5209882] using wordTrace_append hprefix tailTrace_5209882
  have hstable : (prefixWord ++ tailWord_5209882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209882).length < 2 ^ (prefixWord ++ tailWord_5209882).sum := by decide
  have hdescent : baseEnd_5209882 < baseStart_5209882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209888 : List Nat := [2, 1, 1, 5, 1, 1, 3, 2, 7]
def baseStart_5209888 : Nat := 118140960795 + 5209888 * 2 ^ 59
def prefixEnd_5209888 : Nat := 4983230072969 + 3 ^ 40 * 5209888 * 2
def baseEnd_5209888 : Nat := 297241855565713058104463

theorem tailTrace_5209888 : CollatzResearch.WordTrace tailWord_5209888 prefixEnd_5209888 297241855565713058104463 := by
  unfold tailWord_5209888
  simp only [CollatzResearch.WordTrace]
  refine ⟨95010113074736514438331159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126680150766315352584441545 95010113074736514438331159)
  ·
    refine ⟨142515169612104771657496739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95010113074736514438331159 142515169612104771657496739)
    ·
      refine ⟨213772754418157157486245109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142515169612104771657496739 213772754418157157486245109)
      ·
        refine ⟨20041195726702233514335479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 213772754418157157486245109 20041195726702233514335479)
        ·
          refine ⟨30061793590053350271503219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20041195726702233514335479 30061793590053350271503219)
          ·
            refine ⟨45092690385080025407254829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30061793590053350271503219 45092690385080025407254829)
            ·
              refine ⟨16909758894405009527720561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45092690385080025407254829 16909758894405009527720561)
              ·
                refine ⟨12682319170803757145790421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16909758894405009527720561 12682319170803757145790421)
                ·
                  refine ⟨297241855565713058104463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12682319170803757145790421 297241855565713058104463)
                  ·
                    rfl

theorem cell23_5209888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 7].length) (baseStart_5209888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209888 prefixEnd_5209888 := by exact prefixLift 5209888
  have htrace : WordTrace (prefixWord ++ tailWord_5209888) baseStart_5209888 baseEnd_5209888 := by
    simpa [prefixWord, tailWord_5209888, baseEnd_5209888] using wordTrace_append hprefix tailTrace_5209888
  have hstable : (prefixWord ++ tailWord_5209888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209888).length < 2 ^ (prefixWord ++ tailWord_5209888).sum := by decide
  have hdescent : baseEnd_5209888 < baseStart_5209888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209905 : List Nat := [1, 2, 2, 3, 2, 2, 1, 5, 5]
def baseStart_5209905 : Nat := 118140960795 + 5209905 * 2 ^ 59
def prefixEnd_5209905 : Nat := 4983230072969 + 3 ^ 40 * 5209905 * 2
def baseEnd_5209905 : Nat := 297242825473615995158621

theorem tailTrace_5209905 : CollatzResearch.WordTrace tailWord_5209905 prefixEnd_5209905 297242825473615995158621 := by
  unfold tailWord_5209905
  simp only [CollatzResearch.WordTrace]
  refine ⟨190020846190411440780031169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126680564126940960520020779 190020846190411440780031169)
  ·
    refine ⟨142515634642808580585023377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190020846190411440780031169 142515634642808580585023377)
    ·
      refine ⟨106886725982106435438767533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142515634642808580585023377 106886725982106435438767533)
      ·
        refine ⟨40082522243289913289537825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106886725982106435438767533 40082522243289913289537825)
        ·
          refine ⟨30061891682467434967153369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40082522243289913289537825 30061891682467434967153369)
          ·
            refine ⟨22546418761850576225365027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30061891682467434967153369 22546418761850576225365027)
            ·
              refine ⟨33819628142775864338047541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22546418761850576225365027 33819628142775864338047541)
              ·
                refine ⟨3170590138385237281691957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33819628142775864338047541 3170590138385237281691957)
                ·
                  refine ⟨297242825473615995158621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3170590138385237281691957 297242825473615995158621)
                  ·
                    rfl

theorem cell23_5209905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 5].length) (baseStart_5209905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209905 prefixEnd_5209905 := by exact prefixLift 5209905
  have htrace : WordTrace (prefixWord ++ tailWord_5209905) baseStart_5209905 baseEnd_5209905 := by
    simpa [prefixWord, tailWord_5209905, baseEnd_5209905] using wordTrace_append hprefix tailTrace_5209905
  have hstable : (prefixWord ++ tailWord_5209905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209905).length < 2 ^ (prefixWord ++ tailWord_5209905).sum := by decide
  have hdescent : baseEnd_5209905 < baseStart_5209905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209933 : List Nat := [1, 6, 1, 2, 1, 2, 3, 1, 2, 2, 2]
def baseStart_5209933 : Nat := 118140960795 + 5209933 * 2 ^ 59
def prefixEnd_5209933 : Nat := 4983230072969 + 3 ^ 40 * 5209933 * 2
def baseEnd_5209933 : Nat := 2675199806720869846877461

theorem tailTrace_5209933 : CollatzResearch.WordTrace tailWord_5209933 prefixEnd_5209933 2675199806720869846877461 := by
  unfold tailWord_5209933
  simp only [CollatzResearch.WordTrace]
  refine ⟨190021867434310001562050453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126681244956206667708033635 190021867434310001562050453)
  ·
    refine ⟨8907275035983281323221115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 190021867434310001562050453 8907275035983281323221115)
    ·
      refine ⟨13360912553974921984831673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8907275035983281323221115 13360912553974921984831673)
      ·
        refine ⟨10020684415481191488623755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13360912553974921984831673 10020684415481191488623755)
        ·
          refine ⟨15031026623221787232935633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10020684415481191488623755 15031026623221787232935633)
          ·
            refine ⟨11273269967416340424701725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15031026623221787232935633 11273269967416340424701725)
            ·
              refine ⟨4227476237781127659263147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11273269967416340424701725 4227476237781127659263147)
              ·
                refine ⟨6341214356671691488894721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4227476237781127659263147 6341214356671691488894721)
                ·
                  refine ⟨4755910767503768616671041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6341214356671691488894721 4755910767503768616671041)
                  ·
                    refine ⟨3566933075627826462503281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4755910767503768616671041 3566933075627826462503281)
                    ·
                      refine ⟨2675199806720869846877461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3566933075627826462503281 2675199806720869846877461)
                      ·
                        rfl

theorem cell23_5209933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_5209933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209933 prefixEnd_5209933 := by exact prefixLift 5209933
  have htrace : WordTrace (prefixWord ++ tailWord_5209933) baseStart_5209933 baseEnd_5209933 := by
    simpa [prefixWord, tailWord_5209933, baseEnd_5209933] using wordTrace_append hprefix tailTrace_5209933
  have hstable : (prefixWord ++ tailWord_5209933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209933).length < 2 ^ (prefixWord ++ tailWord_5209933).sum := by decide
  have hdescent : baseEnd_5209933 < baseStart_5209933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209965 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 5, 4]
def baseStart_5209965 : Nat := 118140960795 + 5209965 * 2 ^ 59
def prefixEnd_5209965 : Nat := 4983230072969 + 3 ^ 40 * 5209965 * 2
def baseEnd_5209965 : Nat := 891738746033937907225771

theorem tailTrace_5209965 : CollatzResearch.WordTrace tailWord_5209965 prefixEnd_5209965 891738746033937907225771 := by
  unfold tailWord_5209965
  simp only [CollatzResearch.WordTrace]
  refine ⟨190023034570194071027215349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126682023046796047351476899 190023034570194071027215349)
  ·
    refine ⟨17814659490955694158801439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 190023034570194071027215349 17814659490955694158801439)
    ·
      refine ⟨26721989236433541238202159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17814659490955694158801439 26721989236433541238202159)
      ·
        refine ⟨40082983854650311857303239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26721989236433541238202159 40082983854650311857303239)
        ·
          refine ⟨60124475781975467785954859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40082983854650311857303239 60124475781975467785954859)
          ·
            refine ⟨90186713672963201678932289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60124475781975467785954859 90186713672963201678932289)
            ·
              refine ⟨67640035254722401259199217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90186713672963201678932289 67640035254722401259199217)
              ·
                refine ⟨50730026441041800944399413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67640035254722401259199217 50730026441041800944399413)
                ·
                  refine ⟨4755939978847668838537445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50730026441041800944399413 4755939978847668838537445)
                  ·
                    refine ⟨891738746033937907225771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4755939978847668838537445 891738746033937907225771)
                    ·
                      rfl

theorem cell23_5209965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_5209965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209965 prefixEnd_5209965 := by exact prefixLift 5209965
  have htrace : WordTrace (prefixWord ++ tailWord_5209965) baseStart_5209965 baseEnd_5209965 := by
    simpa [prefixWord, tailWord_5209965, baseEnd_5209965] using wordTrace_append hprefix tailTrace_5209965
  have hstable : (prefixWord ++ tailWord_5209965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209965).length < 2 ^ (prefixWord ++ tailWord_5209965).sum := by decide
  have hdescent : baseEnd_5209965 < baseStart_5209965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5209978 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 8]
def baseStart_5209978 : Nat := 118140960795 + 5209978 * 2 ^ 59
def prefixEnd_5209978 : Nat := 4983230072969 + 3 ^ 40 * 5209978 * 2
def baseEnd_5209978 : Nat := 297246990372258018979417

theorem tailTrace_5209978 : CollatzResearch.WordTrace tailWord_5209978 prefixEnd_5209978 297246990372258018979417 := by
  unfold tailWord_5209978
  simp only [CollatzResearch.WordTrace]
  refine ⟨47505877179786743561859647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126682339146097982831625725 47505877179786743561859647)
  ·
    refine ⟨71258815769680115342789471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47505877179786743561859647 71258815769680115342789471)
    ·
      refine ⟨106888223654520173014184207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71258815769680115342789471 106888223654520173014184207)
      ·
        refine ⟨160332335481780259521276311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106888223654520173014184207 160332335481780259521276311)
        ·
          refine ⟨240498503222670389281914467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160332335481780259521276311 240498503222670389281914467)
          ·
            refine ⟨360747754834005583922871701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240498503222670389281914467 360747754834005583922871701)
            ·
              refine ⟨16910051007844011746384611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 360747754834005583922871701 16910051007844011746384611)
              ·
                refine ⟨25365076511766017619576917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16910051007844011746384611 25365076511766017619576917)
                ·
                  refine ⟨297246990372258018979417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25365076511766017619576917 297246990372258018979417)
                  ·
                    rfl

theorem cell23_5209978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 8].length) (baseStart_5209978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5209978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5209978 prefixEnd_5209978 := by exact prefixLift 5209978
  have htrace : WordTrace (prefixWord ++ tailWord_5209978) baseStart_5209978 baseEnd_5209978 := by
    simpa [prefixWord, tailWord_5209978, baseEnd_5209978] using wordTrace_append hprefix tailTrace_5209978
  have hstable : (prefixWord ++ tailWord_5209978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5209978).length < 2 ^ (prefixWord ++ tailWord_5209978).sum := by decide
  have hdescent : baseEnd_5209978 < baseStart_5209978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5209978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210055 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 6, 4]
def baseStart_5210055 : Nat := 118140960795 + 5210055 * 2 ^ 59
def prefixEnd_5210055 : Nat := 4983230072969 + 3 ^ 40 * 5210055 * 2
def baseEnd_5210055 : Nat := 891754150453572789850633

theorem tailTrace_5210055 : CollatzResearch.WordTrace tailWord_5210055 prefixEnd_5210055 891754150453572789850633 := by
  unfold tailWord_5210055
  simp only [CollatzResearch.WordTrace]
  refine ⟨190026317139868016397991619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126684211426578677598661079 190026317139868016397991619)
  ·
    refine ⟨285039475709802024596987429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190026317139868016397991619 285039475709802024596987429)
    ·
      refine ⟨53444901695587879611935143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 285039475709802024596987429 53444901695587879611935143)
      ·
        refine ⟨80167352543381819417902715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53444901695587879611935143 80167352543381819417902715)
        ·
          refine ⟨120251028815072729126854073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80167352543381819417902715 120251028815072729126854073)
          ·
            refine ⟨90188271611304546845140555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120251028815072729126854073 90188271611304546845140555)
            ·
              refine ⟨135282407416956820267710833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90188271611304546845140555 135282407416956820267710833)
              ·
                refine ⟨101461805562717615200783125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135282407416956820267710833 101461805562717615200783125)
                ·
                  refine ⟨4756022135752388212536709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 101461805562717615200783125 4756022135752388212536709)
                  ·
                    refine ⟨891754150453572789850633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4756022135752388212536709 891754150453572789850633)
                    ·
                      rfl

theorem cell23_5210055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_5210055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210055 prefixEnd_5210055 := by exact prefixLift 5210055
  have htrace : WordTrace (prefixWord ++ tailWord_5210055) baseStart_5210055 baseEnd_5210055 := by
    simpa [prefixWord, tailWord_5210055, baseEnd_5210055] using wordTrace_append hprefix tailTrace_5210055
  have hstable : (prefixWord ++ tailWord_5210055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210055).length < 2 ^ (prefixWord ++ tailWord_5210055).sum := by decide
  have hdescent : baseEnd_5210055 < baseStart_5210055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210062 : List Nat := [4, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4]
def baseStart_5210062 : Nat := 118140960795 + 5210062 * 2 ^ 59
def prefixEnd_5210062 : Nat := 4983230072969 + 3 ^ 40 * 5210062 * 2
def baseEnd_5210062 : Nat := 2675266045725299842164367

theorem tailTrace_5210062 : CollatzResearch.WordTrace tailWord_5210062 prefixEnd_5210062 2675266045725299842164367 := by
  unfold tailWord_5210062
  simp only [CollatzResearch.WordTrace]
  refine ⟨23753321556355332074187055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126684381633895104395664293 23753321556355332074187055)
  ·
    refine ⟨35629982334532998111280583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23753321556355332074187055 35629982334532998111280583)
    ·
      refine ⟨53444973501799497166920875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35629982334532998111280583 53444973501799497166920875)
      ·
        refine ⟨80167460252699245750381313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53444973501799497166920875 80167460252699245750381313)
        ·
          refine ⟨60125595189524434312785985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80167460252699245750381313 60125595189524434312785985)
          ·
            refine ⟨45094196392143325734589489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60125595189524434312785985 45094196392143325734589489)
            ·
              refine ⟨33820647294107494300942117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45094196392143325734589489 33820647294107494300942117)
              ·
                refine ⟨6341371367645155181426647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33820647294107494300942117 6341371367645155181426647)
                ·
                  refine ⟨9512057051467732772139971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6341371367645155181426647 9512057051467732772139971)
                  ·
                    refine ⟨14268085577201599158209957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9512057051467732772139971 14268085577201599158209957)
                    ·
                      refine ⟨2675266045725299842164367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14268085577201599158209957 2675266045725299842164367)
                      ·
                        rfl

theorem cell23_5210062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_5210062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210062 prefixEnd_5210062 := by exact prefixLift 5210062
  have htrace : WordTrace (prefixWord ++ tailWord_5210062) baseStart_5210062 baseEnd_5210062 := by
    simpa [prefixWord, tailWord_5210062, baseEnd_5210062] using wordTrace_append hprefix tailTrace_5210062
  have hstable : (prefixWord ++ tailWord_5210062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210062).length < 2 ^ (prefixWord ++ tailWord_5210062).sum := by decide
  have hdescent : baseEnd_5210062 < baseStart_5210062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210079 : List Nat := [1, 1, 2, 3, 4, 1, 4, 1, 1, 1, 4]
def baseStart_5210079 : Nat := 118140960795 + 5210079 * 2 ^ 59
def prefixEnd_5210079 : Nat := 4983230072969 + 3 ^ 40 * 5210079 * 2
def baseEnd_5210079 : Nat := 2675274774896426275651789

theorem tailTrace_5210079 : CollatzResearch.WordTrace tailWord_5210079 prefixEnd_5210079 2675274774896426275651789 := by
  unfold tailWord_5210079
  simp only [CollatzResearch.WordTrace]
  refine ⟨190027192491781068496865291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126684794994520712331243527 190027192491781068496865291)
  ·
    refine ⟨285040788737671602745297937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190027192491781068496865291 285040788737671602745297937)
    ·
      refine ⟨213780591553253702058973453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285040788737671602745297937 213780591553253702058973453)
      ·
        refine ⟨80167721832470138272115045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213780591553253702058973453 80167721832470138272115045)
        ·
          refine ⟨15031447843588150926021571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80167721832470138272115045 15031447843588150926021571)
          ·
            refine ⟨22547171765382226389032357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15031447843588150926021571 22547171765382226389032357)
            ·
              refine ⟨4227594706009167447943567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22547171765382226389032357 4227594706009167447943567)
              ·
                refine ⟨6341392059013751171915351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4227594706009167447943567 6341392059013751171915351)
                ·
                  refine ⟨9512088088520626757873027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6341392059013751171915351 9512088088520626757873027)
                  ·
                    refine ⟨14268132132780940136809541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9512088088520626757873027 14268132132780940136809541)
                    ·
                      refine ⟨2675274774896426275651789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14268132132780940136809541 2675274774896426275651789)
                      ·
                        rfl

theorem cell23_5210079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 1, 1, 4].length) (baseStart_5210079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210079 prefixEnd_5210079 := by exact prefixLift 5210079
  have htrace : WordTrace (prefixWord ++ tailWord_5210079) baseStart_5210079 baseEnd_5210079 := by
    simpa [prefixWord, tailWord_5210079, baseEnd_5210079] using wordTrace_append hprefix tailTrace_5210079
  have hstable : (prefixWord ++ tailWord_5210079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210079).length < 2 ^ (prefixWord ++ tailWord_5210079).sum := by decide
  have hdescent : baseEnd_5210079 < baseStart_5210079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210096 : List Nat := [2, 1, 1, 1, 3, 2, 4, 4, 1, 2, 2]
def baseStart_5210096 : Nat := 118140960795 + 5210096 * 2 ^ 59
def prefixEnd_5210096 : Nat := 4983230072969 + 3 ^ 40 * 5210096 * 2
def baseEnd_5210096 : Nat := 2675283504067552709139211

theorem tailTrace_5210096 : CollatzResearch.WordTrace tailWord_5210096 prefixEnd_5210096 2675283504067552709139211 := by
  unfold tailWord_5210096
  simp only [CollatzResearch.WordTrace]
  refine ⟨95013906266359740200117071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126685208355146320266822761 95013906266359740200117071)
  ·
    refine ⟨142520859399539610300175607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95013906266359740200117071 142520859399539610300175607)
    ·
      refine ⟨213781289099309415450263411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142520859399539610300175607 213781289099309415450263411)
      ·
        refine ⟨320671933648964123175395117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213781289099309415450263411 320671933648964123175395117)
        ·
          refine ⟨120251975118361546190773169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320671933648964123175395117 120251975118361546190773169)
          ·
            refine ⟨90188981338771159643079877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120251975118361546190773169 90188981338771159643079877)
            ·
              refine ⟨16910434001019592433077477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90188981338771159643079877 16910434001019592433077477)
              ·
                refine ⟨3170706375191173581202027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16910434001019592433077477 3170706375191173581202027)
                ·
                  refine ⟨4756059562786760371803041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3170706375191173581202027 4756059562786760371803041)
                  ·
                    refine ⟨3567044672090070278852281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4756059562786760371803041 3567044672090070278852281)
                    ·
                      refine ⟨2675283504067552709139211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3567044672090070278852281 2675283504067552709139211)
                      ·
                        rfl

theorem cell23_5210096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 1, 2, 2].length) (baseStart_5210096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210096 prefixEnd_5210096 := by exact prefixLift 5210096
  have htrace : WordTrace (prefixWord ++ tailWord_5210096) baseStart_5210096 baseEnd_5210096 := by
    simpa [prefixWord, tailWord_5210096, baseEnd_5210096] using wordTrace_append hprefix tailTrace_5210096
  have hstable : (prefixWord ++ tailWord_5210096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210096).length < 2 ^ (prefixWord ++ tailWord_5210096).sum := by decide
  have hdescent : baseEnd_5210096 < baseStart_5210096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210175 : List Nat := [1, 1, 2, 2, 3, 1, 2, 4, 7]
def baseStart_5210175 : Nat := 118140960795 + 5210175 * 2 ^ 59
def prefixEnd_5210175 : Nat := 4983230072969 + 3 ^ 40 * 5210175 * 2
def baseEnd_5210175 : Nat := 297258229893250877783483

theorem tailTrace_5210175 : CollatzResearch.WordTrace tailWord_5210175 prefixEnd_5210175 297258229893250877783483 := by
  unfold tailWord_5210175
  simp only [CollatzResearch.WordTrace]
  refine ⟨190030693899433276892359979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126687129266288851261573319 190030693899433276892359979)
  ·
    refine ⟨285046040849149915338539969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190030693899433276892359979 285046040849149915338539969)
    ·
      refine ⟨213784530636862436503904977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285046040849149915338539969 213784530636862436503904977)
      ·
        refine ⟨160338397977646827377928733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213784530636862436503904977 160338397977646827377928733)
        ·
          refine ⟨60126899241617560266723275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160338397977646827377928733 60126899241617560266723275)
          ·
            refine ⟨90190348862426340400084913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60126899241617560266723275 90190348862426340400084913)
            ·
              refine ⟨67642761646819755300063685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90190348862426340400084913 67642761646819755300063685)
              ·
                refine ⟨12683017808778704118761941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67642761646819755300063685 12683017808778704118761941)
                ·
                  refine ⟨297258229893250877783483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12683017808778704118761941 297258229893250877783483)
                  ·
                    rfl

theorem cell23_5210175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 7].length) (baseStart_5210175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210175 prefixEnd_5210175 := by exact prefixLift 5210175
  have htrace : WordTrace (prefixWord ++ tailWord_5210175) baseStart_5210175 baseEnd_5210175 := by
    simpa [prefixWord, tailWord_5210175, baseEnd_5210175] using wordTrace_append hprefix tailTrace_5210175
  have hstable : (prefixWord ++ tailWord_5210175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210175).length < 2 ^ (prefixWord ++ tailWord_5210175).sum := by decide
  have hdescent : baseEnd_5210175 < baseStart_5210175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210202 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3]
def baseStart_5210202 : Nat := 118140960795 + 5210202 * 2 ^ 59
def prefixEnd_5210202 : Nat := 4983230072969 + 3 ^ 40 * 5210202 * 2
def baseEnd_5210202 : Nat := 2675337933016929294413723

theorem tailTrace_5210202 : CollatzResearch.WordTrace tailWord_5210202 prefixEnd_5210202 2675337933016929294413723 := by
  unfold tailWord_5210202
  simp only [CollatzResearch.WordTrace]
  refine ⟨47507919667583865125898215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126687785780223640335728573 47507919667583865125898215)
  ·
    refine ⟨71261879501375797688847323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47507919667583865125898215 71261879501375797688847323)
    ·
      refine ⟨106892819252063696533270985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71261879501375797688847323 106892819252063696533270985)
      ·
        refine ⟨80169614439047772399953239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106892819252063696533270985 80169614439047772399953239)
        ·
          refine ⟨120254421658571658599929859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80169614439047772399953239 120254421658571658599929859)
          ·
            refine ⟨180381632487857487899894789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120254421658571658599929859 180381632487857487899894789)
            ·
              refine ⟨33821556091473278981230273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 180381632487857487899894789 33821556091473278981230273)
              ·
                refine ⟨25366167068604959235922705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33821556091473278981230273 25366167068604959235922705)
                ·
                  refine ⟨19024625301453719426942029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25366167068604959235922705 19024625301453719426942029)
                  ·
                    refine ⟨7134234488045144785103261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19024625301453719426942029 7134234488045144785103261)
                    ·
                      refine ⟨2675337933016929294413723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7134234488045144785103261 2675337933016929294413723)
                      ·
                        rfl

theorem cell23_5210202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_5210202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210202 prefixEnd_5210202 := by exact prefixLift 5210202
  have htrace : WordTrace (prefixWord ++ tailWord_5210202) baseStart_5210202 baseEnd_5210202 := by
    simpa [prefixWord, tailWord_5210202, baseEnd_5210202] using wordTrace_append hprefix tailTrace_5210202
  have hstable : (prefixWord ++ tailWord_5210202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210202).length < 2 ^ (prefixWord ++ tailWord_5210202).sum := by decide
  have hdescent : baseEnd_5210202 < baseStart_5210202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210222 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 1, 7]
def baseStart_5210222 : Nat := 118140960795 + 5210222 * 2 ^ 59
def prefixEnd_5210222 : Nat := 4983230072969 + 3 ^ 40 * 5210222 * 2
def baseEnd_5210222 : Nat := 891782734210006405387877

theorem tailTrace_5210222 : CollatzResearch.WordTrace tailWord_5210222 prefixEnd_5210222 891782734210006405387877 := by
  unfold tailWord_5210222
  simp only [CollatzResearch.WordTrace]
  refine ⟨23754051016282875489915115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126688272086842002612880613 23754051016282875489915115)
  ·
    refine ⟨35631076524424313234872673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23754051016282875489915115 35631076524424313234872673)
    ·
      refine ⟨26723307393318234926154505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35631076524424313234872673 26723307393318234926154505)
      ·
        refine ⟨20042480544988676194615879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26723307393318234926154505 20042480544988676194615879)
        ·
          refine ⟨30063720817483014291923819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20042480544988676194615879 30063720817483014291923819)
          ·
            refine ⟨45095581226224521437885729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30063720817483014291923819 45095581226224521437885729)
            ·
              refine ⟨33821685919668391078414297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45095581226224521437885729 33821685919668391078414297)
              ·
                refine ⟨25366264439751293308810723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33821685919668391078414297 25366264439751293308810723)
                ·
                  refine ⟨38049396659626939963216085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25366264439751293308810723 38049396659626939963216085)
                  ·
                    refine ⟨891782734210006405387877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38049396659626939963216085 891782734210006405387877)
                    ·
                      rfl

theorem cell23_5210222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_5210222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210222 prefixEnd_5210222 := by exact prefixLift 5210222
  have htrace : WordTrace (prefixWord ++ tailWord_5210222) baseStart_5210222 baseEnd_5210222 := by
    simpa [prefixWord, tailWord_5210222, baseEnd_5210222] using wordTrace_append hprefix tailTrace_5210222
  have hstable : (prefixWord ++ tailWord_5210222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210222).length < 2 ^ (prefixWord ++ tailWord_5210222).sum := by decide
  have hdescent : baseEnd_5210222 < baseStart_5210222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210269 : List Nat := [1, 4, 2, 1, 1, 3, 1, 3, 3, 4]
def baseStart_5210269 : Nat := 118140960795 + 5210269 * 2 ^ 59
def prefixEnd_5210269 : Nat := 4983230072969 + 3 ^ 40 * 5210269 * 2
def baseEnd_5210269 : Nat := 891790778740260177425305

theorem tailTrace_5210269 : CollatzResearch.WordTrace tailWord_5210269 prefixEnd_5210269 891790778740260177425305 := by
  unfold tailWord_5210269
  simp only [CollatzResearch.WordTrace]
  refine ⟨190034122361092730946281861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126689414907395153964187907 190034122361092730946281861)
  ·
    refine ⟨35631397942704887052427849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190034122361092730946281861 35631397942704887052427849)
    ·
      refine ⟨26723548457028665289320887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35631397942704887052427849 26723548457028665289320887)
      ·
        refine ⟨40085322685542997933981331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26723548457028665289320887 40085322685542997933981331)
        ·
          refine ⟨60127984028314496900971997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40085322685542997933981331 60127984028314496900971997)
          ·
            refine ⟨22547994010617936337864499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60127984028314496900971997 22547994010617936337864499)
            ·
              refine ⟨33821991015926904506796749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22547994010617936337864499 33821991015926904506796749)
              ·
                refine ⟨12683246630972589190048781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33821991015926904506796749 12683246630972589190048781)
                ·
                  refine ⟨4756217486614720946268293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12683246630972589190048781 4756217486614720946268293)
                  ·
                    refine ⟨891790778740260177425305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4756217486614720946268293 891790778740260177425305)
                    ·
                      rfl

theorem cell23_5210269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_5210269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210269 prefixEnd_5210269 := by exact prefixLift 5210269
  have htrace : WordTrace (prefixWord ++ tailWord_5210269) baseStart_5210269 baseEnd_5210269 := by
    simpa [prefixWord, tailWord_5210269, baseEnd_5210269] using wordTrace_append hprefix tailTrace_5210269
  have hstable : (prefixWord ++ tailWord_5210269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210269).length < 2 ^ (prefixWord ++ tailWord_5210269).sum := by decide
  have hdescent : baseEnd_5210269 < baseStart_5210269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210309 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 5, 1, 3]
def baseStart_5210309 : Nat := 118140960795 + 5210309 * 2 ^ 59
def prefixEnd_5210309 : Nat := 4983230072969 + 3 ^ 40 * 5210309 * 2
def baseEnd_5210309 : Nat := 2675392875446960375775731

theorem tailTrace_5210309 : CollatzResearch.WordTrace tailWord_5210309 prefixEnd_5210309 2675392875446960375775731 := by
  unfold tailWord_5210309
  simp only [CollatzResearch.WordTrace]
  refine ⟨190035581280947817777737981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126690387520631878518491987 190035581280947817777737981)
  ·
    refine ⟨71263342980355431666651743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190035581280947817777737981 71263342980355431666651743)
    ·
      refine ⟨106895014470533147499977615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71263342980355431666651743 106895014470533147499977615)
      ·
        refine ⟨160342521705799721249966423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106895014470533147499977615 160342521705799721249966423)
        ·
          refine ⟨240513782558699581874949635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160342521705799721249966423 240513782558699581874949635)
          ·
            refine ⟨360770673838049372812424453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240513782558699581874949635 360770673838049372812424453)
            ·
              refine ⟨67644501344634257402329585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 360770673838049372812424453 67644501344634257402329585)
              ·
                refine ⟨50733376008475693051747189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67644501344634257402329585 50733376008475693051747189)
                ·
                  refine ⟨4756254000794596223601299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50733376008475693051747189 4756254000794596223601299)
                  ·
                    refine ⟨7134381001191894335401949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4756254000794596223601299 7134381001191894335401949)
                    ·
                      refine ⟨2675392875446960375775731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7134381001191894335401949 2675392875446960375775731)
                      ·
                        rfl

theorem cell23_5210309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 1, 3].length) (baseStart_5210309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210309 prefixEnd_5210309 := by exact prefixLift 5210309
  have htrace : WordTrace (prefixWord ++ tailWord_5210309) baseStart_5210309 baseEnd_5210309 := by
    simpa [prefixWord, tailWord_5210309, baseEnd_5210309] using wordTrace_append hprefix tailTrace_5210309
  have hstable : (prefixWord ++ tailWord_5210309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210309).length < 2 ^ (prefixWord ++ tailWord_5210309).sum := by decide
  have hdescent : baseEnd_5210309 < baseStart_5210309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210312 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 5, 5]
def baseStart_5210312 : Nat := 118140960795 + 5210312 * 2 ^ 59
def prefixEnd_5210312 : Nat := 4983230072969 + 3 ^ 40 * 5210312 * 2
def baseEnd_5210312 : Nat := 891798138629641288012739

theorem tailTrace_5210312 : CollatzResearch.WordTrace tailWord_5210312 prefixEnd_5210312 891798138629641288012739 := by
  unfold tailWord_5210312
  simp only [CollatzResearch.WordTrace]
  refine ⟨95017845349968474645048595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126690460466624632860064793 95017845349968474645048595)
  ·
    refine ⟨142526768024952711967572893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95017845349968474645048595 142526768024952711967572893)
    ·
      refine ⟨53447538009357266987839835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142526768024952711967572893 53447538009357266987839835)
      ·
        refine ⟨80171307014035900481759753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53447538009357266987839835 80171307014035900481759753)
        ·
          refine ⟨60128480260526925361319815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80171307014035900481759753 60128480260526925361319815)
          ·
            refine ⟨90192720390790388041979723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60128480260526925361319815 90192720390790388041979723)
            ·
              refine ⟨135289080586185582062969585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90192720390790388041979723 135289080586185582062969585)
              ·
                refine ⟨101466810439639186547227189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135289080586185582062969585 101466810439639186547227189)
                ·
                  refine ⟨9512513478716173738802549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101466810439639186547227189 9512513478716173738802549)
                  ·
                    refine ⟨891798138629641288012739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9512513478716173738802549 891798138629641288012739)
                    ·
                      rfl

theorem cell23_5210312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_5210312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210312 prefixEnd_5210312 := by exact prefixLift 5210312
  have htrace : WordTrace (prefixWord ++ tailWord_5210312) baseStart_5210312 baseEnd_5210312 := by
    simpa [prefixWord, tailWord_5210312, baseEnd_5210312] using wordTrace_append hprefix tailTrace_5210312
  have hstable : (prefixWord ++ tailWord_5210312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210312).length < 2 ^ (prefixWord ++ tailWord_5210312).sum := by decide
  have hdescent : baseEnd_5210312 < baseStart_5210312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210333 : List Nat := [1, 4, 3, 2, 1, 3, 2, 1, 6]
def baseStart_5210333 : Nat := 118140960795 + 5210333 * 2 ^ 59
def prefixEnd_5210333 : Nat := 4983230072969 + 3 ^ 40 * 5210333 * 2
def baseEnd_5210333 : Nat := 297267244331407586875069

theorem tailTrace_5210333 : CollatzResearch.WordTrace tailWord_5210333 prefixEnd_5210333 297267244331407586875069 := by
  unfold tailWord_5210333
  simp only [CollatzResearch.WordTrace]
  refine ⟨190036456632860869876611653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126690971088573913251074435 190036456632860869876611653)
  ·
    refine ⟨35631835618661413101864685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190036456632860869876611653 35631835618661413101864685)
    ·
      refine ⟨13361938356998029913199257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35631835618661413101864685 13361938356998029913199257)
      ·
        refine ⟨10021453767748522434899443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13361938356998029913199257 10021453767748522434899443)
        ·
          refine ⟨15032180651622783652349165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10021453767748522434899443 15032180651622783652349165)
          ·
            refine ⟨5637067744358543869630937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15032180651622783652349165 5637067744358543869630937)
            ·
              refine ⟨4227800808268907902223203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5637067744358543869630937 4227800808268907902223203)
              ·
                refine ⟨6341701212403361853334805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4227800808268907902223203 6341701212403361853334805)
                ·
                  refine ⟨297267244331407586875069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6341701212403361853334805 297267244331407586875069)
                  ·
                    rfl

theorem cell23_5210333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_5210333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210333 prefixEnd_5210333 := by exact prefixLift 5210333
  have htrace : WordTrace (prefixWord ++ tailWord_5210333) baseStart_5210333 baseEnd_5210333 := by
    simpa [prefixWord, tailWord_5210333, baseEnd_5210333] using wordTrace_append hprefix tailTrace_5210333
  have hstable : (prefixWord ++ tailWord_5210333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210333).length < 2 ^ (prefixWord ++ tailWord_5210333).sum := by decide
  have hdescent : baseEnd_5210333 < baseStart_5210333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210352 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 5]
def baseStart_5210352 : Nat := 118140960795 + 5210352 * 2 ^ 59
def prefixEnd_5210352 : Nat := 4983230072969 + 3 ^ 40 * 5210352 * 2
def baseEnd_5210352 : Nat := 2675414955115103707538033

theorem tailTrace_5210352 : CollatzResearch.WordTrace tailWord_5210352 prefixEnd_5210352 2675414955115103707538033 := by
  unfold tailWord_5210352
  simp only [CollatzResearch.WordTrace]
  refine ⟨95018574809896018060776655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126691433079861357414368873 95018574809896018060776655)
  ·
    refine ⟨142527862214844027091164983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95018574809896018060776655 142527862214844027091164983)
    ·
      refine ⟨213791793322266040636747475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142527862214844027091164983 213791793322266040636747475)
      ·
        refine ⟨320687689983399060955121213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213791793322266040636747475 320687689983399060955121213)
        ·
          refine ⟨120257883743774647858170455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320687689983399060955121213 120257883743774647858170455)
          ·
            refine ⟨180386825615661971787255683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120257883743774647858170455 180386825615661971787255683)
            ·
              refine ⟨270580238423492957680883525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180386825615661971787255683 270580238423492957680883525)
              ·
                refine ⟨50733794704404929565165661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 270580238423492957680883525 50733794704404929565165661)
                ·
                  refine ⟨19025173014151848586937123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50733794704404929565165661 19025173014151848586937123)
                  ·
                    refine ⟨28537759521227772880405685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19025173014151848586937123 28537759521227772880405685)
                    ·
                      refine ⟨2675414955115103707538033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28537759521227772880405685 2675414955115103707538033)
                      ·
                        rfl

theorem cell23_5210352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 5].length) (baseStart_5210352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210352 prefixEnd_5210352 := by exact prefixLift 5210352
  have htrace : WordTrace (prefixWord ++ tailWord_5210352) baseStart_5210352 baseEnd_5210352 := by
    simpa [prefixWord, tailWord_5210352, baseEnd_5210352] using wordTrace_append hprefix tailTrace_5210352
  have hstable : (prefixWord ++ tailWord_5210352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210352).length < 2 ^ (prefixWord ++ tailWord_5210352).sum := by decide
  have hdescent : baseEnd_5210352 < baseStart_5210352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210372 : List Nat := [2, 3, 2, 2, 14]
def baseStart_5210372 : Nat := 118140960795 + 5210372 * 2 ^ 59
def prefixEnd_5210372 : Nat := 4983230072969 + 3 ^ 40 * 5210372 * 2
def baseEnd_5210372 : Nat := 3669993449558564649229

theorem tailTrace_5210372 : CollatzResearch.WordTrace tailWord_5210372 prefixEnd_5210372 3669993449558564649229 := by
  unfold tailWord_5210372
  simp only [CollatzResearch.WordTrace]
  refine ⟨95018939539859789768640685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126691919386479719691520913 95018939539859789768640685)
  ·
    refine ⟨35632102327447421163240257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95018939539859789768640685 35632102327447421163240257)
    ·
      refine ⟨26724076745585565872430193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35632102327447421163240257 26724076745585565872430193)
      ·
        refine ⟨20043057559189174404322645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26724076745585565872430193 20043057559189174404322645)
        ·
          refine ⟨3669993449558564649229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 20043057559189174404322645 3669993449558564649229)
          ·
            rfl

theorem cell23_5210372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 14].length) (baseStart_5210372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210372 prefixEnd_5210372 := by exact prefixLift 5210372
  have htrace : WordTrace (prefixWord ++ tailWord_5210372) baseStart_5210372 baseEnd_5210372 := by
    simpa [prefixWord, tailWord_5210372, baseEnd_5210372] using wordTrace_append hprefix tailTrace_5210372
  have hstable : (prefixWord ++ tailWord_5210372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210372).length < 2 ^ (prefixWord ++ tailWord_5210372).sum := by decide
  have hdescent : baseEnd_5210372 < baseStart_5210372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210376 : List Nat := [2, 1, 3, 2, 3, 1, 1, 4, 2, 4]
def baseStart_5210376 : Nat := 118140960795 + 5210376 * 2 ^ 59
def prefixEnd_5210376 : Nat := 4983230072969 + 3 ^ 40 * 5210376 * 2
def baseEnd_5210376 : Nat := 891809092883603871212641

theorem tailTrace_5210376 : CollatzResearch.WordTrace tailWord_5210376 prefixEnd_5210376 891809092883603871212641 := by
  unfold tailWord_5210376
  simp only [CollatzResearch.WordTrace]
  refine ⟨95019012485852544110213491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126692016647803392146951321 95019012485852544110213491)
  ·
    refine ⟨142528518728778816165320237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95019012485852544110213491 142528518728778816165320237)
    ·
      refine ⟨53448194523292056061995089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142528518728778816165320237 53448194523292056061995089)
      ·
        refine ⟨40086145892469042046496317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53448194523292056061995089 40086145892469042046496317)
        ·
          refine ⟨15032304709675890767436119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40086145892469042046496317 15032304709675890767436119)
          ·
            refine ⟨22548457064513836151154179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15032304709675890767436119 22548457064513836151154179)
            ·
              refine ⟨33822685596770754226731269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22548457064513836151154179 33822685596770754226731269)
              ·
                refine ⟨6341753549394516417512113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33822685596770754226731269 6341753549394516417512113)
                ·
                  refine ⟨4756315162045887313134085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6341753549394516417512113 4756315162045887313134085)
                  ·
                    refine ⟨891809092883603871212641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4756315162045887313134085 891809092883603871212641)
                    ·
                      rfl

theorem cell23_5210376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_5210376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210376 prefixEnd_5210376 := by exact prefixLift 5210376
  have htrace : WordTrace (prefixWord ++ tailWord_5210376) baseStart_5210376 baseEnd_5210376 := by
    simpa [prefixWord, tailWord_5210376, baseEnd_5210376] using wordTrace_append hprefix tailTrace_5210376
  have hstable : (prefixWord ++ tailWord_5210376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210376).length < 2 ^ (prefixWord ++ tailWord_5210376).sum := by decide
  have hdescent : baseEnd_5210376 < baseStart_5210376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210417 : List Nat := [1, 2, 2, 3, 4, 1, 2, 3, 1, 2, 2]
def baseStart_5210417 : Nat := 118140960795 + 5210417 * 2 ^ 59
def prefixEnd_5210417 : Nat := 4983230072969 + 3 ^ 40 * 5210417 * 2
def baseEnd_5210417 : Nat := 2675448331357645953225235

theorem tailTrace_5210417 : CollatzResearch.WordTrace tailWord_5210417 prefixEnd_5210417 2675448331357645953225235 := by
  unfold tailWord_5210417
  simp only [CollatzResearch.WordTrace]
  refine ⟨190039520364556552222669505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126693013576371034815113003 190039520364556552222669505)
  ·
    refine ⟨142529640273417414167002129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190039520364556552222669505 142529640273417414167002129)
    ·
      refine ⟨106897230205063060625251597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142529640273417414167002129 106897230205063060625251597)
      ·
        refine ⟨40086461326898647734469349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106897230205063060625251597 40086461326898647734469349)
        ·
          refine ⟨7516211498793496450213003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40086461326898647734469349 7516211498793496450213003)
          ·
            refine ⟨11274317248190244675319505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7516211498793496450213003 11274317248190244675319505)
            ·
              refine ⟨8455737936142683506489629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11274317248190244675319505 8455737936142683506489629)
              ·
                refine ⟨3170901726053506314933611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8455737936142683506489629 3170901726053506314933611)
                ·
                  refine ⟨4756352589080259472400417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3170901726053506314933611 4756352589080259472400417)
                  ·
                    refine ⟨3567264441810194604300313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4756352589080259472400417 3567264441810194604300313)
                    ·
                      refine ⟨2675448331357645953225235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3567264441810194604300313 2675448331357645953225235)
                      ·
                        rfl

theorem cell23_5210417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_5210417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210417 prefixEnd_5210417 := by exact prefixLift 5210417
  have htrace : WordTrace (prefixWord ++ tailWord_5210417) baseStart_5210417 baseEnd_5210417 := by
    simpa [prefixWord, tailWord_5210417, baseEnd_5210417] using wordTrace_append hprefix tailTrace_5210417
  have hstable : (prefixWord ++ tailWord_5210417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210417).length < 2 ^ (prefixWord ++ tailWord_5210417).sum := by decide
  have hdescent : baseEnd_5210417 < baseStart_5210417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210420 : List Nat := [2, 5, 1, 1, 1, 2, 4, 1, 1, 2, 3]
def baseStart_5210420 : Nat := 118140960795 + 5210420 * 2 ^ 59
def prefixEnd_5210420 : Nat := 4983230072969 + 3 ^ 40 * 5210420 * 2
def baseEnd_5210420 : Nat := 2675449871799609441487721

theorem tailTrace_5210420 : CollatzResearch.WordTrace tailWord_5210420 prefixEnd_5210420 2675449871799609441487721 := by
  unfold tailWord_5210420
  simp only [CollatzResearch.WordTrace]
  refine ⟨95019814891772841867514357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126693086522363789156685809 95019814891772841867514357)
  ·
    refine ⟨8908107646103703925079471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95019814891772841867514357 8908107646103703925079471)
    ·
      refine ⟨13362161469155555887619207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8908107646103703925079471 13362161469155555887619207)
      ·
        refine ⟨20043242203733333831428811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13362161469155555887619207 20043242203733333831428811)
        ·
          refine ⟨30064863305600000747143217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20043242203733333831428811 30064863305600000747143217)
          ·
            refine ⟨22548647479200000560357413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30064863305600000747143217 22548647479200000560357413)
            ·
              refine ⟨4227871402350000105067015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22548647479200000560357413 4227871402350000105067015)
              ·
                refine ⟨6341807103525000157600523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4227871402350000105067015 6341807103525000157600523)
                ·
                  refine ⟨9512710655287500236400785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6341807103525000157600523 9512710655287500236400785)
                  ·
                    refine ⟨7134532991465625177300589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9512710655287500236400785 7134532991465625177300589)
                    ·
                      refine ⟨2675449871799609441487721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7134532991465625177300589 2675449871799609441487721)
                      ·
                        rfl

theorem cell23_5210420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_5210420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210420 prefixEnd_5210420 := by exact prefixLift 5210420
  have htrace : WordTrace (prefixWord ++ tailWord_5210420) baseStart_5210420 baseEnd_5210420 := by
    simpa [prefixWord, tailWord_5210420, baseEnd_5210420] using wordTrace_append hprefix tailTrace_5210420
  have hstable : (prefixWord ++ tailWord_5210420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210420).length < 2 ^ (prefixWord ++ tailWord_5210420).sum := by decide
  have hdescent : baseEnd_5210420 < baseStart_5210420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210449 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 2, 6]
def baseStart_5210449 : Nat := 118140960795 + 5210449 * 2 ^ 59
def prefixEnd_5210449 : Nat := 4983230072969 + 3 ^ 40 * 5210449 * 2
def baseEnd_5210449 : Nat := 891821587579529942675029

theorem tailTrace_5210449 : CollatzResearch.WordTrace tailWord_5210449 prefixEnd_5210449 891821587579529942675029 := by
  unfold tailWord_5210449
  simp only [CollatzResearch.WordTrace]
  refine ⟨190040687500440621687834401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126693791666960414458556267 190040687500440621687834401)
  ·
    refine ⟨142530515625330466265875801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190040687500440621687834401 142530515625330466265875801)
    ·
      refine ⟨106897886718997849699406851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142530515625330466265875801 106897886718997849699406851)
      ·
        refine ⟨160346830078496774549110277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106897886718997849699406851 160346830078496774549110277)
        ·
          refine ⟨30065030639718145227958177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160346830078496774549110277 30065030639718145227958177)
          ·
            refine ⟨22548772979788608920968633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30065030639718145227958177 22548772979788608920968633)
            ·
              refine ⟨16911579734841456690726475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22548772979788608920968633 16911579734841456690726475)
              ·
                refine ⟨25367369602262185036089713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16911579734841456690726475 25367369602262185036089713)
                ·
                  refine ⟨19025527201696638777067285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25367369602262185036089713 19025527201696638777067285)
                  ·
                    refine ⟨891821587579529942675029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19025527201696638777067285 891821587579529942675029)
                    ·
                      rfl

theorem cell23_5210449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_5210449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210449 prefixEnd_5210449 := by exact prefixLift 5210449
  have htrace : WordTrace (prefixWord ++ tailWord_5210449) baseStart_5210449 baseEnd_5210449 := by
    simpa [prefixWord, tailWord_5210449, baseEnd_5210449] using wordTrace_append hprefix tailTrace_5210449
  have hstable : (prefixWord ++ tailWord_5210449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210449).length < 2 ^ (prefixWord ++ tailWord_5210449).sum := by decide
  have hdescent : baseEnd_5210449 < baseStart_5210449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210456 : List Nat := [2, 1, 2, 2, 1, 1, 2, 5, 1, 4, 2]
def baseStart_5210456 : Nat := 118140960795 + 5210456 * 2 ^ 59
def prefixEnd_5210456 : Nat := 4983230072969 + 3 ^ 40 * 5210456 * 2
def baseEnd_5210456 : Nat := 2675468357103171300637555

theorem tailTrace_5210456 : CollatzResearch.WordTrace tailWord_5210456 prefixEnd_5210456 2675468357103171300637555 := by
  unfold tailWord_5210456
  simp only [CollatzResearch.WordTrace]
  refine ⟨95020471405707630941669611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126693961874276841255559481 95020471405707630941669611)
  ·
    refine ⟨142530707108561446412504417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95020471405707630941669611 142530707108561446412504417)
    ·
      refine ⟨106898030331421084809378313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142530707108561446412504417 106898030331421084809378313)
      ·
        refine ⟨80173522748565813607033735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106898030331421084809378313 80173522748565813607033735)
        ·
          refine ⟨120260284122848720410550603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80173522748565813607033735 120260284122848720410550603)
          ·
            refine ⟨180390426184273080615825905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120260284122848720410550603 180390426184273080615825905)
            ·
              refine ⟨135292819638204810461869429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180390426184273080615825905 135292819638204810461869429)
              ·
                refine ⟨12683701841081700980800259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135292819638204810461869429 12683701841081700980800259)
                ·
                  refine ⟨19025552761622551471200389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12683701841081700980800259 19025552761622551471200389)
                  ·
                    refine ⟨3567291142804228400850073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19025552761622551471200389 3567291142804228400850073)
                    ·
                      refine ⟨2675468357103171300637555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3567291142804228400850073 2675468357103171300637555)
                      ·
                        rfl

theorem cell23_5210456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 1, 4, 2].length) (baseStart_5210456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210456 prefixEnd_5210456 := by exact prefixLift 5210456
  have htrace : WordTrace (prefixWord ++ tailWord_5210456) baseStart_5210456 baseEnd_5210456 := by
    simpa [prefixWord, tailWord_5210456, baseEnd_5210456] using wordTrace_append hprefix tailTrace_5210456
  have hstable : (prefixWord ++ tailWord_5210456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210456).length < 2 ^ (prefixWord ++ tailWord_5210456).sum := by decide
  have hdescent : baseEnd_5210456 < baseStart_5210456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210476 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 5]
def baseStart_5210476 : Nat := 118140960795 + 5210476 * 2 ^ 59
def prefixEnd_5210476 : Nat := 4983230072969 + 3 ^ 40 * 5210476 * 2
def baseEnd_5210476 : Nat := 2675478626716261222387463

theorem tailTrace_5210476 : CollatzResearch.WordTrace tailWord_5210476 prefixEnd_5210476 2675478626716261222387463 := by
  unfold tailWord_5210476
  simp only [CollatzResearch.WordTrace]
  refine ⟨95020836135671402649533641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126694448180895203532711521 95020836135671402649533641)
  ·
    refine ⟨71265627101753551987150231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95020836135671402649533641 71265627101753551987150231)
    ·
      refine ⟨106898440652630327980725347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71265627101753551987150231 106898440652630327980725347)
      ·
        refine ⟨160347660978945491971088021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106898440652630327980725347 160347660978945491971088021)
        ·
          refine ⟨7516296608388069936144751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 160347660978945491971088021 7516296608388069936144751)
          ·
            refine ⟨11274444912582104904217127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7516296608388069936144751 11274444912582104904217127)
            ·
              refine ⟨16911667368873157356325691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11274444912582104904217127 16911667368873157356325691)
              ·
                refine ⟨25367501053309736034488537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16911667368873157356325691 25367501053309736034488537)
                ·
                  refine ⟨19025625789982302025866403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25367501053309736034488537 19025625789982302025866403)
                  ·
                    refine ⟨28538438684973453038799605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19025625789982302025866403 28538438684973453038799605)
                    ·
                      refine ⟨2675478626716261222387463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28538438684973453038799605 2675478626716261222387463)
                      ·
                        rfl

theorem cell23_5210476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 5].length) (baseStart_5210476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210476 prefixEnd_5210476 := by exact prefixLift 5210476
  have htrace : WordTrace (prefixWord ++ tailWord_5210476) baseStart_5210476 baseEnd_5210476 := by
    simpa [prefixWord, tailWord_5210476, baseEnd_5210476] using wordTrace_append hprefix tailTrace_5210476
  have hstable : (prefixWord ++ tailWord_5210476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210476).length < 2 ^ (prefixWord ++ tailWord_5210476).sum := by decide
  have hdescent : baseEnd_5210476 < baseStart_5210476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210507 : List Nat := [1, 1, 1, 1, 4, 6, 2, 1, 2, 2, 2]
def baseStart_5210507 : Nat := 118140960795 + 5210507 * 2 ^ 59
def prefixEnd_5210507 : Nat := 4983230072969 + 3 ^ 40 * 5210507 * 2
def baseEnd_5210507 : Nat := 2675494544616550601099821

theorem tailTrace_5210507 : CollatzResearch.WordTrace tailWord_5210507 prefixEnd_5210507 2675494544616550601099821 := by
  unfold tailWord_5210507
  simp only [CollatzResearch.WordTrace]
  refine ⟨190042802934230497593445775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126695201956153665062297183 190042802934230497593445775)
  ·
    refine ⟨285064204401345746390168663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190042802934230497593445775 285064204401345746390168663)
    ·
      refine ⟨427596306602018619585252995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285064204401345746390168663 427596306602018619585252995)
      ·
        refine ⟨641394459903027929377879493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427596306602018619585252995 641394459903027929377879493)
        ·
          refine ⟨120261461231817736758352405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 641394459903027929377879493 120261461231817736758352405)
          ·
            refine ⟨5637255995241456410547769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 120261461231817736758352405 5637255995241456410547769)
            ·
              refine ⟨4227941996431092307910827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5637255995241456410547769 4227941996431092307910827)
              ·
                refine ⟨6341912994646638461866241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4227941996431092307910827 6341912994646638461866241)
                ·
                  refine ⟨4756434745984978846399681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6341912994646638461866241 4756434745984978846399681)
                  ·
                    refine ⟨3567326059488734134799761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4756434745984978846399681 3567326059488734134799761)
                    ·
                      refine ⟨2675494544616550601099821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3567326059488734134799761 2675494544616550601099821)
                      ·
                        rfl

theorem cell23_5210507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 2, 2, 2].length) (baseStart_5210507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210507 prefixEnd_5210507 := by exact prefixLift 5210507
  have htrace : WordTrace (prefixWord ++ tailWord_5210507) baseStart_5210507 baseEnd_5210507 := by
    simpa [prefixWord, tailWord_5210507, baseEnd_5210507] using wordTrace_append hprefix tailTrace_5210507
  have hstable : (prefixWord ++ tailWord_5210507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210507).length < 2 ^ (prefixWord ++ tailWord_5210507).sum := by decide
  have hdescent : baseEnd_5210507 < baseStart_5210507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210546 : List Nat := [3, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4]
def baseStart_5210546 : Nat := 118140960795 + 5210546 * 2 ^ 59
def prefixEnd_5210546 : Nat := 4983230072969 + 3 ^ 40 * 5210546 * 2
def baseEnd_5210546 : Nat := 2675514570362075948512141

theorem tailTrace_5210546 : CollatzResearch.WordTrace tailWord_5210546 prefixEnd_5210546 2675514570362075948512141 := by
  unfold tailWord_5210546
  simp only [CollatzResearch.WordTrace]
  refine ⟨47511056345272301813528873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126696150254059471502743661 47511056345272301813528873)
  ·
    refine ⟨35633292258954226360146655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47511056345272301813528873 35633292258954226360146655)
    ·
      refine ⟨53449938388431339540219983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35633292258954226360146655 53449938388431339540219983)
      ·
        refine ⟨80174907582647009310329975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53449938388431339540219983 80174907582647009310329975)
        ·
          refine ⟨120262361373970513965494963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80174907582647009310329975 120262361373970513965494963)
          ·
            refine ⟨180393542060955770948242445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120262361373970513965494963 180393542060955770948242445)
            ·
              refine ⟨67647578272858414105590917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180393542060955770948242445 67647578272858414105590917)
              ·
                refine ⟨12683920926160952644798297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67647578272858414105590917 12683920926160952644798297)
                ·
                  refine ⟨9512940694620714483598723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12683920926160952644798297 9512940694620714483598723)
                  ·
                    refine ⟨14269411041931071725398085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9512940694620714483598723 14269411041931071725398085)
                    ·
                      refine ⟨2675514570362075948512141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14269411041931071725398085 2675514570362075948512141)
                      ·
                        rfl

theorem cell23_5210546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_5210546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210546 prefixEnd_5210546 := by exact prefixLift 5210546
  have htrace : WordTrace (prefixWord ++ tailWord_5210546) baseStart_5210546 baseEnd_5210546 := by
    simpa [prefixWord, tailWord_5210546, baseEnd_5210546] using wordTrace_append hprefix tailTrace_5210546
  have hstable : (prefixWord ++ tailWord_5210546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210546).length < 2 ^ (prefixWord ++ tailWord_5210546).sum := by decide
  have hdescent : baseEnd_5210546 < baseStart_5210546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210559 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 4]
def baseStart_5210559 : Nat := 118140960795 + 5210559 * 2 ^ 59
def prefixEnd_5210559 : Nat := 4983230072969 + 3 ^ 40 * 5210559 * 2
def baseEnd_5210559 : Nat := 2675521245610584397649581

theorem tailTrace_5210559 : CollatzResearch.WordTrace tailWord_5210559 prefixEnd_5210559 2675521245610584397649581 := by
  unfold tailWord_5210559
  simp only [CollatzResearch.WordTrace]
  refine ⟨190044699530042110474338731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126696466353361406982892487 190044699530042110474338731)
  ·
    refine ⟨285067049295063165711508097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190044699530042110474338731 285067049295063165711508097)
    ·
      refine ⟨213800286971297374283631073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285067049295063165711508097 213800286971297374283631073)
      ·
        refine ⟨160350215228473030712723305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213800286971297374283631073 160350215228473030712723305)
        ·
          refine ⟨120262661421354773034542479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160350215228473030712723305 120262661421354773034542479)
          ·
            refine ⟨180393992132032159551813719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120262661421354773034542479 180393992132032159551813719)
            ·
              refine ⟨270590988198048239327720579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180393992132032159551813719 270590988198048239327720579)
              ·
                refine ⟨405886482297072358991580869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270590988198048239327720579 405886482297072358991580869)
                ·
                  refine ⟨76103715430701067310921413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 405886482297072358991580869 76103715430701067310921413)
                  ·
                    refine ⟨14269446643256450120797765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 76103715430701067310921413 14269446643256450120797765)
                    ·
                      refine ⟨2675521245610584397649581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14269446643256450120797765 2675521245610584397649581)
                      ·
                        rfl

theorem cell23_5210559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_5210559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210559 prefixEnd_5210559 := by exact prefixLift 5210559
  have htrace : WordTrace (prefixWord ++ tailWord_5210559) baseStart_5210559 baseEnd_5210559 := by
    simpa [prefixWord, tailWord_5210559, baseEnd_5210559] using wordTrace_append hprefix tailTrace_5210559
  have hstable : (prefixWord ++ tailWord_5210559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210559).length < 2 ^ (prefixWord ++ tailWord_5210559).sum := by decide
  have hdescent : baseEnd_5210559 < baseStart_5210559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210580 : List Nat := [2, 4, 1, 2, 2, 3, 1, 1, 2, 1, 4]
def baseStart_5210580 : Nat := 118140960795 + 5210580 * 2 ^ 59
def prefixEnd_5210580 : Nat := 4983230072969 + 3 ^ 40 * 5210580 * 2
def baseEnd_5210580 : Nat := 2675532028704328815486985

theorem tailTrace_5210580 : CollatzResearch.WordTrace tailWord_5210580 prefixEnd_5210580 2675532028704328815486985 := by
  unfold tailWord_5210580
  simp only [CollatzResearch.WordTrace]
  refine ⟨95022732731483015530426597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126696976975310687373902129 95022732731483015530426597)
  ·
    refine ⟨17816762387153065411954987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95022732731483015530426597 17816762387153065411954987)
    ·
      refine ⟨26725143580729598117932481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17816762387153065411954987 26725143580729598117932481)
      ·
        refine ⟨20043857685547198588449361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26725143580729598117932481 20043857685547198588449361)
        ·
          refine ⟨15032893264160398941337021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20043857685547198588449361 15032893264160398941337021)
          ·
            refine ⟨5637334974060149603001383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15032893264160398941337021 5637334974060149603001383)
            ·
              refine ⟨8456002461090224404502075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5637334974060149603001383 8456002461090224404502075)
              ·
                refine ⟨12684003691635336606753113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8456002461090224404502075 12684003691635336606753113)
                ·
                  refine ⟨9513002768726502455064835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12684003691635336606753113 9513002768726502455064835)
                  ·
                    refine ⟨14269504153089753682597253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9513002768726502455064835 14269504153089753682597253)
                    ·
                      refine ⟨2675532028704328815486985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14269504153089753682597253 2675532028704328815486985)
                      ·
                        rfl

theorem cell23_5210580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_5210580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210580 prefixEnd_5210580 := by exact prefixLift 5210580
  have htrace : WordTrace (prefixWord ++ tailWord_5210580) baseStart_5210580 baseEnd_5210580 := by
    simpa [prefixWord, tailWord_5210580, baseEnd_5210580] using wordTrace_append hprefix tailTrace_5210580
  have hstable : (prefixWord ++ tailWord_5210580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210580).length < 2 ^ (prefixWord ++ tailWord_5210580).sum := by decide
  have hdescent : baseEnd_5210580 < baseStart_5210580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210606 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_5210606 : Nat := 118140960795 + 5210606 * 2 ^ 59
def prefixEnd_5210606 : Nat := 4983230072969 + 3 ^ 40 * 5210606 * 2
def baseEnd_5210606 : Nat := 2675545379201345713761865

theorem tailTrace_5210606 : CollatzResearch.WordTrace tailWord_5210606 prefixEnd_5210606 2675545379201345713761865 := by
  unfold tailWord_5210606
  simp only [CollatzResearch.WordTrace]
  refine ⟨23755801720108979687662459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126697609173914558334199781 23755801720108979687662459)
  ·
    refine ⟨35633702580163469531493689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23755801720108979687662459 35633702580163469531493689)
    ·
      refine ⟨26725276935122602148620267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35633702580163469531493689 26725276935122602148620267)
      ·
        refine ⟨40087915402683903222930401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26725276935122602148620267 40087915402683903222930401)
        ·
          refine ⟨30065936552012927417197801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40087915402683903222930401 30065936552012927417197801)
          ·
            refine ⟨22549452414009695562898351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30065936552012927417197801 22549452414009695562898351)
            ·
              refine ⟨33824178621014543344347527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22549452414009695562898351 33824178621014543344347527)
              ·
                refine ⟨50736267931521815016521291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33824178621014543344347527 50736267931521815016521291)
                ·
                  refine ⟨76104401897282722524781937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50736267931521815016521291 76104401897282722524781937)
                  ·
                    refine ⟨57078301422962041893586453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76104401897282722524781937 57078301422962041893586453)
                    ·
                      refine ⟨2675545379201345713761865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57078301422962041893586453 2675545379201345713761865)
                      ·
                        rfl

theorem cell23_5210606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_5210606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210606 prefixEnd_5210606 := by exact prefixLift 5210606
  have htrace : WordTrace (prefixWord ++ tailWord_5210606) baseStart_5210606 baseEnd_5210606 := by
    simpa [prefixWord, tailWord_5210606, baseEnd_5210606] using wordTrace_append hprefix tailTrace_5210606
  have hstable : (prefixWord ++ tailWord_5210606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210606).length < 2 ^ (prefixWord ++ tailWord_5210606).sum := by decide
  have hdescent : baseEnd_5210606 < baseStart_5210606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210703 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 6, 1, 3]
def baseStart_5210703 : Nat := 118140960795 + 5210703 * 2 ^ 59
def prefixEnd_5210703 : Nat := 4983230072969 + 3 ^ 40 * 5210703 * 2
def baseEnd_5210703 : Nat := 2675595186824831834248919

theorem tailTrace_5210703 : CollatzResearch.WordTrace tailWord_5210703 prefixEnd_5210703 2675595186824831834248919 := by
  unfold tailWord_5210703
  simp only [CollatzResearch.WordTrace]
  refine ⟨190049951641520423067580763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126699967761013615378387175 190049951641520423067580763)
  ·
    refine ⟨285074927462280634601371145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190049951641520423067580763 285074927462280634601371145)
    ·
      refine ⟨213806195596710475951028359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285074927462280634601371145 213806195596710475951028359)
      ·
        refine ⟨320709293395065713926542539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213806195596710475951028359 320709293395065713926542539)
        ·
          refine ⟨481063940092598570889813809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320709293395065713926542539 481063940092598570889813809)
          ·
            refine ⟨360797955069448928167360357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 481063940092598570889813809 360797955069448928167360357)
            ·
              refine ⟨67649616575521674031380067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 360797955069448928167360357 67649616575521674031380067)
              ·
                refine ⟨101474424863282511047070101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67649616575521674031380067 101474424863282511047070101)
                ·
                  refine ⟨4756613665466367705331411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 101474424863282511047070101 4756613665466367705331411)
                  ·
                    refine ⟨7134920498199551557997117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4756613665466367705331411 7134920498199551557997117)
                    ·
                      refine ⟨2675595186824831834248919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7134920498199551557997117 2675595186824831834248919)
                      ·
                        rfl

theorem cell23_5210703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 1, 3].length) (baseStart_5210703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210703 prefixEnd_5210703 := by exact prefixLift 5210703
  have htrace : WordTrace (prefixWord ++ tailWord_5210703) baseStart_5210703 baseEnd_5210703 := by
    simpa [prefixWord, tailWord_5210703, baseEnd_5210703] using wordTrace_append hprefix tailTrace_5210703
  have hstable : (prefixWord ++ tailWord_5210703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210703).length < 2 ^ (prefixWord ++ tailWord_5210703).sum := by decide
  have hdescent : baseEnd_5210703 < baseStart_5210703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210720 : List Nat := [2, 1, 1, 3, 2, 1, 3, 4, 2, 1, 3]
def baseStart_5210720 : Nat := 118140960795 + 5210720 * 2 ^ 59
def prefixEnd_5210720 : Nat := 4983230072969 + 3 ^ 40 * 5210720 * 2
def baseEnd_5210720 : Nat := 2675603915995958267736341

theorem tailTrace_5210720 : CollatzResearch.WordTrace tailWord_5210720 prefixEnd_5210720 2675603915995958267736341 := by
  unfold tailWord_5210720
  simp only [CollatzResearch.WordTrace]
  refine ⟨95025285841229417485474807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126700381121639223313966409 95025285841229417485474807)
  ·
    refine ⟨142537928761844126228212211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95025285841229417485474807 142537928761844126228212211)
    ·
      refine ⟨213806893142766189342318317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142537928761844126228212211 213806893142766189342318317)
      ·
        refine ⟨80177584928537321003369369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213806893142766189342318317 80177584928537321003369369)
        ·
          refine ⟨60133188696402990752527027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80177584928537321003369369 60133188696402990752527027)
          ·
            refine ⟨90199783044604486128790541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60133188696402990752527027 90199783044604486128790541)
            ·
              refine ⟨33824918641726682298296453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90199783044604486128790541 33824918641726682298296453)
              ·
                refine ⟨6342172245323752930930585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33824918641726682298296453 6342172245323752930930585)
                ·
                  refine ⟨4756629183992814698197939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6342172245323752930930585 4756629183992814698197939)
                  ·
                    refine ⟨7134943775989222047296909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4756629183992814698197939 7134943775989222047296909)
                    ·
                      refine ⟨2675603915995958267736341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7134943775989222047296909 2675603915995958267736341)
                      ·
                        rfl

theorem cell23_5210720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_5210720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210720 prefixEnd_5210720 := by exact prefixLift 5210720
  have htrace : WordTrace (prefixWord ++ tailWord_5210720) baseStart_5210720 baseEnd_5210720 := by
    simpa [prefixWord, tailWord_5210720, baseEnd_5210720] using wordTrace_append hprefix tailTrace_5210720
  have hstable : (prefixWord ++ tailWord_5210720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210720).length < 2 ^ (prefixWord ++ tailWord_5210720).sum := by decide
  have hdescent : baseEnd_5210720 < baseStart_5210720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210721 : List Nat := [1, 2, 3, 1, 1, 6, 2, 2, 1, 2, 2]
def baseStart_5210721 : Nat := 118140960795 + 5210721 * 2 ^ 59
def prefixEnd_5210721 : Nat := 4983230072969 + 3 ^ 40 * 5210721 * 2
def baseEnd_5210721 : Nat := 2675604429476612763823837

theorem tailTrace_5210721 : CollatzResearch.WordTrace tailWord_5210721 prefixEnd_5210721 2675604429476612763823837 := by
  unfold tailWord_5210721
  simp only [CollatzResearch.WordTrace]
  refine ⟨190050608155455212141736017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126700405436970141427824011 190050608155455212141736017)
  ·
    refine ⟨142537956116591409106302013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190050608155455212141736017 142537956116591409106302013)
    ·
      refine ⟨53451733543721778414863255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142537956116591409106302013 53451733543721778414863255)
      ·
        refine ⟨80177600315582667622294883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53451733543721778414863255 80177600315582667622294883)
        ·
          refine ⟨120266400473374001433442325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80177600315582667622294883 120266400473374001433442325)
          ·
            refine ⟨5637487522189406317192609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 120266400473374001433442325 5637487522189406317192609)
            ·
              refine ⟨4228115641642054737894457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5637487522189406317192609 4228115641642054737894457)
              ·
                refine ⟨3171086731231541053420843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4228115641642054737894457 3171086731231541053420843)
                ·
                  refine ⟨4756630096847311580131265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3171086731231541053420843 4756630096847311580131265)
                  ·
                    refine ⟨3567472572635483685098449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4756630096847311580131265 3567472572635483685098449)
                    ·
                      refine ⟨2675604429476612763823837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3567472572635483685098449 2675604429476612763823837)
                      ·
                        rfl

theorem cell23_5210721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 1, 2, 2].length) (baseStart_5210721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210721 prefixEnd_5210721 := by exact prefixLift 5210721
  have htrace : WordTrace (prefixWord ++ tailWord_5210721) baseStart_5210721 baseEnd_5210721 := by
    simpa [prefixWord, tailWord_5210721, baseEnd_5210721] using wordTrace_append hprefix tailTrace_5210721
  have hstable : (prefixWord ++ tailWord_5210721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210721).length < 2 ^ (prefixWord ++ tailWord_5210721).sum := by decide
  have hdescent : baseEnd_5210721 < baseStart_5210721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210730 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 5, 3, 2]
def baseStart_5210730 : Nat := 118140960795 + 5210730 * 2 ^ 59
def prefixEnd_5210730 : Nat := 4983230072969 + 3 ^ 40 * 5210730 * 2
def baseEnd_5210730 : Nat := 2675609050802503228611295

theorem tailTrace_5210730 : CollatzResearch.WordTrace tailWord_5210730 prefixEnd_5210730 2675609050802503228611295 := by
  unfold tailWord_5210730
  simp only [CollatzResearch.WordTrace]
  refine ⟨47512734103105651669703411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126700624274948404452542429 47512734103105651669703411)
  ·
    refine ⟨71269101154658477504555117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47512734103105651669703411 71269101154658477504555117)
    ·
      refine ⟨26725912932996929064208169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71269101154658477504555117 26725912932996929064208169)
      ·
        refine ⟨20044434699747696798156127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26725912932996929064208169 20044434699747696798156127)
        ·
          refine ⟨30066652049621545197234191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20044434699747696798156127 30066652049621545197234191)
          ·
            refine ⟨45099978074432317795851287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30066652049621545197234191 45099978074432317795851287)
            ·
              refine ⟨67649967111648476693776931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45099978074432317795851287 67649967111648476693776931)
              ·
                refine ⟨101474950667472715040665397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67649967111648476693776931 101474950667472715040665397)
                ·
                  refine ⟨9513276625075567035062381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101474950667472715040665397 9513276625075567035062381)
                  ·
                    refine ⟨3567478734403337638148393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9513276625075567035062381 3567478734403337638148393)
                    ·
                      refine ⟨2675609050802503228611295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3567478734403337638148393 2675609050802503228611295)
                      ·
                        rfl

theorem cell23_5210730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_5210730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210730 prefixEnd_5210730 := by exact prefixLift 5210730
  have htrace : WordTrace (prefixWord ++ tailWord_5210730) baseStart_5210730 baseEnd_5210730 := by
    simpa [prefixWord, tailWord_5210730, baseEnd_5210730] using wordTrace_append hprefix tailTrace_5210730
  have hstable : (prefixWord ++ tailWord_5210730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210730).length < 2 ^ (prefixWord ++ tailWord_5210730).sum := by decide
  have hdescent : baseEnd_5210730 < baseStart_5210730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210813 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 1, 7]
def baseStart_5210813 : Nat := 118140960795 + 5210813 * 2 ^ 59
def prefixEnd_5210813 : Nat := 4983230072969 + 3 ^ 40 * 5210813 * 2
def baseEnd_5210813 : Nat := 891883889898942134624471

theorem tailTrace_5210813 : CollatzResearch.WordTrace tailWord_5210813 prefixEnd_5210813 891883889898942134624471 := by
  unfold tailWord_5210813
  simp only [CollatzResearch.WordTrace]
  refine ⟨190053963671121911854085093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126702642447414607902723395 190053963671121911854085093)
  ·
    refine ⟨35635118188335358472640955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190053963671121911854085093 35635118188335358472640955)
    ·
      refine ⟨53452677282503037708961433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35635118188335358472640955 53452677282503037708961433)
      ·
        refine ⟨40089507961877278281721075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53452677282503037708961433 40089507961877278281721075)
        ·
          refine ⟨60134261942815917422581613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40089507961877278281721075 60134261942815917422581613)
          ·
            refine ⟨22550348228555969033468105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60134261942815917422581613 22550348228555969033468105)
            ·
              refine ⟨16912761171416976775101079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22550348228555969033468105 16912761171416976775101079)
              ·
                refine ⟨25369141757125465162651619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16912761171416976775101079 25369141757125465162651619)
                ·
                  refine ⟨38053712635688197743977429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25369141757125465162651619 38053712635688197743977429)
                  ·
                    refine ⟨891883889898942134624471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38053712635688197743977429 891883889898942134624471)
                    ·
                      rfl

theorem cell23_5210813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_5210813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210813 prefixEnd_5210813 := by exact prefixLift 5210813
  have htrace : WordTrace (prefixWord ++ tailWord_5210813) baseStart_5210813 baseEnd_5210813 := by
    simpa [prefixWord, tailWord_5210813, baseEnd_5210813] using wordTrace_append hprefix tailTrace_5210813
  have hstable : (prefixWord ++ tailWord_5210813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210813).length < 2 ^ (prefixWord ++ tailWord_5210813).sum := by decide
  have hdescent : baseEnd_5210813 < baseStart_5210813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210830 : List Nat := [4, 1, 1, 1, 3, 3, 1, 2, 2, 5]
def baseStart_5210830 : Nat := 118140960795 + 5210830 * 2 ^ 59
def prefixEnd_5210830 : Nat := 4983230072969 + 3 ^ 40 * 5210830 * 2
def baseEnd_5210830 : Nat := 891886799622650945786945

theorem tailTrace_5210830 : CollatzResearch.WordTrace tailWord_5210830 prefixEnd_5210830 891886799622650945786945 := by
  unfold tailWord_5210830
  simp only [CollatzResearch.WordTrace]
  refine ⟨23756822964007540469681743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126703055808040215838302629 23756822964007540469681743)
  ·
    refine ⟨35635234446011310704522615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23756822964007540469681743 35635234446011310704522615)
    ·
      refine ⟨53452851669016966056783923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35635234446011310704522615 53452851669016966056783923)
      ·
        refine ⟨80179277503525449085175885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53452851669016966056783923 80179277503525449085175885)
        ·
          refine ⟨30067229063822043406940957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80179277503525449085175885 30067229063822043406940957)
          ·
            refine ⟨11275210898933266277602859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30067229063822043406940957 11275210898933266277602859)
            ·
              refine ⟨16912816348399899416404289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11275210898933266277602859 16912816348399899416404289)
              ·
                refine ⟨12684612261299924562303217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16912816348399899416404289 12684612261299924562303217)
                ·
                  refine ⟨9513459195974943421727413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12684612261299924562303217 9513459195974943421727413)
                  ·
                    refine ⟨891886799622650945786945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9513459195974943421727413 891886799622650945786945)
                    ·
                      rfl

theorem cell23_5210830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_5210830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210830 prefixEnd_5210830 := by exact prefixLift 5210830
  have htrace : WordTrace (prefixWord ++ tailWord_5210830) baseStart_5210830 baseEnd_5210830 := by
    simpa [prefixWord, tailWord_5210830, baseEnd_5210830] using wordTrace_append hprefix tailTrace_5210830
  have hstable : (prefixWord ++ tailWord_5210830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210830).length < 2 ^ (prefixWord ++ tailWord_5210830).sum := by decide
  have hdescent : baseEnd_5210830 < baseStart_5210830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210834 : List Nat := [3, 2, 2, 2, 3, 1, 3, 2, 5]
def baseStart_5210834 : Nat := 118140960795 + 5210834 * 2 ^ 59
def prefixEnd_5210834 : Nat := 4983230072969 + 3 ^ 40 * 5210834 * 2
def baseEnd_5210834 : Nat := 297295828087841202412313

theorem tailTrace_5210834 : CollatzResearch.WordTrace tailWord_5210834 prefixEnd_5210834 297295828087841202412313 := by
  unfold tailWord_5210834
  simp only [CollatzResearch.WordTrace]
  refine ⟨47513682401011458110149889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126703153069363888293733037 47513682401011458110149889)
  ·
    refine ⟨35635261800758593582612417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47513682401011458110149889 35635261800758593582612417)
    ·
      refine ⟨26726446350568945186959313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35635261800758593582612417 26726446350568945186959313)
      ·
        refine ⟨20044834762926708890219485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26726446350568945186959313 20044834762926708890219485)
        ·
          refine ⟨7516813036097515833832307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20044834762926708890219485 7516813036097515833832307)
          ·
            refine ⟨11275219554146273750748461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7516813036097515833832307 11275219554146273750748461)
            ·
              refine ⟨4228207332804852656530673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11275219554146273750748461 4228207332804852656530673)
              ·
                refine ⟨3171155499603639492398005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4228207332804852656530673 3171155499603639492398005)
                ·
                  refine ⟨297295828087841202412313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3171155499603639492398005 297295828087841202412313)
                  ·
                    rfl

theorem cell23_5210834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_5210834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210834 prefixEnd_5210834 := by exact prefixLift 5210834
  have htrace : WordTrace (prefixWord ++ tailWord_5210834) baseStart_5210834 baseEnd_5210834 := by
    simpa [prefixWord, tailWord_5210834, baseEnd_5210834] using wordTrace_append hprefix tailTrace_5210834
  have hstable : (prefixWord ++ tailWord_5210834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210834).length < 2 ^ (prefixWord ++ tailWord_5210834).sum := by decide
  have hdescent : baseEnd_5210834 < baseStart_5210834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210843 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 9, 4]
def baseStart_5210843 : Nat := 118140960795 + 5210843 * 2 ^ 59
def prefixEnd_5210843 : Nat := 4983230072969 + 3 ^ 40 * 5210843 * 2
def baseEnd_5210843 : Nat := 891889024705487095499425

theorem tailTrace_5210843 : CollatzResearch.WordTrace tailWord_5210843 prefixEnd_5210843 891889024705487095499425 := by
  unfold tailWord_5210843
  simp only [CollatzResearch.WordTrace]
  refine ⟨190055057861013226977677183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126703371907342151318451455 190055057861013226977677183)
  ·
    refine ⟨285082586791519840466515775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190055057861013226977677183 285082586791519840466515775)
    ·
      refine ⟨427623880187279760699773663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285082586791519840466515775 427623880187279760699773663)
      ·
        refine ⟨641435820280919641049660495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427623880187279760699773663 641435820280919641049660495)
        ·
          refine ⟨962153730421379461574490743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 641435820280919641049660495 962153730421379461574490743)
          ·
            refine ⟨1443230595632069192361736115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 962153730421379461574490743 1443230595632069192361736115)
            ·
              refine ⟨2164845893448103788542604173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1443230595632069192361736115 2164845893448103788542604173)
              ·
                refine ⟨811817210043038920703476565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2164845893448103788542604173 811817210043038920703476565)
                ·
                  refine ⟨4756741465095931175996933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 811817210043038920703476565 4756741465095931175996933)
                  ·
                    refine ⟨891889024705487095499425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4756741465095931175996933 891889024705487095499425)
                    ·
                      rfl

theorem cell23_5210843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 4].length) (baseStart_5210843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210843 prefixEnd_5210843 := by exact prefixLift 5210843
  have htrace : WordTrace (prefixWord ++ tailWord_5210843) baseStart_5210843 baseEnd_5210843 := by
    simpa [prefixWord, tailWord_5210843, baseEnd_5210843] using wordTrace_append hprefix tailTrace_5210843
  have hstable : (prefixWord ++ tailWord_5210843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210843).length < 2 ^ (prefixWord ++ tailWord_5210843).sum := by decide
  have hdescent : baseEnd_5210843 < baseStart_5210843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210877 : List Nat := [1, 4, 1, 1, 1, 1, 4, 5, 1, 4]
def baseStart_5210877 : Nat := 118140960795 + 5210877 * 2 ^ 59
def prefixEnd_5210877 : Nat := 4983230072969 + 3 ^ 40 * 5210877 * 2
def baseEnd_5210877 : Nat := 891894844152904717824373

theorem tailTrace_5210877 : CollatzResearch.WordTrace tailWord_5210877 prefixEnd_5210877 891894844152904717824373 := by
  unfold tailWord_5210877
  simp only [CollatzResearch.WordTrace]
  refine ⟨190056297942890050784414885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126704198628593367189609923 190056297942890050784414885)
  ·
    refine ⟨35635555864291884522077791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190056297942890050784414885 35635555864291884522077791)
    ·
      refine ⟨53453333796437826783116687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35635555864291884522077791 53453333796437826783116687)
      ·
        refine ⟨80180000694656740174675031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53453333796437826783116687 80180000694656740174675031)
        ·
          refine ⟨120270001041985110262012547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80180000694656740174675031 120270001041985110262012547)
          ·
            refine ⟨180405001562977665393018821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120270001041985110262012547 180405001562977665393018821)
            ·
              refine ⟨33825937793058312261191029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 180405001562977665393018821 33825937793058312261191029)
              ·
                refine ⟨3171181668099216774486659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33825937793058312261191029 3171181668099216774486659)
                ·
                  refine ⟨4756772502148825161729989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3171181668099216774486659 4756772502148825161729989)
                  ·
                    refine ⟨891894844152904717824373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4756772502148825161729989 891894844152904717824373)
                    ·
                      rfl

theorem cell23_5210877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_5210877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210877 prefixEnd_5210877 := by exact prefixLift 5210877
  have htrace : WordTrace (prefixWord ++ tailWord_5210877) baseStart_5210877 baseEnd_5210877 := by
    simpa [prefixWord, tailWord_5210877, baseEnd_5210877] using wordTrace_append hprefix tailTrace_5210877
  have hstable : (prefixWord ++ tailWord_5210877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210877).length < 2 ^ (prefixWord ++ tailWord_5210877).sum := by decide
  have hdescent : baseEnd_5210877 < baseStart_5210877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210887 : List Nat := [1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 3]
def baseStart_5210887 : Nat := 118140960795 + 5210887 * 2 ^ 59
def prefixEnd_5210887 : Nat := 4983230072969 + 3 ^ 40 * 5210887 * 2
def baseEnd_5210887 : Nat := 2675689667265259114348073

theorem tailTrace_5210887 : CollatzResearch.WordTrace tailWord_5210887 prefixEnd_5210887 2675689667265259114348073 := by
  unfold tailWord_5210887
  simp only [CollatzResearch.WordTrace]
  refine ⟨190056662672853822492278915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126704441781902548328185943 190056662672853822492278915)
  ·
    refine ⟨285084994009280733738418373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190056662672853822492278915 285084994009280733738418373)
    ·
      refine ⟨53453436376740137575953445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 285084994009280733738418373 53453436376740137575953445)
      ·
        refine ⟨10022519320638775795491271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53453436376740137575953445 10022519320638775795491271)
        ·
          refine ⟨15033778980958163693236907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10022519320638775795491271 15033778980958163693236907)
          ·
            refine ⟨22550668471437245539855361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15033778980958163693236907 22550668471437245539855361)
            ·
              refine ⟨16913001353577934154891521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22550668471437245539855361 16913001353577934154891521)
              ·
                refine ⟨12684751015183450616168641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16913001353577934154891521 12684751015183450616168641)
                ·
                  refine ⟨9513563261387587962126481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12684751015183450616168641 9513563261387587962126481)
                  ·
                    refine ⟨7135172446040690971594861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9513563261387587962126481 7135172446040690971594861)
                    ·
                      refine ⟨2675689667265259114348073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7135172446040690971594861 2675689667265259114348073)
                      ·
                        rfl

theorem cell23_5210887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_5210887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210887 prefixEnd_5210887 := by exact prefixLift 5210887
  have htrace : WordTrace (prefixWord ++ tailWord_5210887) baseStart_5210887 baseEnd_5210887 := by
    simpa [prefixWord, tailWord_5210887, baseEnd_5210887] using wordTrace_append hprefix tailTrace_5210887
  have hstable : (prefixWord ++ tailWord_5210887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210887).length < 2 ^ (prefixWord ++ tailWord_5210887).sum := by decide
  have hdescent : baseEnd_5210887 < baseStart_5210887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210890 : List Nat := [3, 1, 2, 2, 1, 2, 4, 2, 6]
def baseStart_5210890 : Nat := 118140960795 + 5210890 * 2 ^ 59
def prefixEnd_5210890 : Nat := 4983230072969 + 3 ^ 40 * 5210890 * 2
def baseEnd_5210890 : Nat := 297299023078580289178951

theorem tailTrace_5210890 : CollatzResearch.WordTrace tailWord_5210890 prefixEnd_5210890 297299023078580289178951 := by
  unfold tailWord_5210890
  simp only [CollatzResearch.WordTrace]
  refine ⟨47514193022960738501159531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126704514727895302669758749 47514193022960738501159531)
  ·
    refine ⟨71271289534441107751739297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47514193022960738501159531 71271289534441107751739297)
    ·
      refine ⟨53453467150830830813804473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71271289534441107751739297 53453467150830830813804473)
      ·
        refine ⟨40090100363123123110353355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53453467150830830813804473 40090100363123123110353355)
        ·
          refine ⟨60135150544684684665530033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40090100363123123110353355 60135150544684684665530033)
          ·
            refine ⟨45101362908513513499147525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60135150544684684665530033 45101362908513513499147525)
            ·
              refine ⟨8456505545346283781090161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45101362908513513499147525 8456505545346283781090161)
              ·
                refine ⟨6342379159009712835817621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8456505545346283781090161 6342379159009712835817621)
                ·
                  refine ⟨297299023078580289178951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6342379159009712835817621 297299023078580289178951)
                  ·
                    rfl

theorem cell23_5210890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 6].length) (baseStart_5210890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210890 prefixEnd_5210890 := by exact prefixLift 5210890
  have htrace : WordTrace (prefixWord ++ tailWord_5210890) baseStart_5210890 baseEnd_5210890 := by
    simpa [prefixWord, tailWord_5210890, baseEnd_5210890] using wordTrace_append hprefix tailTrace_5210890
  have hstable : (prefixWord ++ tailWord_5210890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210890).length < 2 ^ (prefixWord ++ tailWord_5210890).sum := by decide
  have hdescent : baseEnd_5210890 < baseStart_5210890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210913 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 2, 1, 7]
def baseStart_5210913 : Nat := 118140960795 + 5210913 * 2 ^ 59
def prefixEnd_5210913 : Nat := 4983230072969 + 3 ^ 40 * 5210913 * 2
def baseEnd_5210913 : Nat := 2675703017762276012622953

theorem tailTrace_5210913 : CollatzResearch.WordTrace tailWord_5210913 prefixEnd_5210913 2675703017762276012622953 := by
  unfold tailWord_5210913
  simp only [CollatzResearch.WordTrace]
  refine ⟨190057610970759628932725393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126705073980506419288483595 190057610970759628932725393)
  ·
    refine ⟨142543208228069721699544045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190057610970759628932725393 142543208228069721699544045)
    ·
      refine ⟨53453703085526145637329017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142543208228069721699544045 53453703085526145637329017)
      ·
        refine ⟨40090277314144609227996763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53453703085526145637329017 40090277314144609227996763)
        ·
          refine ⟨60135415971216913841995145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40090277314144609227996763 60135415971216913841995145)
          ·
            refine ⟨45101561978412685381496359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60135415971216913841995145 45101561978412685381496359)
            ·
              refine ⟨67652342967619028072244539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45101561978412685381496359 67652342967619028072244539)
              ·
                refine ⟨101478514451428542108366809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67652342967619028072244539 101478514451428542108366809)
                ·
                  refine ⟨76108885838571406581275107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101478514451428542108366809 76108885838571406581275107)
                  ·
                    refine ⟨114163328757857109871912661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76108885838571406581275107 114163328757857109871912661)
                    ·
                      refine ⟨2675703017762276012622953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114163328757857109871912661 2675703017762276012622953)
                      ·
                        rfl

theorem cell23_5210913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_5210913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210913 prefixEnd_5210913 := by exact prefixLift 5210913
  have htrace : WordTrace (prefixWord ++ tailWord_5210913) baseStart_5210913 baseEnd_5210913 := by
    simpa [prefixWord, tailWord_5210913, baseEnd_5210913] using wordTrace_append hprefix tailTrace_5210913
  have hstable : (prefixWord ++ tailWord_5210913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210913).length < 2 ^ (prefixWord ++ tailWord_5210913).sum := by decide
  have hdescent : baseEnd_5210913 < baseStart_5210913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210917 : List Nat := [1, 3, 1, 2, 3, 1, 3, 2, 3, 1, 3]
def baseStart_5210917 : Nat := 118140960795 + 5210917 * 2 ^ 59
def prefixEnd_5210917 : Nat := 4983230072969 + 3 ^ 40 * 5210917 * 2
def baseEnd_5210917 : Nat := 2675705071684893996972935

theorem tailTrace_5210917 : CollatzResearch.WordTrace tailWord_5210917 prefixEnd_5210917 2675705071684893996972935 := by
  unfold tailWord_5210917
  simp only [CollatzResearch.WordTrace]
  refine ⟨190057756862745137615871005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126705171241830091743914003 190057756862745137615871005)
  ·
    refine ⟨71271658823529426605951627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190057756862745137615871005 71271658823529426605951627)
    ·
      refine ⟨106907488235294139908927441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71271658823529426605951627 106907488235294139908927441)
      ·
        refine ⟨80180616176470604931695581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106907488235294139908927441 80180616176470604931695581)
        ·
          refine ⟨30067731066176476849385843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80180616176470604931695581 30067731066176476849385843)
          ·
            refine ⟨45101596599264715274078765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30067731066176476849385843 45101596599264715274078765)
            ·
              refine ⟨16913098724724268227779537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45101596599264715274078765 16913098724724268227779537)
              ·
                refine ⟨12684824043543201170834653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16913098724724268227779537 12684824043543201170834653)
                ·
                  refine ⟨4756809016328700439062995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12684824043543201170834653 4756809016328700439062995)
                  ·
                    refine ⟨7135213524493050658594493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4756809016328700439062995 7135213524493050658594493)
                    ·
                      refine ⟨2675705071684893996972935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7135213524493050658594493 2675705071684893996972935)
                      ·
                        rfl

theorem cell23_5210917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_5210917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210917 prefixEnd_5210917 := by exact prefixLift 5210917
  have htrace : WordTrace (prefixWord ++ tailWord_5210917) baseStart_5210917 baseEnd_5210917 := by
    simpa [prefixWord, tailWord_5210917, baseEnd_5210917] using wordTrace_append hprefix tailTrace_5210917
  have hstable : (prefixWord ++ tailWord_5210917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210917).length < 2 ^ (prefixWord ++ tailWord_5210917).sum := by decide
  have hdescent : baseEnd_5210917 < baseStart_5210917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210920 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 3, 5]
def baseStart_5210920 : Nat := 118140960795 + 5210920 * 2 ^ 59
def prefixEnd_5210920 : Nat := 4983230072969 + 3 ^ 40 * 5210920 * 2
def baseEnd_5210920 : Nat := 891902204042285828411807

theorem tailTrace_5210920 : CollatzResearch.WordTrace tailWord_5210920 prefixEnd_5210920 891902204042285828411807 := by
  unfold tailWord_5210920
  simp only [CollatzResearch.WordTrace]
  refine ⟨95028933140867134564115107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126705244187822846085486809 95028933140867134564115107)
  ·
    refine ⟨142543399711300701846172661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95028933140867134564115107 142543399711300701846172661)
    ·
      refine ⟨13363443722934440798078687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142543399711300701846172661 13363443722934440798078687)
      ·
        refine ⟨20045165584401661197118031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13363443722934440798078687 20045165584401661197118031)
        ·
          refine ⟨30067748376602491795677047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20045165584401661197118031 30067748376602491795677047)
          ·
            refine ⟨45101622564903737693515571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30067748376602491795677047 45101622564903737693515571)
            ·
              refine ⟨67652433847355606540273357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45101622564903737693515571 67652433847355606540273357)
              ·
                refine ⟨25369662692758352452602509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67652433847355606540273357 25369662692758352452602509)
                ·
                  refine ⟨9513623509784382169725941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25369662692758352452602509 9513623509784382169725941)
                  ·
                    refine ⟨891902204042285828411807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9513623509784382169725941 891902204042285828411807)
                    ·
                      rfl

theorem cell23_5210920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_5210920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210920 prefixEnd_5210920 := by exact prefixLift 5210920
  have htrace : WordTrace (prefixWord ++ tailWord_5210920) baseStart_5210920 baseEnd_5210920 := by
    simpa [prefixWord, tailWord_5210920, baseEnd_5210920] using wordTrace_append hprefix tailTrace_5210920
  have hstable : (prefixWord ++ tailWord_5210920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210920).length < 2 ^ (prefixWord ++ tailWord_5210920).sum := by decide
  have hdescent : baseEnd_5210920 < baseStart_5210920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210960 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 3]
def baseStart_5210960 : Nat := 118140960795 + 5210960 * 2 ^ 59
def prefixEnd_5210960 : Nat := 4983230072969 + 3 ^ 40 * 5210960 * 2
def baseEnd_5210960 : Nat := 2675727151353037328735237

theorem tailTrace_5210960 : CollatzResearch.WordTrace tailWord_5210960 prefixEnd_5210960 2675727151353037328735237 := by
  unfold tailWord_5210960
  simp only [CollatzResearch.WordTrace]
  refine ⟨95029662600794677979843167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126706216801059570639790889 95029662600794677979843167)
  ·
    refine ⟨142544493901192016969764751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95029662600794677979843167 142544493901192016969764751)
    ·
      refine ⟨213816740851788025454647127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142544493901192016969764751 213816740851788025454647127)
      ·
        refine ⟨320725111277682038181970691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213816740851788025454647127 320725111277682038181970691)
        ·
          refine ⟨481087666916523057272956037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320725111277682038181970691 481087666916523057272956037)
          ·
            refine ⟨90203937546848073238679257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 481087666916523057272956037 90203937546848073238679257)
            ·
              refine ⟨67652953160136054929009443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90203937546848073238679257 67652953160136054929009443)
              ·
                refine ⟨101479429740204082393514165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67652953160136054929009443 101479429740204082393514165)
                ·
                  refine ⟨9513696538144132724391953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101479429740204082393514165 9513696538144132724391953)
                  ·
                    refine ⟨7135272403608099543293965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9513696538144132724391953 7135272403608099543293965)
                    ·
                      refine ⟨2675727151353037328735237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7135272403608099543293965 2675727151353037328735237)
                      ·
                        rfl

theorem cell23_5210960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 3].length) (baseStart_5210960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210960 prefixEnd_5210960 := by exact prefixLift 5210960
  have htrace : WordTrace (prefixWord ++ tailWord_5210960) baseStart_5210960 baseEnd_5210960 := by
    simpa [prefixWord, tailWord_5210960, baseEnd_5210960] using wordTrace_append hprefix tailTrace_5210960
  have hstable : (prefixWord ++ tailWord_5210960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210960).length < 2 ^ (prefixWord ++ tailWord_5210960).sum := by decide
  have hdescent : baseEnd_5210960 < baseStart_5210960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210967 : List Nat := [1, 1, 3, 2, 4, 3, 1, 1, 1, 6]
def baseStart_5210967 : Nat := 118140960795 + 5210967 * 2 ^ 59
def prefixEnd_5210967 : Nat := 4983230072969 + 3 ^ 40 * 5210967 * 2
def baseEnd_5210967 : Nat := 891910248572539600449235

theorem tailTrace_5210967 : CollatzResearch.WordTrace tailWord_5210967 prefixEnd_5210967 891910248572539600449235 := by
  unfold tailWord_5210967
  simp only [CollatzResearch.WordTrace]
  refine ⟨190059580512563996155191155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126706387008375997436794103 190059580512563996155191155)
  ·
    refine ⟨285089370768845994232786733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190059580512563996155191155 285089370768845994232786733)
    ·
      refine ⟨106908514038317247837295025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285089370768845994232786733 106908514038317247837295025)
      ·
        refine ⟨80181385528737935877971269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106908514038317247837295025 80181385528737935877971269)
        ·
          refine ⟨15034009786638362977119613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80181385528737935877971269 15034009786638362977119613)
          ·
            refine ⟨5637753669989386116419855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15034009786638362977119613 5637753669989386116419855)
            ·
              refine ⟨8456630504984079174629783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5637753669989386116419855 8456630504984079174629783)
              ·
                refine ⟨12684945757476118761944675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8456630504984079174629783 12684945757476118761944675)
                ·
                  refine ⟨19027418636214178142917013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12684945757476118761944675 19027418636214178142917013)
                  ·
                    refine ⟨891910248572539600449235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19027418636214178142917013 891910248572539600449235)
                    ·
                      rfl

theorem cell23_5210967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 6].length) (baseStart_5210967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210967 prefixEnd_5210967 := by exact prefixLift 5210967
  have htrace : WordTrace (prefixWord ++ tailWord_5210967) baseStart_5210967 baseEnd_5210967 := by
    simpa [prefixWord, tailWord_5210967, baseEnd_5210967] using wordTrace_append hprefix tailTrace_5210967
  have hstable : (prefixWord ++ tailWord_5210967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210967).length < 2 ^ (prefixWord ++ tailWord_5210967).sum := by decide
  have hdescent : baseEnd_5210967 < baseStart_5210967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210970 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6]
def baseStart_5210970 : Nat := 118140960795 + 5210970 * 2 ^ 59
def prefixEnd_5210970 : Nat := 4983230072969 + 3 ^ 40 * 5210970 * 2
def baseEnd_5210970 : Nat := 2675732286159582289610191

theorem tailTrace_5210970 : CollatzResearch.WordTrace tailWord_5210970 prefixEnd_5210970 2675732286159582289610191 := by
  unfold tailWord_5210970
  simp only [CollatzResearch.WordTrace]
  refine ⟨47514922482888281916887591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126706459954368751778366909 47514922482888281916887591)
  ·
    refine ⟨71272383724332422875331387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47514922482888281916887591 71272383724332422875331387)
    ·
      refine ⟨106908575586498634312997081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71272383724332422875331387 106908575586498634312997081)
      ·
        refine ⟨80181431689873975734747811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106908575586498634312997081 80181431689873975734747811)
        ·
          refine ⟨120272147534810963602121717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80181431689873975734747811 120272147534810963602121717)
          ·
            refine ⟨11275513831388527837698911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120272147534810963602121717 11275513831388527837698911)
            ·
              refine ⟨16913270747082791756548367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11275513831388527837698911 16913270747082791756548367)
              ·
                refine ⟨25369906120624187634822551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16913270747082791756548367 25369906120624187634822551)
                ·
                  refine ⟨38054859180936281452233827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25369906120624187634822551 38054859180936281452233827)
                  ·
                    refine ⟨57082288771404422178350741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38054859180936281452233827 57082288771404422178350741)
                    ·
                      refine ⟨2675732286159582289610191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57082288771404422178350741 2675732286159582289610191)
                      ·
                        rfl

theorem cell23_5210970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_5210970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210970 prefixEnd_5210970 := by exact prefixLift 5210970
  have htrace : WordTrace (prefixWord ++ tailWord_5210970) baseStart_5210970 baseEnd_5210970 := by
    simpa [prefixWord, tailWord_5210970, baseEnd_5210970] using wordTrace_append hprefix tailTrace_5210970
  have hstable : (prefixWord ++ tailWord_5210970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210970).length < 2 ^ (prefixWord ++ tailWord_5210970).sum := by decide
  have hdescent : baseEnd_5210970 < baseStart_5210970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5210980 : List Nat := [2, 3, 1, 1, 4, 2, 1, 9]
def baseStart_5210980 : Nat := 118140960795 + 5210980 * 2 ^ 59
def prefixEnd_5210980 : Nat := 4983230072969 + 3 ^ 40 * 5210980 * 2
def baseEnd_5210980 : Nat := 99101385961708416684635

theorem tailTrace_5210980 : CollatzResearch.WordTrace tailWord_5210980 prefixEnd_5210980 99101385961708416684635 := by
  unfold tailWord_5210980
  simp only [CollatzResearch.WordTrace]
  refine ⟨95030027330758449687707197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126706703107677932916942929 95030027330758449687707197)
  ·
    refine ⟨35636260249034418632890199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95030027330758449687707197 35636260249034418632890199)
    ·
      refine ⟨53454390373551627949335299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35636260249034418632890199 53454390373551627949335299)
      ·
        refine ⟨80181585560327441924002949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53454390373551627949335299 80181585560327441924002949)
        ·
          refine ⟨15034047292561395360750553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80181585560327441924002949 15034047292561395360750553)
          ·
            refine ⟨11275535469421046520562915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15034047292561395360750553 11275535469421046520562915)
            ·
              refine ⟨16913303204131569780844373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11275535469421046520562915 16913303204131569780844373)
              ·
                refine ⟨99101385961708416684635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16913303204131569780844373 99101385961708416684635)
                ·
                  rfl

theorem cell23_5210980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 9].length) (baseStart_5210980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5210980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5210980 prefixEnd_5210980 := by exact prefixLift 5210980
  have htrace : WordTrace (prefixWord ++ tailWord_5210980) baseStart_5210980 baseEnd_5210980 := by
    simpa [prefixWord, tailWord_5210980, baseEnd_5210980] using wordTrace_append hprefix tailTrace_5210980
  have hstable : (prefixWord ++ tailWord_5210980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5210980).length < 2 ^ (prefixWord ++ tailWord_5210980).sum := by decide
  have hdescent : baseEnd_5210980 < baseStart_5210980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5210980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211007 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 4, 1, 3]
def baseStart_5211007 : Nat := 118140960795 + 5211007 * 2 ^ 59
def prefixEnd_5211007 : Nat := 4983230072969 + 3 ^ 40 * 5211007 * 2
def baseEnd_5211007 : Nat := 2675751284943798644847521

theorem tailTrace_5211007 : CollatzResearch.WordTrace tailWord_5211007 prefixEnd_5211007 2675751284943798644847521 := by
  unfold tailWord_5211007
  simp only [CollatzResearch.WordTrace]
  refine ⟨190061039432419082986647275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126707359621612721991098183 190061039432419082986647275)
  ·
    refine ⟨285091559148628624479970913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190061039432419082986647275 285091559148628624479970913)
    ·
      refine ⟨213818669361471468359978185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285091559148628624479970913 213818669361471468359978185)
      ·
        refine ⟨160364002021103601269983639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213818669361471468359978185 160364002021103601269983639)
        ·
          refine ⟨240546003031655401904975459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160364002021103601269983639 240546003031655401904975459)
          ·
            refine ⟨360819004547483102857463189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240546003031655401904975459 360819004547483102857463189)
            ·
              refine ⟨16913390838163270446443587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 360819004547483102857463189 16913390838163270446443587)
              ·
                refine ⟨25370086257244905669665381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16913390838163270446443587 25370086257244905669665381)
                ·
                  refine ⟨4756891173233419813062259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25370086257244905669665381 4756891173233419813062259)
                  ·
                    refine ⟨7135336759850129719593389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4756891173233419813062259 7135336759850129719593389)
                    ·
                      refine ⟨2675751284943798644847521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7135336759850129719593389 2675751284943798644847521)
                      ·
                        rfl

theorem cell23_5211007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 1, 3].length) (baseStart_5211007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211007 prefixEnd_5211007 := by exact prefixLift 5211007
  have htrace : WordTrace (prefixWord ++ tailWord_5211007) baseStart_5211007 baseEnd_5211007 := by
    simpa [prefixWord, tailWord_5211007, baseEnd_5211007] using wordTrace_append hprefix tailTrace_5211007
  have hstable : (prefixWord ++ tailWord_5211007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211007).length < 2 ^ (prefixWord ++ tailWord_5211007).sum := by decide
  have hdescent : baseEnd_5211007 < baseStart_5211007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211137 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_5211137 : Nat := 118140960795 + 5211137 * 2 ^ 59
def prefixEnd_5211137 : Nat := 4983230072969 + 3 ^ 40 * 5211137 * 2
def baseEnd_5211137 : Nat := 2675818037428883136221923

theorem tailTrace_5211137 : CollatzResearch.WordTrace tailWord_5211137 prefixEnd_5211137 2675818037428883136221923 := by
  unfold tailWord_5211137
  simp only [CollatzResearch.WordTrace]
  refine ⟨190065780921948115188879665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126710520614632076792586443 190065780921948115188879665)
  ·
    refine ⟨142549335691461086391659749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190065780921948115188879665 142549335691461086391659749)
    ·
      refine ⟨26728000442148953698436203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142549335691461086391659749 26728000442148953698436203)
      ·
        refine ⟨40092000663223430547654305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26728000442148953698436203 40092000663223430547654305)
        ·
          refine ⟨30069000497417572910740729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40092000663223430547654305 30069000497417572910740729)
          ·
            refine ⟨22551750373063179683055547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30069000497417572910740729 22551750373063179683055547)
            ·
              refine ⟨33827625559594769524583321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22551750373063179683055547 33827625559594769524583321)
              ·
                refine ⟨25370719169696077143437491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33827625559594769524583321 25370719169696077143437491)
                ·
                  refine ⟨38056078754544115715156237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25370719169696077143437491 38056078754544115715156237)
                  ·
                    refine ⟨14271029532954043393183589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38056078754544115715156237 14271029532954043393183589)
                    ·
                      refine ⟨2675818037428883136221923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14271029532954043393183589 2675818037428883136221923)
                      ·
                        rfl

theorem cell23_5211137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_5211137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211137 prefixEnd_5211137 := by exact prefixLift 5211137
  have htrace : WordTrace (prefixWord ++ tailWord_5211137) baseStart_5211137 baseEnd_5211137 := by
    simpa [prefixWord, tailWord_5211137, baseEnd_5211137] using wordTrace_append hprefix tailTrace_5211137
  have hstable : (prefixWord ++ tailWord_5211137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211137).length < 2 ^ (prefixWord ++ tailWord_5211137).sum := by decide
  have hdescent : baseEnd_5211137 < baseStart_5211137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211194 : List Nat := [3, 1, 1, 1, 3, 1, 6, 1, 6]
def baseStart_5211194 : Nat := 118140960795 + 5211194 * 2 ^ 59
def prefixEnd_5211194 : Nat := 4983230072969 + 3 ^ 40 * 5211194 * 2
def baseEnd_5211194 : Nat := 297316367314021045912129

theorem tailTrace_5211194 : CollatzResearch.WordTrace tailWord_5211194 prefixEnd_5211194 297316367314021045912129 := by
  unfold tailWord_5211194
  simp only [CollatzResearch.WordTrace]
  refine ⟨47516964970685403480926159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126711906588494409282469757 47516964970685403480926159)
  ·
    refine ⟨71275447456028105221389239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47516964970685403480926159 71275447456028105221389239)
    ·
      refine ⟨106913171184042157832083859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71275447456028105221389239 106913171184042157832083859)
      ·
        refine ⟨160369756776063236748125789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106913171184042157832083859 160369756776063236748125789)
        ·
          refine ⟨60138658791023713780547171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160369756776063236748125789 60138658791023713780547171)
          ·
            refine ⟨90207988186535570670820757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60138658791023713780547171 90207988186535570670820757)
            ·
              refine ⟨4228499446243854875194723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90207988186535570670820757 4228499446243854875194723)
              ·
                refine ⟨6342749169365782312792085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4228499446243854875194723 6342749169365782312792085)
                ·
                  refine ⟨297316367314021045912129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6342749169365782312792085 297316367314021045912129)
                  ·
                    rfl

theorem cell23_5211194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 6].length) (baseStart_5211194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211194 prefixEnd_5211194 := by exact prefixLift 5211194
  have htrace : WordTrace (prefixWord ++ tailWord_5211194) baseStart_5211194 baseEnd_5211194 := by
    simpa [prefixWord, tailWord_5211194, baseEnd_5211194] using wordTrace_append hprefix tailTrace_5211194
  have hstable : (prefixWord ++ tailWord_5211194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211194).length < 2 ^ (prefixWord ++ tailWord_5211194).sum := by decide
  have hdescent : baseEnd_5211194 < baseStart_5211194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211237 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 3, 6]
def baseStart_5211237 : Nat := 118140960795 + 5211237 * 2 ^ 59
def prefixEnd_5211237 : Nat := 4983230072969 + 3 ^ 40 * 5211237 * 2
def baseEnd_5211237 : Nat := 891956461831444248323821

theorem tailTrace_5211237 : CollatzResearch.WordTrace tailWord_5211237 prefixEnd_5211237 891956461831444248323821 := by
  unfold tailWord_5211237
  simp only [CollatzResearch.WordTrace]
  refine ⟨190069428221585832267519965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126712952147723888178346643 190069428221585832267519965)
  ·
    refine ⟨71276035583094687100319987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190069428221585832267519965 71276035583094687100319987)
    ·
      refine ⟨106914053374642030650479981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71276035583094687100319987 106914053374642030650479981)
      ·
        refine ⟨40092770015490761493929993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106914053374642030650479981 40092770015490761493929993)
        ·
          refine ⟨30069577511618071120447495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40092770015490761493929993 30069577511618071120447495)
          ·
            refine ⟨45104366267427106680671243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30069577511618071120447495 45104366267427106680671243)
            ·
              refine ⟨67656549401140660021006865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45104366267427106680671243 67656549401140660021006865)
              ·
                refine ⟨50742412050855495015755149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67656549401140660021006865 50742412050855495015755149)
                ·
                  refine ⟨19028404519070810630908181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50742412050855495015755149 19028404519070810630908181)
                  ·
                    refine ⟨891956461831444248323821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19028404519070810630908181 891956461831444248323821)
                    ·
                      rfl

theorem cell23_5211237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_5211237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211237 prefixEnd_5211237 := by exact prefixLift 5211237
  have htrace : WordTrace (prefixWord ++ tailWord_5211237) baseStart_5211237 baseEnd_5211237 := by
    simpa [prefixWord, tailWord_5211237, baseEnd_5211237] using wordTrace_append hprefix tailTrace_5211237
  have hstable : (prefixWord ++ tailWord_5211237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211237).length < 2 ^ (prefixWord ++ tailWord_5211237).sum := by decide
  have hdescent : baseEnd_5211237 < baseStart_5211237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211247 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 5]
def baseStart_5211247 : Nat := 118140960795 + 5211247 * 2 ^ 59
def prefixEnd_5211247 : Nat := 4983230072969 + 3 ^ 40 * 5211247 * 2
def baseEnd_5211247 : Nat := 2675874520300877705846417

theorem tailTrace_5211247 : CollatzResearch.WordTrace tailWord_5211247 prefixEnd_5211247 2675874520300877705846417 := by
  unfold tailWord_5211247
  simp only [CollatzResearch.WordTrace]
  refine ⟨190069792951549603975383995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126713195301033069316922663 190069792951549603975383995)
  ·
    refine ⟨285104689427324405963075993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190069792951549603975383995 285104689427324405963075993)
    ·
      refine ⟨213828517070493304472306995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285104689427324405963075993 213828517070493304472306995)
      ·
        refine ⟨320742775605739956708460493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213828517070493304472306995 320742775605739956708460493)
        ·
          refine ⟨120278540852152483765672685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320742775605739956708460493 120278540852152483765672685)
          ·
            refine ⟨45104452819557181412127257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120278540852152483765672685 45104452819557181412127257)
            ·
              refine ⟨33828339614667886059095443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45104452819557181412127257 33828339614667886059095443)
              ·
                refine ⟨50742509422001829088643165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33828339614667886059095443 50742509422001829088643165)
                ·
                  refine ⟨19028441033250685908241187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50742509422001829088643165 19028441033250685908241187)
                  ·
                    refine ⟨28542661549876028862361781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19028441033250685908241187 28542661549876028862361781)
                    ·
                      refine ⟨2675874520300877705846417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28542661549876028862361781 2675874520300877705846417)
                      ·
                        rfl

theorem cell23_5211247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 5].length) (baseStart_5211247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211247 prefixEnd_5211247 := by exact prefixLift 5211247
  have htrace : WordTrace (prefixWord ++ tailWord_5211247) baseStart_5211247 baseEnd_5211247 := by
    simpa [prefixWord, tailWord_5211247, baseEnd_5211247] using wordTrace_append hprefix tailTrace_5211247
  have hstable : (prefixWord ++ tailWord_5211247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211247).length < 2 ^ (prefixWord ++ tailWord_5211247).sum := by decide
  have hdescent : baseEnd_5211247 < baseStart_5211247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211264 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 3]
def baseStart_5211264 : Nat := 118140960795 + 5211264 * 2 ^ 59
def prefixEnd_5211264 : Nat := 4983230072969 + 3 ^ 40 * 5211264 * 2
def baseEnd_5211264 : Nat := 2675883249472004139333839

theorem tailTrace_5211264 : CollatzResearch.WordTrace tailWord_5211264 prefixEnd_5211264 2675883249472004139333839 := by
  unfold tailWord_5211264
  simp only [CollatzResearch.WordTrace]
  refine ⟨95035206496244007939376423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126713608661658677252501897 95035206496244007939376423)
  ·
    refine ⟨142552809744366011909064635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95035206496244007939376423 142552809744366011909064635)
    ·
      refine ⟨213829214616549017863596953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142552809744366011909064635 213829214616549017863596953)
      ·
        refine ⟨160371910962411763397697715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213829214616549017863596953 160371910962411763397697715)
        ·
          refine ⟨240557866443617645096546573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160371910962411763397697715 240557866443617645096546573)
          ·
            refine ⟨90209199916356616911204965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240557866443617645096546573 90209199916356616911204965)
            ·
              refine ⟨16914224984316865670850931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90209199916356616911204965 16914224984316865670850931)
              ·
                refine ⟨25371337476475298506276397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16914224984316865670850931 25371337476475298506276397)
                ·
                  refine ⟨9514251553678236939853649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25371337476475298506276397 9514251553678236939853649)
                  ·
                    refine ⟨7135688665258677704890237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9514251553678236939853649 7135688665258677704890237)
                    ·
                      refine ⟨2675883249472004139333839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7135688665258677704890237 2675883249472004139333839)
                      ·
                        rfl

theorem cell23_5211264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 3].length) (baseStart_5211264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211264 prefixEnd_5211264 := by exact prefixLift 5211264
  have htrace : WordTrace (prefixWord ++ tailWord_5211264) baseStart_5211264 baseEnd_5211264 := by
    simpa [prefixWord, tailWord_5211264, baseEnd_5211264] using wordTrace_append hprefix tailTrace_5211264
  have hstable : (prefixWord ++ tailWord_5211264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211264).length < 2 ^ (prefixWord ++ tailWord_5211264).sum := by decide
  have hdescent : baseEnd_5211264 < baseStart_5211264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211274 : List Nat := [3, 1, 2, 3, 1, 1, 1, 4, 1, 2, 4]
def baseStart_5211274 : Nat := 118140960795 + 5211274 * 2 ^ 59
def prefixEnd_5211274 : Nat := 4983230072969 + 3 ^ 40 * 5211274 * 2
def baseEnd_5211274 : Nat := 2675888384278549100208793

theorem tailTrace_5211274 : CollatzResearch.WordTrace tailWord_5211274 prefixEnd_5211274 2675888384278549100208793 := by
  unfold tailWord_5211274
  simp only [CollatzResearch.WordTrace]
  refine ⟨47517694430612946896654219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126713851814967858391077917 47517694430612946896654219)
  ·
    refine ⟨71276541645919420344981329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47517694430612946896654219 71276541645919420344981329)
    ·
      refine ⟨53457406234439565258735997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71276541645919420344981329 53457406234439565258735997)
      ·
        refine ⟨20046527337914836972025999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53457406234439565258735997 20046527337914836972025999)
        ·
          refine ⟨30069791006872255458038999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20046527337914836972025999 30069791006872255458038999)
          ·
            refine ⟨45104686510308383187058499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30069791006872255458038999 45104686510308383187058499)
            ·
              refine ⟨67657029765462574780587749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45104686510308383187058499 67657029765462574780587749)
              ·
                refine ⟨12685693081024232771360203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67657029765462574780587749 12685693081024232771360203)
                ·
                  refine ⟨19028539621536349157040305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12685693081024232771360203 19028539621536349157040305)
                  ·
                    refine ⟨14271404716152261867780229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19028539621536349157040305 14271404716152261867780229)
                    ·
                      refine ⟨2675888384278549100208793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14271404716152261867780229 2675888384278549100208793)
                      ·
                        rfl

theorem cell23_5211274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_5211274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211274 prefixEnd_5211274 := by exact prefixLift 5211274
  have htrace : WordTrace (prefixWord ++ tailWord_5211274) baseStart_5211274 baseEnd_5211274 := by
    simpa [prefixWord, tailWord_5211274, baseEnd_5211274] using wordTrace_append hprefix tailTrace_5211274
  have hstable : (prefixWord ++ tailWord_5211274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211274).length < 2 ^ (prefixWord ++ tailWord_5211274).sum := by decide
  have hdescent : baseEnd_5211274 < baseStart_5211274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211278 : List Nat := [4, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4]
def baseStart_5211278 : Nat := 118140960795 + 5211278 * 2 ^ 59
def prefixEnd_5211278 : Nat := 4983230072969 + 3 ^ 40 * 5211278 * 2
def baseEnd_5211278 : Nat := 2675890438201167084558775

theorem tailTrace_5211278 : CollatzResearch.WordTrace tailWord_5211278 prefixEnd_5211278 2675890438201167084558775 := by
  unfold tailWord_5211278
  simp only [CollatzResearch.WordTrace]
  refine ⟨23758865451804662033720311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126713949076291530846508325 23758865451804662033720311)
  ·
    refine ⟨35638298177706993050580467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23758865451804662033720311 35638298177706993050580467)
    ·
      refine ⟨53457447266560489575870701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35638298177706993050580467 53457447266560489575870701)
      ·
        refine ⟨20046542724960183590951513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53457447266560489575870701 20046542724960183590951513)
        ·
          refine ⟨15034907043720137693213635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20046542724960183590951513 15034907043720137693213635)
          ·
            refine ⟨22552360565580206539820453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15034907043720137693213635 22552360565580206539820453)
            ·
              refine ⟨4228567606046288726216335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22552360565580206539820453 4228567606046288726216335)
              ·
                refine ⟨6342851409069433089324503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4228567606046288726216335 6342851409069433089324503)
                ·
                  refine ⟨9514277113604149633986755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6342851409069433089324503 9514277113604149633986755)
                  ·
                    refine ⟨14271415670406224450980133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9514277113604149633986755 14271415670406224450980133)
                    ·
                      refine ⟨2675890438201167084558775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14271415670406224450980133 2675890438201167084558775)
                      ·
                        rfl

theorem cell23_5211278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_5211278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211278 prefixEnd_5211278 := by exact prefixLift 5211278
  have htrace : WordTrace (prefixWord ++ tailWord_5211278) baseStart_5211278 baseEnd_5211278 := by
    simpa [prefixWord, tailWord_5211278, baseEnd_5211278] using wordTrace_append hprefix tailTrace_5211278
  have hstable : (prefixWord ++ tailWord_5211278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211278).length < 2 ^ (prefixWord ++ tailWord_5211278).sum := by decide
  have hdescent : baseEnd_5211278 < baseStart_5211278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211288 : List Nat := [2, 1, 2, 4, 2, 3, 1, 2, 2, 4]
def baseStart_5211288 : Nat := 118140960795 + 5211288 * 2 ^ 59
def prefixEnd_5211288 : Nat := 4983230072969 + 3 ^ 40 * 5211288 * 2
def baseEnd_5211288 : Nat := 891965191002570681811243

theorem tailTrace_5211288 : CollatzResearch.WordTrace tailWord_5211288 prefixEnd_5211288 891965191002570681811243 := by
  unfold tailWord_5211288
  simp only [CollatzResearch.WordTrace]
  refine ⟨95035644172200533988813259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126714192229600711985084345 95035644172200533988813259)
  ·
    refine ⟨142553466258300800983219889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95035644172200533988813259 142553466258300800983219889)
    ·
      refine ⟨106915099693725600737414917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142553466258300800983219889 106915099693725600737414917)
      ·
        refine ⟨20046581192573550138265297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106915099693725600737414917 20046581192573550138265297)
        ·
          refine ⟨15034935894430162603698973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20046581192573550138265297 15034935894430162603698973)
          ·
            refine ⟨5638100960411310976387115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15034935894430162603698973 5638100960411310976387115)
            ·
              refine ⟨8457151440616966464580673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5638100960411310976387115 8457151440616966464580673)
              ·
                refine ⟨6342863580462724848435505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8457151440616966464580673 6342863580462724848435505)
                ·
                  refine ⟨4757147685347043636326629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6342863580462724848435505 4757147685347043636326629)
                  ·
                    refine ⟨891965191002570681811243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4757147685347043636326629 891965191002570681811243)
                    ·
                      rfl

theorem cell23_5211288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 2, 4].length) (baseStart_5211288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211288 prefixEnd_5211288 := by exact prefixLift 5211288
  have htrace : WordTrace (prefixWord ++ tailWord_5211288) baseStart_5211288 baseEnd_5211288 := by
    simpa [prefixWord, tailWord_5211288, baseEnd_5211288] using wordTrace_append hprefix tailTrace_5211288
  have hstable : (prefixWord ++ tailWord_5211288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211288).length < 2 ^ (prefixWord ++ tailWord_5211288).sum := by decide
  have hdescent : baseEnd_5211288 < baseStart_5211288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211295 : List Nat := [1, 1, 2, 6, 2, 1, 2, 1, 3, 2, 2]
def baseStart_5211295 : Nat := 118140960795 + 5211295 * 2 ^ 59
def prefixEnd_5211295 : Nat := 4983230072969 + 3 ^ 40 * 5211295 * 2
def baseEnd_5211295 : Nat := 2675899167372293518046197

theorem tailTrace_5211295 : CollatzResearch.WordTrace tailWord_5211295 prefixEnd_5211295 2675899167372293518046197 := by
  unfold tailWord_5211295
  simp only [CollatzResearch.WordTrace]
  refine ⟨190071543655375708173131339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126714362436917138782087559 190071543655375708173131339)
  ·
    refine ⟨285107315483063562259697009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190071543655375708173131339 285107315483063562259697009)
    ·
      refine ⟨213830486612297671694772757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285107315483063562259697009 213830486612297671694772757)
      ·
        refine ⟨10023304059951453360692473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 213830486612297671694772757 10023304059951453360692473)
        ·
          refine ⟨7517478044963590020519355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10023304059951453360692473 7517478044963590020519355)
          ·
            refine ⟨11276217067445385030779033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7517478044963590020519355 11276217067445385030779033)
            ·
              refine ⟨8457162800584038773084275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11276217067445385030779033 8457162800584038773084275)
              ·
                refine ⟨12685744200876058159626413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8457162800584038773084275 12685744200876058159626413)
                ·
                  refine ⟨4757154075328521809859905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12685744200876058159626413 4757154075328521809859905)
                  ·
                    refine ⟨3567865556496391357394929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4757154075328521809859905 3567865556496391357394929)
                    ·
                      refine ⟨2675899167372293518046197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3567865556496391357394929 2675899167372293518046197)
                      ·
                        rfl

theorem cell23_5211295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_5211295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211295 prefixEnd_5211295 := by exact prefixLift 5211295
  have htrace : WordTrace (prefixWord ++ tailWord_5211295) baseStart_5211295 baseEnd_5211295 := by
    simpa [prefixWord, tailWord_5211295, baseEnd_5211295] using wordTrace_append hprefix tailTrace_5211295
  have hstable : (prefixWord ++ tailWord_5211295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211295).length < 2 ^ (prefixWord ++ tailWord_5211295).sum := by decide
  have hdescent : baseEnd_5211295 < baseStart_5211295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211311 : List Nat := [1, 1, 2, 1, 2, 3, 2, 5, 2, 1, 3]
def baseStart_5211311 : Nat := 118140960795 + 5211311 * 2 ^ 59
def prefixEnd_5211311 : Nat := 4983230072969 + 3 ^ 40 * 5211311 * 2
def baseEnd_5211311 : Nat := 2675907383062765455446123

theorem tailTrace_5211311 : CollatzResearch.WordTrace tailWord_5211311 prefixEnd_5211311 2675907383062765455446123 := by
  unfold tailWord_5211311
  simp only [CollatzResearch.WordTrace]
  refine ⟨190072127223317742905713787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126714751482211828603809191 190072127223317742905713787)
  ·
    refine ⟨285108190834976614358570681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190072127223317742905713787 285108190834976614358570681)
    ·
      refine ⟨213831143126232460768928011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285108190834976614358570681 213831143126232460768928011)
      ·
        refine ⟨320746714689348691153392017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213831143126232460768928011 320746714689348691153392017)
        ·
          refine ⟨240560036017011518365044013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320746714689348691153392017 240560036017011518365044013)
          ·
            refine ⟨90210013506379319386891505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240560036017011518365044013 90210013506379319386891505)
            ·
              refine ⟨67657510129784489540168629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90210013506379319386891505 67657510129784489540168629)
              ·
                refine ⟨6342891574667295894390809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67657510129784489540168629 6342891574667295894390809)
                ·
                  refine ⟨4757168681000471920793107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6342891574667295894390809 4757168681000471920793107)
                  ·
                    refine ⟨7135753021500707881189661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4757168681000471920793107 7135753021500707881189661)
                    ·
                      refine ⟨2675907383062765455446123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7135753021500707881189661 2675907383062765455446123)
                      ·
                        rfl

theorem cell23_5211311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 1, 3].length) (baseStart_5211311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211311 prefixEnd_5211311 := by exact prefixLift 5211311
  have htrace : WordTrace (prefixWord ++ tailWord_5211311) baseStart_5211311 baseEnd_5211311 := by
    simpa [prefixWord, tailWord_5211311, baseEnd_5211311] using wordTrace_append hprefix tailTrace_5211311
  have hstable : (prefixWord ++ tailWord_5211311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211311).length < 2 ^ (prefixWord ++ tailWord_5211311).sum := by decide
  have hdescent : baseEnd_5211311 < baseStart_5211311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211318 : List Nat := [5, 1, 3, 2, 1, 1, 1, 9]
def baseStart_5211318 : Nat := 118140960795 + 5211318 * 2 ^ 59
def prefixEnd_5211318 : Nat := 4983230072969 + 3 ^ 40 * 5211318 * 2
def baseEnd_5211318 : Nat := 99107813978790626965133

theorem tailTrace_5211318 : CollatzResearch.WordTrace tailWord_5211318 prefixEnd_5211318 99107813978790626965133 := by
  unfold tailWord_5211318
  simp only [CollatzResearch.WordTrace]
  refine ⟨11879523908393273943826163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126714921689528255400812405 11879523908393273943826163)
  ·
    refine ⟨17819285862589910915739245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11879523908393273943826163 17819285862589910915739245)
    ·
      refine ⟨6682232198471216593402217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17819285862589910915739245 6682232198471216593402217)
      ·
        refine ⟨5011674148853412445051663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6682232198471216593402217 5011674148853412445051663)
        ·
          refine ⟨7517511223280118667577495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5011674148853412445051663 7517511223280118667577495)
          ·
            refine ⟨11276266834920178001366243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7517511223280118667577495 11276266834920178001366243)
            ·
              refine ⟨16914400252380267002049365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11276266834920178001366243 16914400252380267002049365)
              ·
                refine ⟨99107813978790626965133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16914400252380267002049365 99107813978790626965133)
                ·
                  rfl

theorem cell23_5211318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_5211318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211318 prefixEnd_5211318 := by exact prefixLift 5211318
  have htrace : WordTrace (prefixWord ++ tailWord_5211318) baseStart_5211318 baseEnd_5211318 := by
    simpa [prefixWord, tailWord_5211318, baseEnd_5211318] using wordTrace_append hprefix tailTrace_5211318
  have hstable : (prefixWord ++ tailWord_5211318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211318).length < 2 ^ (prefixWord ++ tailWord_5211318).sum := by decide
  have hdescent : baseEnd_5211318 < baseStart_5211318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211324 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 2, 2, 5]
def baseStart_5211324 : Nat := 118140960795 + 5211324 * 2 ^ 59
def prefixEnd_5211324 : Nat := 4983230072969 + 3 ^ 40 * 5211324 * 2
def baseEnd_5211324 : Nat := 2675914058311273904583563

theorem tailTrace_5211324 : CollatzResearch.WordTrace tailWord_5211324 prefixEnd_5211324 2675914058311273904583563 := by
  unfold tailWord_5211324
  simp only [CollatzResearch.WordTrace]
  refine ⟨95036300686135323062968513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126715067581513764083958017 95036300686135323062968513)
  ·
    refine ⟨71277225514601492297226385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95036300686135323062968513 71277225514601492297226385)
    ·
      refine ⟨53457919135951119222919789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71277225514601492297226385 53457919135951119222919789)
      ·
        refine ⟨20046719675981669708594921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53457919135951119222919789 20046719675981669708594921)
        ·
          refine ⟨15035039756986252281446191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20046719675981669708594921 15035039756986252281446191)
          ·
            refine ⟨22552559635479378422169287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15035039756986252281446191 22552559635479378422169287)
            ·
              refine ⟨33828839453219067633253931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22552559635479378422169287 33828839453219067633253931)
              ·
                refine ⟨50743259179828601449880897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33828839453219067633253931 50743259179828601449880897)
                ·
                  refine ⟨38057444384871451087410673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50743259179828601449880897 38057444384871451087410673)
                  ·
                    refine ⟨28543083288653588315558005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38057444384871451087410673 28543083288653588315558005)
                    ·
                      refine ⟨2675914058311273904583563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28543083288653588315558005 2675914058311273904583563)
                      ·
                        rfl

theorem cell23_5211324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_5211324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211324 prefixEnd_5211324 := by exact prefixLift 5211324
  have htrace : WordTrace (prefixWord ++ tailWord_5211324) baseStart_5211324 baseEnd_5211324 := by
    simpa [prefixWord, tailWord_5211324, baseEnd_5211324] using wordTrace_append hprefix tailTrace_5211324
  have hstable : (prefixWord ++ tailWord_5211324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211324).length < 2 ^ (prefixWord ++ tailWord_5211324).sum := by decide
  have hdescent : baseEnd_5211324 < baseStart_5211324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211327 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 1, 8]
def baseStart_5211327 : Nat := 118140960795 + 5211327 * 2 ^ 59
def prefixEnd_5211327 : Nat := 4983230072969 + 3 ^ 40 * 5211327 * 2
def baseEnd_5211327 : Nat := 891971866251079130948683

theorem tailTrace_5211327 : CollatzResearch.WordTrace tailWord_5211327 prefixEnd_5211327 891971866251079130948683 := by
  unfold tailWord_5211327
  simp only [CollatzResearch.WordTrace]
  refine ⟨190072710791259777638296235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126715140527506518425530823 190072710791259777638296235)
  ·
    refine ⟨285109066186889666457444353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190072710791259777638296235 285109066186889666457444353)
    ·
      refine ⟨213831799640167249843083265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285109066186889666457444353 213831799640167249843083265)
      ·
        refine ⟨160373849730125437382312449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213831799640167249843083265 160373849730125437382312449)
        ·
          refine ⟨120280387297594078036734337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160373849730125437382312449 120280387297594078036734337)
          ·
            refine ⟨90210290473195558527550753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120280387297594078036734337 90210290473195558527550753)
            ·
              refine ⟨67657717854896668895663065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90210290473195558527550753 67657717854896668895663065)
              ·
                refine ⟨50743288391172501671747299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67657717854896668895663065 50743288391172501671747299)
                ·
                  refine ⟨76114932586758752507620949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50743288391172501671747299 76114932586758752507620949)
                  ·
                    refine ⟨891971866251079130948683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76114932586758752507620949 891971866251079130948683)
                    ·
                      rfl

theorem cell23_5211327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 8].length) (baseStart_5211327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211327 prefixEnd_5211327 := by exact prefixLift 5211327
  have htrace : WordTrace (prefixWord ++ tailWord_5211327) baseStart_5211327 baseEnd_5211327 := by
    simpa [prefixWord, tailWord_5211327, baseEnd_5211327] using wordTrace_append hprefix tailTrace_5211327
  have hstable : (prefixWord ++ tailWord_5211327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211327).length < 2 ^ (prefixWord ++ tailWord_5211327).sum := by decide
  have hdescent : baseEnd_5211327 < baseStart_5211327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211329 : List Nat := [1, 2, 6, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_5211329 : Nat := 118140960795 + 5211329 * 2 ^ 59
def prefixEnd_5211329 : Nat := 4983230072969 + 3 ^ 40 * 5211329 * 2
def baseEnd_5211329 : Nat := 2675916625714546385021041

theorem tailTrace_5211329 : CollatzResearch.WordTrace tailWord_5211329 prefixEnd_5211329 2675916625714546385021041 := by
  unfold tailWord_5211329
  simp only [CollatzResearch.WordTrace]
  refine ⟨190072783737252531979869041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126715189158168354653246027 190072783737252531979869041)
  ·
    refine ⟨142554587802939398984901781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190072783737252531979869041 142554587802939398984901781)
    ·
      refine ⟨6682246303262784327417271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 142554587802939398984901781 6682246303262784327417271)
      ·
        refine ⟨10023369454894176491125907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6682246303262784327417271 10023369454894176491125907)
        ·
          refine ⟨15035054182341264736688861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10023369454894176491125907 15035054182341264736688861)
          ·
            refine ⟨5638145318377974276258323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15035054182341264736688861 5638145318377974276258323)
            ·
              refine ⟨8457217977566961414387485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5638145318377974276258323 8457217977566961414387485)
              ·
                refine ⟨3171456741587610530395307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8457217977566961414387485 3171456741587610530395307)
                ·
                  refine ⟨4757185112381415795592961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3171456741587610530395307 4757185112381415795592961)
                  ·
                    refine ⟨3567888834286061846694721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4757185112381415795592961 3567888834286061846694721)
                    ·
                      refine ⟨2675916625714546385021041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3567888834286061846694721 2675916625714546385021041)
                      ·
                        rfl

theorem cell23_5211329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_5211329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211329 prefixEnd_5211329 := by exact prefixLift 5211329
  have htrace : WordTrace (prefixWord ++ tailWord_5211329) baseStart_5211329 baseEnd_5211329 := by
    simpa [prefixWord, tailWord_5211329, baseEnd_5211329] using wordTrace_append hprefix tailTrace_5211329
  have hstable : (prefixWord ++ tailWord_5211329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211329).length < 2 ^ (prefixWord ++ tailWord_5211329).sum := by decide
  have hdescent : baseEnd_5211329 < baseStart_5211329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211338 : List Nat := [3, 1, 2, 1, 3, 2, 2, 3, 1, 3, 2]
def baseStart_5211338 : Nat := 118140960795 + 5211338 * 2 ^ 59
def prefixEnd_5211338 : Nat := 4983230072969 + 3 ^ 40 * 5211338 * 2
def baseEnd_5211338 : Nat := 2675921247040436849808499

theorem tailTrace_5211338 : CollatzResearch.WordTrace tailWord_5211338 prefixEnd_5211338 2675921247040436849808499 := by
  unfold tailWord_5211338
  simp only [CollatzResearch.WordTrace]
  refine ⟨47518277998554981629236667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126715407996146617677964445 47518277998554981629236667)
  ·
    refine ⟨71277416997832472443855001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47518277998554981629236667 71277416997832472443855001)
    ·
      refine ⟨53458062748374354332891251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71277416997832472443855001 53458062748374354332891251)
      ·
        refine ⟨80187094122561531499336877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53458062748374354332891251 80187094122561531499336877)
        ·
          refine ⟨30070160295960574312251329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80187094122561531499336877 30070160295960574312251329)
          ·
            refine ⟨22552620221970430734188497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30070160295960574312251329 22552620221970430734188497)
            ·
              refine ⟨16914465166477823050641373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22552620221970430734188497 16914465166477823050641373)
              ·
                refine ⟨6342924437429183643990515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16914465166477823050641373 6342924437429183643990515)
                ·
                  refine ⟨9514386656143775465985773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6342924437429183643990515 9514386656143775465985773)
                  ·
                    refine ⟨3567894996053915799744665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9514386656143775465985773 3567894996053915799744665)
                    ·
                      refine ⟨2675921247040436849808499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3567894996053915799744665 2675921247040436849808499)
                      ·
                        rfl

theorem cell23_5211338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 1, 3, 2].length) (baseStart_5211338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211338 prefixEnd_5211338 := by exact prefixLift 5211338
  have htrace : WordTrace (prefixWord ++ tailWord_5211338) baseStart_5211338 baseEnd_5211338 := by
    simpa [prefixWord, tailWord_5211338, baseEnd_5211338] using wordTrace_append hprefix tailTrace_5211338
  have hstable : (prefixWord ++ tailWord_5211338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211338).length < 2 ^ (prefixWord ++ tailWord_5211338).sum := by decide
  have hdescent : baseEnd_5211338 < baseStart_5211338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211354 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3]
def baseStart_5211354 : Nat := 118140960795 + 5211354 * 2 ^ 59
def prefixEnd_5211354 : Nat := 4983230072969 + 3 ^ 40 * 5211354 * 2
def baseEnd_5211354 : Nat := 2675929462730908787208425

theorem tailTrace_5211354 : CollatzResearch.WordTrace tailWord_5211354 prefixEnd_5211354 2675929462730908787208425 := by
  unfold tailWord_5211354
  simp only [CollatzResearch.WordTrace]
  refine ⟨47518423890540490312382279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126715797041441307499686077 47518423890540490312382279)
  ·
    refine ⟨71277635835810735468573419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47518423890540490312382279 71277635835810735468573419)
    ·
      refine ⟨106916453753716103202860129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71277635835810735468573419 106916453753716103202860129)
      ·
        refine ⟨80187340315287077402145097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106916453753716103202860129 80187340315287077402145097)
        ·
          refine ⟨60140505236465308051608823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80187340315287077402145097 60140505236465308051608823)
          ·
            refine ⟨90210757854697962077413235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60140505236465308051608823 90210757854697962077413235)
            ·
              refine ⟨135316136782046943116119853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90210757854697962077413235 135316136782046943116119853)
              ·
                refine ⟨50743551293267603668544945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135316136782046943116119853 50743551293267603668544945)
                ·
                  refine ⟨38057663469950702751408709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50743551293267603668544945 38057663469950702751408709)
                  ·
                    refine ⟨7135811900615756765889133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38057663469950702751408709 7135811900615756765889133)
                    ·
                      refine ⟨2675929462730908787208425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7135811900615756765889133 2675929462730908787208425)
                      ·
                        rfl

theorem cell23_5211354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_5211354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211354 prefixEnd_5211354 := by exact prefixLift 5211354
  have htrace : WordTrace (prefixWord ++ tailWord_5211354) baseStart_5211354 baseEnd_5211354 := by
    simpa [prefixWord, tailWord_5211354, baseEnd_5211354] using wordTrace_append hprefix tailTrace_5211354
  have hstable : (prefixWord ++ tailWord_5211354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211354).length < 2 ^ (prefixWord ++ tailWord_5211354).sum := by decide
  have hdescent : baseEnd_5211354 < baseStart_5211354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211364 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 2, 2, 4]
def baseStart_5211364 : Nat := 118140960795 + 5211364 * 2 ^ 59
def prefixEnd_5211364 : Nat := 4983230072969 + 3 ^ 40 * 5211364 * 2
def baseEnd_5211364 : Nat := 2675934597537453748083379

theorem tailTrace_5211364 : CollatzResearch.WordTrace tailWord_5211364 prefixEnd_5211364 2675934597537453748083379 := by
  unfold tailWord_5211364
  simp only [CollatzResearch.WordTrace]
  refine ⟨95037030146062866478696573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126716040194750488638262097 95037030146062866478696573)
  ·
    refine ⟨35638886304773574929511215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95037030146062866478696573 35638886304773574929511215)
    ·
      refine ⟨53458329457160362394266823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35638886304773574929511215 53458329457160362394266823)
      ·
        refine ⟨80187494185740543591400235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53458329457160362394266823 80187494185740543591400235)
        ·
          refine ⟨120281241278610815387100353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80187494185740543591400235 120281241278610815387100353)
          ·
            refine ⟨90210930958958111540325265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120281241278610815387100353 90210930958958111540325265)
            ·
              refine ⟨67658198219218583655243949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90210930958958111540325265 67658198219218583655243949)
              ·
                refine ⟨25371824332206968870716481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67658198219218583655243949 25371824332206968870716481)
                ·
                  refine ⟨19028868249155226653037361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25371824332206968870716481 19028868249155226653037361)
                  ·
                    refine ⟨14271651186866419989778021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19028868249155226653037361 14271651186866419989778021)
                    ·
                      refine ⟨2675934597537453748083379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14271651186866419989778021 2675934597537453748083379)
                      ·
                        rfl

theorem cell23_5211364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_5211364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211364 prefixEnd_5211364 := by exact prefixLift 5211364
  have htrace : WordTrace (prefixWord ++ tailWord_5211364) baseStart_5211364 baseEnd_5211364 := by
    simpa [prefixWord, tailWord_5211364, baseEnd_5211364] using wordTrace_append hprefix tailTrace_5211364
  have hstable : (prefixWord ++ tailWord_5211364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211364).length < 2 ^ (prefixWord ++ tailWord_5211364).sum := by decide
  have hdescent : baseEnd_5211364 < baseStart_5211364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211374 : List Nat := [4, 1, 2, 1, 1, 1, 2, 4, 7]
def baseStart_5211374 : Nat := 118140960795 + 5211374 * 2 ^ 59
def prefixEnd_5211374 : Nat := 4983230072969 + 3 ^ 40 * 5211374 * 2
def baseEnd_5211374 : Nat := 297326636927110967662037

theorem tailTrace_5211374 : CollatzResearch.WordTrace tailWord_5211374 prefixEnd_5211374 297326636927110967662037 := by
  unfold tailWord_5211374
  simp only [CollatzResearch.WordTrace]
  refine ⟨23759303127761188083157147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126716283348059669776838117 23759303127761188083157147)
  ·
    refine ⟨35638954691641782124735721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23759303127761188083157147 35638954691641782124735721)
    ·
      refine ⟨26729216018731336593551791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35638954691641782124735721 26729216018731336593551791)
      ·
        refine ⟨40093824028097004890327687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26729216018731336593551791 40093824028097004890327687)
        ·
          refine ⟨60140736042145507335491531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40093824028097004890327687 60140736042145507335491531)
          ·
            refine ⟨90211104063218261003237297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60140736042145507335491531 90211104063218261003237297)
            ·
              refine ⟨67658328047413695752427973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90211104063218261003237297 67658328047413695752427973)
              ·
                refine ⟨12685936508890067953580245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67658328047413695752427973 12685936508890067953580245)
                ·
                  refine ⟨297326636927110967662037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12685936508890067953580245 297326636927110967662037)
                  ·
                    rfl

theorem cell23_5211374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_5211374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211374 prefixEnd_5211374 := by exact prefixLift 5211374
  have htrace : WordTrace (prefixWord ++ tailWord_5211374) baseStart_5211374 baseEnd_5211374 := by
    simpa [prefixWord, tailWord_5211374, baseEnd_5211374] using wordTrace_append hprefix tailTrace_5211374
  have hstable : (prefixWord ++ tailWord_5211374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211374).length < 2 ^ (prefixWord ++ tailWord_5211374).sum := by decide
  have hdescent : baseEnd_5211374 < baseStart_5211374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211384 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 6, 3, 3]
def baseStart_5211384 : Nat := 118140960795 + 5211384 * 2 ^ 59
def prefixEnd_5211384 : Nat := 4983230072969 + 3 ^ 40 * 5211384 * 2
def baseEnd_5211384 : Nat := 2675944867150543669833287

theorem tailTrace_5211384 : CollatzResearch.WordTrace tailWord_5211384 prefixEnd_5211384 2675944867150543669833287 := by
  unfold tailWord_5211384
  simp only [CollatzResearch.WordTrace]
  refine ⟨95037394876026638186560603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126716526501368850915414137 95037394876026638186560603)
  ·
    refine ⟨142556092314039957279840905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95037394876026638186560603 142556092314039957279840905)
    ·
      refine ⟨106917069235529967959880679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142556092314039957279840905 106917069235529967959880679)
      ·
        refine ⟨160375603853294951939821019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106917069235529967959880679 160375603853294951939821019)
        ·
          refine ⟨240563405779942427909731529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160375603853294951939821019 240563405779942427909731529)
          ·
            refine ⟨180422554334956820932298647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240563405779942427909731529 180422554334956820932298647)
            ·
              refine ⟨270633831502435231398447971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180422554334956820932298647 270633831502435231398447971)
              ·
                refine ⟨405950747253652847097671957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270633831502435231398447971 405950747253652847097671957)
                ·
                  refine ⟨19028941277514977207703373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 405950747253652847097671957 19028941277514977207703373)
                  ·
                    refine ⟨7135852979068116452888765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19028941277514977207703373 7135852979068116452888765)
                    ·
                      refine ⟨2675944867150543669833287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7135852979068116452888765 2675944867150543669833287)
                      ·
                        rfl

theorem cell23_5211384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 6, 3, 3].length) (baseStart_5211384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211384 prefixEnd_5211384 := by exact prefixLift 5211384
  have htrace : WordTrace (prefixWord ++ tailWord_5211384) baseStart_5211384 baseEnd_5211384 := by
    simpa [prefixWord, tailWord_5211384, baseEnd_5211384] using wordTrace_append hprefix tailTrace_5211384
  have hstable : (prefixWord ++ tailWord_5211384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211384).length < 2 ^ (prefixWord ++ tailWord_5211384).sum := by decide
  have hdescent : baseEnd_5211384 < baseStart_5211384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211441 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 1, 3, 4]
def baseStart_5211441 : Nat := 118140960795 + 5211441 * 2 ^ 59
def prefixEnd_5211441 : Nat := 4983230072969 + 3 ^ 40 * 5211441 * 2
def baseEnd_5211441 : Nat := 2675974135547849946820525

theorem tailTrace_5211441 : CollatzResearch.WordTrace tailWord_5211441 prefixEnd_5211441 2675974135547849946820525 := by
  unfold tailWord_5211441
  simp only [CollatzResearch.WordTrace]
  refine ⟨190076868712846775107946177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126717912475231183405297451 190076868712846775107946177)
  ·
    refine ⟨142557651534635081330959633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190076868712846775107946177 142557651534635081330959633)
    ·
      refine ⟨106918238650976310998219725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142557651534635081330959633 106918238650976310998219725)
      ·
        refine ⟨40094339494116116624332397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106918238650976310998219725 40094339494116116624332397)
        ·
          refine ⟨15035377310293543734124649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40094339494116116624332397 15035377310293543734124649)
          ·
            refine ⟨11276532982720157800593487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15035377310293543734124649 11276532982720157800593487)
            ·
              refine ⟨16914799474080236700890231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11276532982720157800593487 16914799474080236700890231)
              ·
                refine ⟨25372199211120355051335347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16914799474080236700890231 25372199211120355051335347)
                ·
                  refine ⟨38058298816680532577003021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25372199211120355051335347 38058298816680532577003021)
                  ·
                    refine ⟨14271862056255199716376133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38058298816680532577003021 14271862056255199716376133)
                    ·
                      refine ⟨2675974135547849946820525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14271862056255199716376133 2675974135547849946820525)
                      ·
                        rfl

theorem cell23_5211441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_5211441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211441 prefixEnd_5211441 := by exact prefixLift 5211441
  have htrace : WordTrace (prefixWord ++ tailWord_5211441) baseStart_5211441 baseEnd_5211441 := by
    simpa [prefixWord, tailWord_5211441, baseEnd_5211441] using wordTrace_append hprefix tailTrace_5211441
  have hstable : (prefixWord ++ tailWord_5211441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211441).length < 2 ^ (prefixWord ++ tailWord_5211441).sum := by decide
  have hdescent : baseEnd_5211441 < baseStart_5211441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211461 : List Nat := [1, 3, 1, 1, 1, 2, 1, 6, 2, 2, 3]
def baseStart_5211461 : Nat := 118140960795 + 5211461 * 2 ^ 59
def prefixEnd_5211461 : Nat := 4983230072969 + 3 ^ 40 * 5211461 * 2
def baseEnd_5211461 : Nat := 2675984405160939868570433

theorem tailTrace_5211461 : CollatzResearch.WordTrace tailWord_5211461 prefixEnd_5211461 2675984405160939868570433 := by
  unfold tailWord_5211461
  simp only [CollatzResearch.WordTrace]
  refine ⟨190077598172774318523674237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126718398781849545682449491 190077598172774318523674237)
  ·
    refine ⟨71279099314790369446377839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190077598172774318523674237 71279099314790369446377839)
    ·
      refine ⟨106918648972185554169566759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71279099314790369446377839 106918648972185554169566759)
      ·
        refine ⟨160377973458278331254350139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106918648972185554169566759 160377973458278331254350139)
        ·
          refine ⟨240566960187417496881525209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160377973458278331254350139 240566960187417496881525209)
          ·
            refine ⟨180425220140563122661143907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240566960187417496881525209 180425220140563122661143907)
            ·
              refine ⟨270637830210844683991715861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180425220140563122661143907 270637830210844683991715861)
              ·
                refine ⟨12686148291133344562111681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 270637830210844683991715861 12686148291133344562111681)
                ·
                  refine ⟨9514611218350008421583761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12686148291133344562111681 9514611218350008421583761)
                  ·
                    refine ⟨7135958413762506316187821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9514611218350008421583761 7135958413762506316187821)
                    ·
                      refine ⟨2675984405160939868570433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7135958413762506316187821 2675984405160939868570433)
                      ·
                        rfl

theorem cell23_5211461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 2, 3].length) (baseStart_5211461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211461 prefixEnd_5211461 := by exact prefixLift 5211461
  have htrace : WordTrace (prefixWord ++ tailWord_5211461) baseStart_5211461 baseEnd_5211461 := by
    simpa [prefixWord, tailWord_5211461, baseEnd_5211461] using wordTrace_append hprefix tailTrace_5211461
  have hstable : (prefixWord ++ tailWord_5211461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211461).length < 2 ^ (prefixWord ++ tailWord_5211461).sum := by decide
  have hdescent : baseEnd_5211461 < baseStart_5211461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211468 : List Nat := [2, 2, 1, 3, 2, 3, 2, 1, 3, 4]
def baseStart_5211468 : Nat := 118140960795 + 5211468 * 2 ^ 59
def prefixEnd_5211468 : Nat := 4983230072969 + 3 ^ 40 * 5211468 * 2
def baseEnd_5211468 : Nat := 891995999841840447060967

theorem tailTrace_5211468 : CollatzResearch.WordTrace tailWord_5211468 prefixEnd_5211468 891995999841840447060967 := by
  unfold tailWord_5211468
  simp only [CollatzResearch.WordTrace]
  refine ⟨95038926741874479359589529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126718568989165972479452705 95038926741874479359589529)
  ·
    refine ⟨71279195056405859519692147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95038926741874479359589529 71279195056405859519692147)
    ·
      refine ⟨106918792584608789279538221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71279195056405859519692147 106918792584608789279538221)
      ·
        refine ⟨40094547219228295979826833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106918792584608789279538221 40094547219228295979826833)
        ·
          refine ⟨30070910414421221984870125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40094547219228295979826833 30070910414421221984870125)
          ·
            refine ⟨11276591405407958244326297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30070910414421221984870125 11276591405407958244326297)
            ·
              refine ⟨8457443554055968683244723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11276591405407958244326297 8457443554055968683244723)
              ·
                refine ⟨12686165331083953024867085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8457443554055968683244723 12686165331083953024867085)
                ·
                  refine ⟨4757311999156482384325157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12686165331083953024867085 4757311999156482384325157)
                  ·
                    refine ⟨891995999841840447060967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4757311999156482384325157 891995999841840447060967)
                    ·
                      rfl

theorem cell23_5211468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 3, 4].length) (baseStart_5211468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211468 prefixEnd_5211468 := by exact prefixLift 5211468
  have htrace : WordTrace (prefixWord ++ tailWord_5211468) baseStart_5211468 baseEnd_5211468 := by
    simpa [prefixWord, tailWord_5211468, baseEnd_5211468] using wordTrace_append hprefix tailTrace_5211468
  have hstable : (prefixWord ++ tailWord_5211468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211468).length < 2 ^ (prefixWord ++ tailWord_5211468).sum := by decide
  have hdescent : baseEnd_5211468 < baseStart_5211468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211511 : List Nat := [1, 1, 3, 1, 1, 2, 3, 5, 1, 5]
def baseStart_5211511 : Nat := 118140960795 + 5211511 * 2 ^ 59
def prefixEnd_5211511 : Nat := 4983230072969 + 3 ^ 40 * 5211511 * 2
def baseEnd_5211511 : Nat := 892003359731221557648401

theorem tailTrace_5211511 : CollatzResearch.WordTrace tailWord_5211511 prefixEnd_5211511 892003359731221557648401 := by
  unfold tailWord_5211511
  simp only [CollatzResearch.WordTrace]
  refine ⟨190079421822593177062994387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126719614548395451375329591 190079421822593177062994387)
  ·
    refine ⟨285119132733889765594491581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190079421822593177062994387 285119132733889765594491581)
    ·
      refine ⟨106919674775208662097934343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285119132733889765594491581 106919674775208662097934343)
      ·
        refine ⟨160379512162812993146901515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106919674775208662097934343 160379512162812993146901515)
        ·
          refine ⟨240569268244219489720352273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160379512162812993146901515 240569268244219489720352273)
          ·
            refine ⟨180426951183164617290264205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240569268244219489720352273 180426951183164617290264205)
            ·
              refine ⟨67660106693686731483849077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180426951183164617290264205 67660106693686731483849077)
              ·
                refine ⟨6343135002533131076610851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67660106693686731483849077 6343135002533131076610851)
                ·
                  refine ⟨9514702503799696614916277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6343135002533131076610851 9514702503799696614916277)
                  ·
                    refine ⟨892003359731221557648401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9514702503799696614916277 892003359731221557648401)
                    ·
                      rfl

theorem cell23_5211511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 5].length) (baseStart_5211511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211511 prefixEnd_5211511 := by exact prefixLift 5211511
  have htrace : WordTrace (prefixWord ++ tailWord_5211511) baseStart_5211511 baseEnd_5211511 := by
    simpa [prefixWord, tailWord_5211511, baseEnd_5211511] using wordTrace_append hprefix tailTrace_5211511
  have hstable : (prefixWord ++ tailWord_5211511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211511).length < 2 ^ (prefixWord ++ tailWord_5211511).sum := by decide
  have hdescent : baseEnd_5211511 < baseStart_5211511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211525 : List Nat := [1, 3, 1, 1, 3, 1, 2, 6, 1, 1, 3]
def baseStart_5211525 : Nat := 118140960795 + 5211525 * 2 ^ 59
def prefixEnd_5211525 : Nat := 4983230072969 + 3 ^ 40 * 5211525 * 2
def baseEnd_5211525 : Nat := 2676017267922827618170139

theorem tailTrace_5211525 : CollatzResearch.WordTrace tailWord_5211525 prefixEnd_5211525 2676017267922827618170139 := by
  unfold tailWord_5211525
  simp only [CollatzResearch.WordTrace]
  refine ⟨190079932444542457454004029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126719954963028304969336019 190079932444542457454004029)
  ·
    refine ⟨71279974666703421545251511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190079932444542457454004029 71279974666703421545251511)
    ·
      refine ⟨106919962000055132317877267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71279974666703421545251511 106919962000055132317877267)
      ·
        refine ⟨160379943000082698476815901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106919962000055132317877267 160379943000082698476815901)
        ·
          refine ⟨60142478625031011928805963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160379943000082698476815901 60142478625031011928805963)
          ·
            refine ⟨90213717937546517893208945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60142478625031011928805963 90213717937546517893208945)
            ·
              refine ⟨67660288453159888419906709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90213717937546517893208945 67660288453159888419906709)
              ·
                refine ⟨3171576021241869769683127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67660288453159888419906709 3171576021241869769683127)
                ·
                  refine ⟨4757364031862804654524691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3171576021241869769683127 4757364031862804654524691)
                  ·
                    refine ⟨7136046047794206981787037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4757364031862804654524691 7136046047794206981787037)
                    ·
                      refine ⟨2676017267922827618170139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7136046047794206981787037 2676017267922827618170139)
                      ·
                        rfl

theorem cell23_5211525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 1, 1, 3].length) (baseStart_5211525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211525 prefixEnd_5211525 := by exact prefixLift 5211525
  have htrace : WordTrace (prefixWord ++ tailWord_5211525) baseStart_5211525 baseEnd_5211525 := by
    simpa [prefixWord, tailWord_5211525, baseEnd_5211525] using wordTrace_append hprefix tailTrace_5211525
  have hstable : (prefixWord ++ tailWord_5211525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211525).length < 2 ^ (prefixWord ++ tailWord_5211525).sum := by decide
  have hdescent : baseEnd_5211525 < baseStart_5211525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211531 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 4]
def baseStart_5211531 : Nat := 118140960795 + 5211531 * 2 ^ 59
def prefixEnd_5211531 : Nat := 4983230072969 + 3 ^ 40 * 5211531 * 2
def baseEnd_5211531 : Nat := 2676020348806754594695111

theorem tailTrace_5211531 : CollatzResearch.WordTrace tailWord_5211531 prefixEnd_5211531 2676020348806754594695111 := by
  unfold tailWord_5211531
  simp only [CollatzResearch.WordTrace]
  refine ⟨190080151282520720478722447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126720100855013813652481631 190080151282520720478722447)
  ·
    refine ⟨285120226923781080718083671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190080151282520720478722447 285120226923781080718083671)
    ·
      refine ⟨427680340385671621077125507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285120226923781080718083671 427680340385671621077125507)
      ·
        refine ⟨641520510578507431615688261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427680340385671621077125507 641520510578507431615688261)
        ·
          refine ⟨120285095733470143427941549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 641520510578507431615688261 120285095733470143427941549)
          ·
            refine ⟨45106910900051303785478081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120285095733470143427941549 45106910900051303785478081)
            ·
              refine ⟨33830183175038477839108561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45106910900051303785478081 33830183175038477839108561)
              ·
                refine ⟨25372637381278858379331421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33830183175038477839108561 25372637381278858379331421)
                ·
                  refine ⟨9514739017979571892249283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25372637381278858379331421 9514739017979571892249283)
                  ·
                    refine ⟨14272108526969357838373925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9514739017979571892249283 14272108526969357838373925)
                    ·
                      refine ⟨2676020348806754594695111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14272108526969357838373925 2676020348806754594695111)
                      ·
                        rfl

theorem cell23_5211531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 4].length) (baseStart_5211531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211531 prefixEnd_5211531 := by exact prefixLift 5211531
  have htrace : WordTrace (prefixWord ++ tailWord_5211531) baseStart_5211531 baseEnd_5211531 := by
    simpa [prefixWord, tailWord_5211531, baseEnd_5211531] using wordTrace_append hprefix tailTrace_5211531
  have hstable : (prefixWord ++ tailWord_5211531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211531).length < 2 ^ (prefixWord ++ tailWord_5211531).sum := by decide
  have hdescent : baseEnd_5211531 < baseStart_5211531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211588 : List Nat := [2, 3, 3, 2, 1, 1, 3, 8]
def baseStart_5211588 : Nat := 118140960795 + 5211588 * 2 ^ 59
def prefixEnd_5211588 : Nat := 4983230072969 + 3 ^ 40 * 5211588 * 2
def baseEnd_5211588 : Nat := 99112948785335587840087

theorem tailTrace_5211588 : CollatzResearch.WordTrace tailWord_5211588 prefixEnd_5211588 99112948785335587840087 := by
  unfold tailWord_5211588
  simp only [CollatzResearch.WordTrace]
  refine ⟨95041115121657109606773709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126721486828876146142364945 95041115121657109606773709)
  ·
    refine ⟨35640418170621416102540141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95041115121657109606773709 35640418170621416102540141)
    ·
      refine ⟨13365156813983031038452553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35640418170621416102540141 13365156813983031038452553)
      ·
        refine ⟨10023867610487273278839415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13365156813983031038452553 10023867610487273278839415)
        ·
          refine ⟨15035801415730909918259123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10023867610487273278839415 15035801415730909918259123)
          ·
            refine ⟨22553702123596364877388685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15035801415730909918259123 22553702123596364877388685)
            ·
              refine ⟨8457638296348636829020757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22553702123596364877388685 8457638296348636829020757)
              ·
                refine ⟨99112948785335587840087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8457638296348636829020757 99112948785335587840087)
                ·
                  rfl

theorem cell23_5211588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 8].length) (baseStart_5211588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211588 prefixEnd_5211588 := by exact prefixLift 5211588
  have htrace : WordTrace (prefixWord ++ tailWord_5211588) baseStart_5211588 baseEnd_5211588 := by
    simpa [prefixWord, tailWord_5211588, baseEnd_5211588] using wordTrace_append hprefix tailTrace_5211588
  have hstable : (prefixWord ++ tailWord_5211588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211588).length < 2 ^ (prefixWord ++ tailWord_5211588).sum := by decide
  have hdescent : baseEnd_5211588 < baseStart_5211588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211598 : List Nat := [4, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3]
def baseStart_5211598 : Nat := 118140960795 + 5211598 * 2 ^ 59
def prefixEnd_5211598 : Nat := 4983230072969 + 3 ^ 40 * 5211598 * 2
def baseEnd_5211598 : Nat := 2676054752010605832557303

theorem tailTrace_5211598 : CollatzResearch.WordTrace tailWord_5211598 prefixEnd_5211598 2676054752010605832557303 := by
  unfold tailWord_5211598
  simp only [CollatzResearch.WordTrace]
  refine ⟨23760324371659748865176431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126721729982185327280940965 23760324371659748865176431)
  ·
    refine ⟨35640486557489623297764647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23760324371659748865176431 35640486557489623297764647)
    ·
      refine ⟨53460729836234434946646971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35640486557489623297764647 53460729836234434946646971)
      ·
        refine ⟨80191094754351652419970457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53460729836234434946646971 80191094754351652419970457)
        ·
          refine ⟨60143321065763739314977843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80191094754351652419970457 60143321065763739314977843)
          ·
            refine ⟨90214981598645608972466765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60143321065763739314977843 90214981598645608972466765)
            ·
              refine ⟨33830618099492103364675037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90214981598645608972466765 33830618099492103364675037)
              ·
                refine ⟨12686481787309538761753139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33830618099492103364675037 12686481787309538761753139)
                ·
                  refine ⟨19029722680964308142629709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12686481787309538761753139 19029722680964308142629709)
                  ·
                    refine ⟨7136146005361615553486141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19029722680964308142629709 7136146005361615553486141)
                    ·
                      refine ⟨2676054752010605832557303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7136146005361615553486141 2676054752010605832557303)
                      ·
                        rfl

theorem cell23_5211598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_5211598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211598 prefixEnd_5211598 := by exact prefixLift 5211598
  have htrace : WordTrace (prefixWord ++ tailWord_5211598) baseStart_5211598 baseEnd_5211598 := by
    simpa [prefixWord, tailWord_5211598, baseEnd_5211598] using wordTrace_append hprefix tailTrace_5211598
  have hstable : (prefixWord ++ tailWord_5211598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211598).length < 2 ^ (prefixWord ++ tailWord_5211598).sum := by decide
  have hdescent : baseEnd_5211598 < baseStart_5211598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211631 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 2, 6]
def baseStart_5211631 : Nat := 118140960795 + 5211631 * 2 ^ 59
def prefixEnd_5211631 : Nat := 4983230072969 + 3 ^ 40 * 5211631 * 2
def baseEnd_5211631 : Nat := 892023898957401401148217

theorem tailTrace_5211631 : CollatzResearch.WordTrace tailWord_5211631 prefixEnd_5211631 892023898957401401148217 := by
  unfold tailWord_5211631
  simp only [CollatzResearch.WordTrace]
  refine ⟨190083798582158437557362747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126722532388105625038241831 190083798582158437557362747)
  ·
    refine ⟨285125697873237656336044121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190083798582158437557362747 285125697873237656336044121)
    ·
      refine ⟨213844273404928242252033091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285125697873237656336044121 213844273404928242252033091)
      ·
        refine ⟨320766410107392363378049637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213844273404928242252033091 320766410107392363378049637)
        ·
          refine ⟨60143701895136068133384307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 320766410107392363378049637 60143701895136068133384307)
          ·
            refine ⟨90215552842704102200076461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60143701895136068133384307 90215552842704102200076461)
            ·
              refine ⟨33830832316014038325028673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90215552842704102200076461 33830832316014038325028673)
              ·
                refine ⟨25373124237010528743771505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33830832316014038325028673 25373124237010528743771505)
                ·
                  refine ⟨19029843177757896557828629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25373124237010528743771505 19029843177757896557828629)
                  ·
                    refine ⟨892023898957401401148217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19029843177757896557828629 892023898957401401148217)
                    ·
                      rfl

theorem cell23_5211631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 6].length) (baseStart_5211631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211631 prefixEnd_5211631 := by exact prefixLift 5211631
  have htrace : WordTrace (prefixWord ++ tailWord_5211631) baseStart_5211631 baseEnd_5211631 := by
    simpa [prefixWord, tailWord_5211631, baseEnd_5211631] using wordTrace_append hprefix tailTrace_5211631
  have hstable : (prefixWord ++ tailWord_5211631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211631).length < 2 ^ (prefixWord ++ tailWord_5211631).sum := by decide
  have hdescent : baseEnd_5211631 < baseStart_5211631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211632 : List Nat := [2, 1, 1, 1, 3, 6, 1, 2, 2, 1, 3]
def baseStart_5211632 : Nat := 118140960795 + 5211632 * 2 ^ 59
def prefixEnd_5211632 : Nat := 4983230072969 + 3 ^ 40 * 5211632 * 2
def baseEnd_5211632 : Nat := 2676072210352858699532147

theorem tailTrace_5211632 : CollatzResearch.WordTrace tailWord_5211632 prefixEnd_5211632 2676072210352858699532147 := by
  unfold tailWord_5211632
  simp only [CollatzResearch.WordTrace]
  refine ⟨95041917527577407364074575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126722556703436543152099433 95041917527577407364074575)
  ·
    refine ⟨142562876291366111046111863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95041917527577407364074575 142562876291366111046111863)
    ·
      refine ⟨213844314437049166569167795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142562876291366111046111863 213844314437049166569167795)
      ·
        refine ⟨320766471655573749853751693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213844314437049166569167795 320766471655573749853751693)
        ·
          refine ⟨120287426870840156195156885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320766471655573749853751693 120287426870840156195156885)
          ·
            refine ⟨5638473134570632321647979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 120287426870840156195156885 5638473134570632321647979)
            ·
              refine ⟨8457709701855948482471969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5638473134570632321647979 8457709701855948482471969)
              ·
                refine ⟨6343282276391961361853977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8457709701855948482471969 6343282276391961361853977)
                ·
                  refine ⟨4757461707293971021390483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6343282276391961361853977 4757461707293971021390483)
                  ·
                    refine ⟨7136192560940956532085725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4757461707293971021390483 7136192560940956532085725)
                    ·
                      refine ⟨2676072210352858699532147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7136192560940956532085725 2676072210352858699532147)
                      ·
                        rfl

theorem cell23_5211632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 2, 1, 3].length) (baseStart_5211632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211632 prefixEnd_5211632 := by exact prefixLift 5211632
  have htrace : WordTrace (prefixWord ++ tailWord_5211632) baseStart_5211632 baseEnd_5211632 := by
    simpa [prefixWord, tailWord_5211632, baseEnd_5211632] using wordTrace_append hprefix tailTrace_5211632
  have hstable : (prefixWord ++ tailWord_5211632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211632).length < 2 ^ (prefixWord ++ tailWord_5211632).sum := by decide
  have hdescent : baseEnd_5211632 < baseStart_5211632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211641 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 4, 1, 5]
def baseStart_5211641 : Nat := 118140960795 + 5211641 * 2 ^ 59
def prefixEnd_5211641 : Nat := 4983230072969 + 3 ^ 40 * 5211641 * 2
def baseEnd_5211641 : Nat := 2676076831678749164319605

theorem tailTrace_5211641 : CollatzResearch.WordTrace tailWord_5211641 prefixEnd_5211641 2676076831678749164319605 := by
  unfold tailWord_5211641
  simp only [CollatzResearch.WordTrace]
  refine ⟨190084163312122209265226777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126722775541414806176817851 190084163312122209265226777)
  ·
    refine ⟨142563122484091656948920083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190084163312122209265226777 142563122484091656948920083)
    ·
      refine ⟨213844683726137485423380125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142563122484091656948920083 213844683726137485423380125)
      ·
        refine ⟨80191756397301557033767547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213844683726137485423380125 80191756397301557033767547)
        ·
          refine ⟨120287634595952335550651321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80191756397301557033767547 120287634595952335550651321)
          ·
            refine ⟨90215725946964251662988491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120287634595952335550651321 90215725946964251662988491)
            ·
              refine ⟨135323588920446377494482737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90215725946964251662988491 135323588920446377494482737)
              ·
                refine ⟨101492691690334783120862053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135323588920446377494482737 101492691690334783120862053)
                ·
                  refine ⟨19029879691937771835161635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101492691690334783120862053 19029879691937771835161635)
                  ·
                    refine ⟨28544819537906657752742453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19029879691937771835161635 28544819537906657752742453)
                    ·
                      refine ⟨2676076831678749164319605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28544819537906657752742453 2676076831678749164319605)
                      ·
                        rfl

theorem cell23_5211641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_5211641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211641 prefixEnd_5211641 := by exact prefixLift 5211641
  have htrace : WordTrace (prefixWord ++ tailWord_5211641) baseStart_5211641 baseEnd_5211641 := by
    simpa [prefixWord, tailWord_5211641, baseEnd_5211641] using wordTrace_append hprefix tailTrace_5211641
  have hstable : (prefixWord ++ tailWord_5211641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211641).length < 2 ^ (prefixWord ++ tailWord_5211641).sum := by decide
  have hdescent : baseEnd_5211641 < baseStart_5211641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211649 : List Nat := [1, 2, 4, 1, 4, 1, 3, 1, 2, 1, 3]
def baseStart_5211649 : Nat := 118140960795 + 5211649 * 2 ^ 59
def prefixEnd_5211649 : Nat := 4983230072969 + 3 ^ 40 * 5211649 * 2
def baseEnd_5211649 : Nat := 2676080939523985133019569

theorem tailTrace_5211649 : CollatzResearch.WordTrace tailWord_5211649 prefixEnd_5211649 2676080939523985133019569 := by
  unfold tailWord_5211649
  simp only [CollatzResearch.WordTrace]
  refine ⟨190084455096093226631518001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126722970064062151087678667 190084455096093226631518001)
  ·
    refine ⟨142563341322069919973638501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190084455096093226631518001 142563341322069919973638501)
    ·
      refine ⟨26730626497888109995057219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142563341322069919973638501 26730626497888109995057219)
      ·
        refine ⟨40095939746832164992585829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26730626497888109995057219 40095939746832164992585829)
        ·
          refine ⟨7517988702531030936109843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40095939746832164992585829 7517988702531030936109843)
          ·
            refine ⟨11276983053796546404164765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7517988702531030936109843 11276983053796546404164765)
            ·
              refine ⟨4228868645173704901561787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11276983053796546404164765 4228868645173704901561787)
              ·
                refine ⟨6343302967760557352342681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4228868645173704901561787 6343302967760557352342681)
                ·
                  refine ⟨4757477225820418014257011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6343302967760557352342681 4757477225820418014257011)
                  ·
                    refine ⟨7136215838730627021385517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4757477225820418014257011 7136215838730627021385517)
                    ·
                      refine ⟨2676080939523985133019569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7136215838730627021385517 2676080939523985133019569)
                      ·
                        rfl

theorem cell23_5211649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_5211649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211649 prefixEnd_5211649 := by exact prefixLift 5211649
  have htrace : WordTrace (prefixWord ++ tailWord_5211649) baseStart_5211649 baseEnd_5211649 := by
    simpa [prefixWord, tailWord_5211649, baseEnd_5211649] using wordTrace_append hprefix tailTrace_5211649
  have hstable : (prefixWord ++ tailWord_5211649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211649).length < 2 ^ (prefixWord ++ tailWord_5211649).sum := by decide
  have hdescent : baseEnd_5211649 < baseStart_5211649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211651 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 4]
def baseStart_5211651 : Nat := 118140960795 + 5211651 * 2 ^ 59
def prefixEnd_5211651 : Nat := 4983230072969 + 3 ^ 40 * 5211651 * 2
def baseEnd_5211651 : Nat := 2676081966485294125194559

theorem tailTrace_5211651 : CollatzResearch.WordTrace tailWord_5211651 prefixEnd_5211651 2676081966485294125194559 := by
  unfold tailWord_5211651
  simp only [CollatzResearch.WordTrace]
  refine ⟨190084528042085980973090807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126723018694723987315393871 190084528042085980973090807)
  ·
    refine ⟨285126792063128971459636211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190084528042085980973090807 285126792063128971459636211)
    ·
      refine ⟨427690188094693457189454317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285126792063128971459636211 427690188094693457189454317)
      ·
        refine ⟨160383820535510046446045369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 427690188094693457189454317 160383820535510046446045369)
        ·
          refine ⟨120287865401632534834534027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160383820535510046446045369 120287865401632534834534027)
          ·
            refine ⟨180431798102448802251801041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120287865401632534834534027 180431798102448802251801041)
            ·
              refine ⟨135323848576836601688850781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180431798102448802251801041 135323848576836601688850781)
              ·
                refine ⟨50746443216313725633319043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135323848576836601688850781 50746443216313725633319043)
                ·
                  refine ⟨76119664824470588449978565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50746443216313725633319043 76119664824470588449978565)
                  ·
                    refine ⟨14272437154588235334370981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 76119664824470588449978565 14272437154588235334370981)
                    ·
                      refine ⟨2676081966485294125194559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14272437154588235334370981 2676081966485294125194559)
                      ·
                        rfl

theorem cell23_5211651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_5211651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211651 prefixEnd_5211651 := by exact prefixLift 5211651
  have htrace : WordTrace (prefixWord ++ tailWord_5211651) baseStart_5211651 baseEnd_5211651 := by
    simpa [prefixWord, tailWord_5211651, baseEnd_5211651] using wordTrace_append hprefix tailTrace_5211651
  have hstable : (prefixWord ++ tailWord_5211651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211651).length < 2 ^ (prefixWord ++ tailWord_5211651).sum := by decide
  have hdescent : baseEnd_5211651 < baseStart_5211651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211721 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 2, 8]
def baseStart_5211721 : Nat := 118140960795 + 5211721 * 2 ^ 59
def prefixEnd_5211721 : Nat := 4983230072969 + 3 ^ 40 * 5211721 * 2
def baseEnd_5211721 : Nat := 892039303377036283773079

theorem tailTrace_5211721 : CollatzResearch.WordTrace tailWord_5211721 prefixEnd_5211721 892039303377036283773079 := by
  unfold tailWord_5211721
  simp only [CollatzResearch.WordTrace]
  refine ⟨190087081151832382928139017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126724720767888255285426011 190087081151832382928139017)
  ·
    refine ⟨142565310863874287196104263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190087081151832382928139017 142565310863874287196104263)
    ·
      refine ⟨213847966295811430794156395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142565310863874287196104263 213847966295811430794156395)
      ·
        refine ⟨320771949443717146191234593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213847966295811430794156395 320771949443717146191234593)
        ·
          refine ⟨240578962082787859643425945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320771949443717146191234593 240578962082787859643425945)
          ·
            refine ⟨180434221562090894732569459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240578962082787859643425945 180434221562090894732569459)
            ·
              refine ⟨270651332343136342098854189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180434221562090894732569459 270651332343136342098854189)
              ·
                refine ⟨101494249628676128287070321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 270651332343136342098854189 101494249628676128287070321)
                ·
                  refine ⟨76120687221507096215302741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101494249628676128287070321 76120687221507096215302741)
                  ·
                    refine ⟨892039303377036283773079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76120687221507096215302741 892039303377036283773079)
                    ·
                      rfl

theorem cell23_5211721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 8].length) (baseStart_5211721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211721 prefixEnd_5211721 := by exact prefixLift 5211721
  have htrace : WordTrace (prefixWord ++ tailWord_5211721) baseStart_5211721 baseEnd_5211721 := by
    simpa [prefixWord, tailWord_5211721, baseEnd_5211721] using wordTrace_append hprefix tailTrace_5211721
  have hstable : (prefixWord ++ tailWord_5211721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211721).length < 2 ^ (prefixWord ++ tailWord_5211721).sum := by decide
  have hdescent : baseEnd_5211721 < baseStart_5211721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211745 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 2, 4, 2]
def baseStart_5211745 : Nat := 118140960795 + 5211745 * 2 ^ 59
def prefixEnd_5211745 : Nat := 4983230072969 + 3 ^ 40 * 5211745 * 2
def baseEnd_5211745 : Nat := 2676130233666816757419127

theorem tailTrace_5211745 : CollatzResearch.WordTrace tailWord_5211745 prefixEnd_5211745 2676130233666816757419127 := by
  unfold tailWord_5211745
  simp only [CollatzResearch.WordTrace]
  refine ⟨190087956503745435027012689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126725304335830290018008459 190087956503745435027012689)
  ·
    refine ⟨142565967377809076270259517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190087956503745435027012689 142565967377809076270259517)
    ·
      refine ⟨53462237766678403601347319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142565967377809076270259517 53462237766678403601347319)
      ·
        refine ⟨80193356650017605402020979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53462237766678403601347319 80193356650017605402020979)
        ·
          refine ⟨120290034975026408103031469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80193356650017605402020979 120290034975026408103031469)
          ·
            refine ⟨45108763115634903038636801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120290034975026408103031469 45108763115634903038636801)
            ·
              refine ⟨33831572336726177278977601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45108763115634903038636801 33831572336726177278977601)
              ·
                refine ⟨25373679252544632959233201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33831572336726177278977601 25373679252544632959233201)
                ·
                  refine ⟨19030259439408474719424901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25373679252544632959233201 19030259439408474719424901)
                  ·
                    refine ⟨3568173644889089009892169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19030259439408474719424901 3568173644889089009892169)
                    ·
                      refine ⟨2676130233666816757419127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3568173644889089009892169 2676130233666816757419127)
                      ·
                        rfl

theorem cell23_5211745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 4, 2].length) (baseStart_5211745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211745 prefixEnd_5211745 := by exact prefixLift 5211745
  have htrace : WordTrace (prefixWord ++ tailWord_5211745) baseStart_5211745 baseEnd_5211745 := by
    simpa [prefixWord, tailWord_5211745, baseEnd_5211745] using wordTrace_append hprefix tailTrace_5211745
  have hstable : (prefixWord ++ tailWord_5211745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211745).length < 2 ^ (prefixWord ++ tailWord_5211745).sum := by decide
  have hdescent : baseEnd_5211745 < baseStart_5211745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211762 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 2, 4, 2]
def baseStart_5211762 : Nat := 118140960795 + 5211762 * 2 ^ 59
def prefixEnd_5211762 : Nat := 4983230072969 + 3 ^ 40 * 5211762 * 2
def baseEnd_5211762 : Nat := 2676138962837943190906549

theorem tailTrace_5211762 : CollatzResearch.WordTrace tailWord_5211762 prefixEnd_5211762 2676138962837943190906549 := by
  unfold tailWord_5211762
  simp only [CollatzResearch.WordTrace]
  refine ⟨47522144136170961732595385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126725717696455897953587693 47522144136170961732595385)
  ·
    refine ⟨35641608102128221299446539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47522144136170961732595385 35641608102128221299446539)
    ·
      refine ⟨53462412153192331949169809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35641608102128221299446539 53462412153192331949169809)
      ·
        refine ⟨40096809114894248961877357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53462412153192331949169809 40096809114894248961877357)
        ·
          refine ⟨15036303418085343360704009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40096809114894248961877357 15036303418085343360704009)
          ·
            refine ⟨11277227563564007520528007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15036303418085343360704009 11277227563564007520528007)
            ·
              refine ⟨16915841345346011280792011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11277227563564007520528007 16915841345346011280792011)
              ·
                refine ⟨25373762018019016921188017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16915841345346011280792011 25373762018019016921188017)
                ·
                  refine ⟨19030321513514262690891013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25373762018019016921188017 19030321513514262690891013)
                  ·
                    refine ⟨3568185283783924254542065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19030321513514262690891013 3568185283783924254542065)
                    ·
                      refine ⟨2676138962837943190906549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3568185283783924254542065 2676138962837943190906549)
                      ·
                        rfl

theorem cell23_5211762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_5211762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211762 prefixEnd_5211762 := by exact prefixLift 5211762
  have htrace : WordTrace (prefixWord ++ tailWord_5211762) baseStart_5211762 baseEnd_5211762 := by
    simpa [prefixWord, tailWord_5211762, baseEnd_5211762] using wordTrace_append hprefix tailTrace_5211762
  have hstable : (prefixWord ++ tailWord_5211762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211762).length < 2 ^ (prefixWord ++ tailWord_5211762).sum := by decide
  have hdescent : baseEnd_5211762 < baseStart_5211762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211812 : List Nat := [2, 3, 1, 2, 2, 2, 1, 3, 3, 1, 3]
def baseStart_5211812 : Nat := 118140960795 + 5211812 * 2 ^ 59
def prefixEnd_5211812 : Nat := 4983230072969 + 3 ^ 40 * 5211812 * 2
def baseEnd_5211812 : Nat := 2676164636870667995281319

theorem tailTrace_5211812 : CollatzResearch.WordTrace tailWord_5211812 prefixEnd_5211812 2676164636870667995281319 := by
  unfold tailWord_5211812
  simp only [CollatzResearch.WordTrace]
  refine ⟨95045200097251352734850845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126726933463001803646467793 95045200097251352734850845)
  ·
    refine ⟨35641950036469257275569067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95045200097251352734850845 35641950036469257275569067)
    ·
      refine ⟨53462925054703885913353601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35641950036469257275569067 53462925054703885913353601)
      ·
        refine ⟨40097193791027914435015201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53462925054703885913353601 40097193791027914435015201)
        ·
          refine ⟨30072895343270935826261401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40097193791027914435015201 30072895343270935826261401)
          ·
            refine ⟨22554671507453201869696051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30072895343270935826261401 22554671507453201869696051)
            ·
              refine ⟨33832007261179802804544077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22554671507453201869696051 33832007261179802804544077)
              ·
                refine ⟨12687002722942426051704029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33832007261179802804544077 12687002722942426051704029)
                ·
                  refine ⟨4757626021103409769389011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12687002722942426051704029 4757626021103409769389011)
                  ·
                    refine ⟨7136439031655114654083517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4757626021103409769389011 7136439031655114654083517)
                    ·
                      refine ⟨2676164636870667995281319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7136439031655114654083517 2676164636870667995281319)
                      ·
                        rfl

theorem cell23_5211812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_5211812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211812 prefixEnd_5211812 := by exact prefixLift 5211812
  have htrace : WordTrace (prefixWord ++ tailWord_5211812) baseStart_5211812 baseEnd_5211812 := by
    simpa [prefixWord, tailWord_5211812, baseEnd_5211812] using wordTrace_append hprefix tailTrace_5211812
  have hstable : (prefixWord ++ tailWord_5211812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211812).length < 2 ^ (prefixWord ++ tailWord_5211812).sum := by decide
  have hdescent : baseEnd_5211812 < baseStart_5211812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211888 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 4, 7]
def baseStart_5211888 : Nat := 118140960795 + 5211888 * 2 ^ 59
def prefixEnd_5211888 : Nat := 4983230072969 + 3 ^ 40 * 5211888 * 2
def baseEnd_5211888 : Nat := 892067887133469899310323

theorem tailTrace_5211888 : CollatzResearch.WordTrace tailWord_5211888 prefixEnd_5211888 892067887133469899310323 := by
  unfold tailWord_5211888
  simp only [CollatzResearch.WordTrace]
  refine ⟨95046586071113685224734159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126728781428151580299645545 95046586071113685224734159)
  ·
    refine ⟨142569879106670527837101239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95046586071113685224734159 142569879106670527837101239)
    ·
      refine ⟨213854818660005791755651859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142569879106670527837101239 213854818660005791755651859)
      ·
        refine ⟨320782227990008687633477789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213854818660005791755651859 320782227990008687633477789)
        ·
          refine ⟨120293335496253257862554171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320782227990008687633477789 120293335496253257862554171)
          ·
            refine ⟨180440003244379886793831257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120293335496253257862554171 180440003244379886793831257)
            ·
              refine ⟨135330002433284915095373443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180440003244379886793831257 135330002433284915095373443)
              ·
                refine ⟨202995003649927372643060165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135330002433284915095373443 202995003649927372643060165)
                ·
                  refine ⟨38061563184361382370573781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 202995003649927372643060165 38061563184361382370573781)
                  ·
                    refine ⟨892067887133469899310323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38061563184361382370573781 892067887133469899310323)
                    ·
                      rfl

theorem cell23_5211888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 4, 7].length) (baseStart_5211888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211888 prefixEnd_5211888 := by exact prefixLift 5211888
  have htrace : WordTrace (prefixWord ++ tailWord_5211888) baseStart_5211888 baseEnd_5211888 := by
    simpa [prefixWord, tailWord_5211888, baseEnd_5211888] using wordTrace_append hprefix tailTrace_5211888
  have hstable : (prefixWord ++ tailWord_5211888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211888).length < 2 ^ (prefixWord ++ tailWord_5211888).sum := by decide
  have hdescent : baseEnd_5211888 < baseStart_5211888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211889 : List Nat := [1, 2, 2, 2, 2, 5, 1, 2, 1, 2, 3]
def baseStart_5211889 : Nat := 118140960795 + 5211889 * 2 ^ 59
def prefixEnd_5211889 : Nat := 4983230072969 + 3 ^ 40 * 5211889 * 2
def baseEnd_5211889 : Nat := 2676204174881064194018465

theorem tailTrace_5211889 : CollatzResearch.WordTrace tailWord_5211889 prefixEnd_5211889 2676204174881064194018465 := by
  unfold tailWord_5211889
  simp only [CollatzResearch.WordTrace]
  refine ⟨190093208615223747620254721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126728805743482498413503147 190093208615223747620254721)
  ·
    refine ⟨142569906461417810715191041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190093208615223747620254721 142569906461417810715191041)
    ·
      refine ⟨106927429846063358036393281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142569906461417810715191041 106927429846063358036393281)
      ·
        refine ⟨80195572384547518527294961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106927429846063358036393281 80195572384547518527294961)
        ·
          refine ⟨60146679288410638895471221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80195572384547518527294961 60146679288410638895471221)
          ·
            refine ⟨5638751183288497396450427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60146679288410638895471221 5638751183288497396450427)
            ·
              refine ⟨8458126774932746094675641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5638751183288497396450427 8458126774932746094675641)
              ·
                refine ⟨6343595081199559571006731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8458126774932746094675641 6343595081199559571006731)
                ·
                  refine ⟨9515392621799339356510097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6343595081199559571006731 9515392621799339356510097)
                  ·
                    refine ⟨7136544466349504517382573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9515392621799339356510097 7136544466349504517382573)
                    ·
                      refine ⟨2676204174881064194018465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7136544466349504517382573 2676204174881064194018465)
                      ·
                        rfl

theorem cell23_5211889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_5211889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211889 prefixEnd_5211889 := by exact prefixLift 5211889
  have htrace : WordTrace (prefixWord ++ tailWord_5211889) baseStart_5211889 baseEnd_5211889 := by
    simpa [prefixWord, tailWord_5211889, baseEnd_5211889] using wordTrace_append hprefix tailTrace_5211889
  have hstable : (prefixWord ++ tailWord_5211889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211889).length < 2 ^ (prefixWord ++ tailWord_5211889).sum := by decide
  have hdescent : baseEnd_5211889 < baseStart_5211889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211906 : List Nat := [3, 4, 1, 1, 1, 1, 5, 1, 1, 2, 3]
def baseStart_5211906 : Nat := 118140960795 + 5211906 * 2 ^ 59
def prefixEnd_5211906 : Nat := 4983230072969 + 3 ^ 40 * 5211906 * 2
def baseEnd_5211906 : Nat := 2676212904052190627505887

theorem tailTrace_5211906 : CollatzResearch.WordTrace tailWord_5211906 prefixEnd_5211906 2676212904052190627505887 := by
  unfold tailWord_5211906
  simp only [CollatzResearch.WordTrace]
  refine ⟨47523457164040539880905893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126729219104108106349082381 47523457164040539880905893)
  ·
    refine ⟨8910648218257601227669855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47523457164040539880905893 8910648218257601227669855)
    ·
      refine ⟨13365972327386401841504783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8910648218257601227669855 13365972327386401841504783)
      ·
        refine ⟨20048958491079602762257175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13365972327386401841504783 20048958491079602762257175)
        ·
          refine ⟨30073437736619404143385763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20048958491079602762257175 30073437736619404143385763)
          ·
            refine ⟨45110156604929106215078645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30073437736619404143385763 45110156604929106215078645)
            ·
              refine ⟨4229077181712103707663623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45110156604929106215078645 4229077181712103707663623)
              ·
                refine ⟨6343615772568155561495435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4229077181712103707663623 6343615772568155561495435)
                ·
                  refine ⟨9515423658852233342243153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6343615772568155561495435 9515423658852233342243153)
                  ·
                    refine ⟨7136567744139175006682365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9515423658852233342243153 7136567744139175006682365)
                    ·
                      refine ⟨2676212904052190627505887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7136567744139175006682365 2676212904052190627505887)
                      ·
                        rfl

theorem cell23_5211906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_5211906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211906 prefixEnd_5211906 := by exact prefixLift 5211906
  have htrace : WordTrace (prefixWord ++ tailWord_5211906) baseStart_5211906 baseEnd_5211906 := by
    simpa [prefixWord, tailWord_5211906, baseEnd_5211906] using wordTrace_append hprefix tailTrace_5211906
  have hstable : (prefixWord ++ tailWord_5211906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211906).length < 2 ^ (prefixWord ++ tailWord_5211906).sum := by decide
  have hdescent : baseEnd_5211906 < baseStart_5211906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211922 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 2, 7]
def baseStart_5211922 : Nat := 118140960795 + 5211922 * 2 ^ 59
def prefixEnd_5211922 : Nat := 4983230072969 + 3 ^ 40 * 5211922 * 2
def baseEnd_5211922 : Nat := 892073706580887521635271

theorem tailTrace_5211922 : CollatzResearch.WordTrace tailWord_5211922 prefixEnd_5211922 892073706580887521635271 := by
  unfold tailWord_5211922
  simp only [CollatzResearch.WordTrace]
  refine ⟨47523603056026048564051505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126729608149402796170804013 47523603056026048564051505)
  ·
    refine ⟨35642702292019536423038629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47523603056026048564051505 35642702292019536423038629)
    ·
      refine ⟨6683006679753663079319743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35642702292019536423038629 6683006679753663079319743)
      ·
        refine ⟨10024510019630494618979615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6683006679753663079319743 10024510019630494618979615)
        ·
          refine ⟨15036765029445741928469423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10024510019630494618979615 15036765029445741928469423)
          ·
            refine ⟨22555147544168612892704135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15036765029445741928469423 22555147544168612892704135)
            ·
              refine ⟨33832721316252919339056203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22555147544168612892704135 33832721316252919339056203)
              ·
                refine ⟨50749081974379379008584305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33832721316252919339056203 50749081974379379008584305)
                ·
                  refine ⟨38061811480784534256438229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50749081974379379008584305 38061811480784534256438229)
                  ·
                    refine ⟨892073706580887521635271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38061811480784534256438229 892073706580887521635271)
                    ·
                      rfl

theorem cell23_5211922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_5211922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211922 prefixEnd_5211922 := by exact prefixLift 5211922
  have htrace : WordTrace (prefixWord ++ tailWord_5211922) baseStart_5211922 baseEnd_5211922 := by
    simpa [prefixWord, tailWord_5211922, baseEnd_5211922] using wordTrace_append hprefix tailTrace_5211922
  have hstable : (prefixWord ++ tailWord_5211922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211922).length < 2 ^ (prefixWord ++ tailWord_5211922).sum := by decide
  have hdescent : baseEnd_5211922 < baseStart_5211922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211925 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 2, 3, 4]
def baseStart_5211925 : Nat := 118140960795 + 5211925 * 2 ^ 59
def prefixEnd_5211925 : Nat := 4983230072969 + 3 ^ 40 * 5211925 * 2
def baseEnd_5211925 : Nat := 2676222660184626053168299

theorem tailTrace_5211925 : CollatzResearch.WordTrace tailWord_5211925 prefixEnd_5211925 2676222660184626053168299 := by
  unfold tailWord_5211925
  simp only [CollatzResearch.WordTrace]
  refine ⟨190094521643093325768565229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126729681095395550512376819 190094521643093325768565229)
  ·
    refine ⟨71285445616159997163211961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190094521643093325768565229 71285445616159997163211961)
    ·
      refine ⟨53464084212119997872408971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71285445616159997163211961 53464084212119997872408971)
      ·
        refine ⟨80196126318179996808613457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53464084212119997872408971 80196126318179996808613457)
        ·
          refine ⟨60147094738634997606460093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80196126318179996808613457 60147094738634997606460093)
          ·
            refine ⟨22555160526988124102422535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60147094738634997606460093 22555160526988124102422535)
            ·
              refine ⟨33832740790482186153633803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22555160526988124102422535 33832740790482186153633803)
              ·
                refine ⟨50749111185723279230450705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33832740790482186153633803 50749111185723279230450705)
                ·
                  refine ⟨38061833389292459422838029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50749111185723279230450705 38061833389292459422838029)
                  ·
                    refine ⟨14273187520984672283564261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38061833389292459422838029 14273187520984672283564261)
                    ·
                      refine ⟨2676222660184626053168299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14273187520984672283564261 2676222660184626053168299)
                      ·
                        rfl

theorem cell23_5211925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_5211925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211925 prefixEnd_5211925 := by exact prefixLift 5211925
  have htrace : WordTrace (prefixWord ++ tailWord_5211925) baseStart_5211925 baseEnd_5211925 := by
    simpa [prefixWord, tailWord_5211925, baseEnd_5211925] using wordTrace_append hprefix tailTrace_5211925
  have hstable : (prefixWord ++ tailWord_5211925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211925).length < 2 ^ (prefixWord ++ tailWord_5211925).sum := by decide
  have hdescent : baseEnd_5211925 < baseStart_5211925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211935 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 2, 6]
def baseStart_5211935 : Nat := 118140960795 + 5211935 * 2 ^ 59
def prefixEnd_5211935 : Nat := 4983230072969 + 3 ^ 40 * 5211935 * 2
def baseEnd_5211935 : Nat := 892075931663723671347751

theorem tailTrace_5211935 : CollatzResearch.WordTrace tailWord_5211935 prefixEnd_5211935 892075931663723671347751 := by
  unfold tailWord_5211935
  simp only [CollatzResearch.WordTrace]
  refine ⟨190094886373057097476429259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126729924248704731650952839 190094886373057097476429259)
  ·
    refine ⟨285142329559585646214643889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190094886373057097476429259 285142329559585646214643889)
    ·
      refine ⟨213856747169689234660982917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285142329559585646214643889 213856747169689234660982917)
      ·
        refine ⟨40098140094316731498934297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213856747169689234660982917 40098140094316731498934297)
        ·
          refine ⟨30073605070737548624200723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40098140094316731498934297 30073605070737548624200723)
          ·
            refine ⟨45110407606106322936301085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30073605070737548624200723 45110407606106322936301085)
            ·
              refine ⟨16916402852289871101112907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45110407606106322936301085 16916402852289871101112907)
              ·
                refine ⟨25374604278434806651669361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16916402852289871101112907 25374604278434806651669361)
                ·
                  refine ⟨19030953208826104988752021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25374604278434806651669361 19030953208826104988752021)
                  ·
                    refine ⟨892075931663723671347751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19030953208826104988752021 892075931663723671347751)
                    ·
                      rfl

theorem cell23_5211935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 6].length) (baseStart_5211935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211935 prefixEnd_5211935 := by exact prefixLift 5211935
  have htrace : WordTrace (prefixWord ++ tailWord_5211935) baseStart_5211935 baseEnd_5211935 := by
    simpa [prefixWord, tailWord_5211935, baseEnd_5211935] using wordTrace_append hprefix tailTrace_5211935
  have hstable : (prefixWord ++ tailWord_5211935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211935).length < 2 ^ (prefixWord ++ tailWord_5211935).sum := by decide
  have hdescent : baseEnd_5211935 < baseStart_5211935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5211976 : List Nat := [2, 1, 3, 1, 1, 4, 3, 2, 2, 2, 2]
def baseStart_5211976 : Nat := 118140960795 + 5211976 * 2 ^ 59
def prefixEnd_5211976 : Nat := 4983230072969 + 3 ^ 40 * 5211976 * 2
def baseEnd_5211976 : Nat := 2676248847698005353630565

theorem tailTrace_5211976 : CollatzResearch.WordTrace tailWord_5211976 prefixEnd_5211976 2676248847698005353630565 := by
  unfold tailWord_5211976
  simp only [CollatzResearch.WordTrace]
  refine ⟨95048190882954280739335891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126730921177272374319114521 95048190882954280739335891)
  ·
    refine ⟨142572286324431421109003837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95048190882954280739335891 142572286324431421109003837)
    ·
      refine ⟨53464607371661782915876439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142572286324431421109003837 53464607371661782915876439)
      ·
        refine ⟨80196911057492674373814659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53464607371661782915876439 80196911057492674373814659)
        ·
          refine ⟨120295366586239011560721989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80196911057492674373814659 120295366586239011560721989)
          ·
            refine ⟨22555381234919814667635373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120295366586239011560721989 22555381234919814667635373)
            ·
              refine ⟨8458267963094930500363265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22555381234919814667635373 8458267963094930500363265)
              ·
                refine ⟨6343700972321197875272449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8458267963094930500363265 6343700972321197875272449)
                ·
                  refine ⟨4757775729240898406454337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6343700972321197875272449 4757775729240898406454337)
                  ·
                    refine ⟨3568331796930673804840753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4757775729240898406454337 3568331796930673804840753)
                    ·
                      refine ⟨2676248847698005353630565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3568331796930673804840753 2676248847698005353630565)
                      ·
                        rfl

theorem cell23_5211976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 2, 2, 2].length) (baseStart_5211976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5211976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5211976 prefixEnd_5211976 := by exact prefixLift 5211976
  have htrace : WordTrace (prefixWord ++ tailWord_5211976) baseStart_5211976 baseEnd_5211976 := by
    simpa [prefixWord, tailWord_5211976, baseEnd_5211976] using wordTrace_append hprefix tailTrace_5211976
  have hstable : (prefixWord ++ tailWord_5211976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5211976).length < 2 ^ (prefixWord ++ tailWord_5211976).sum := by decide
  have hdescent : baseEnd_5211976 < baseStart_5211976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5211976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212005 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 3, 2, 5]
def baseStart_5212005 : Nat := 118140960795 + 5212005 * 2 ^ 59
def prefixEnd_5212005 : Nat := 4983230072969 + 3 ^ 40 * 5212005 * 2
def baseEnd_5212005 : Nat := 2676263738636985740167931

theorem tailTrace_5212005 : CollatzResearch.WordTrace tailWord_5212005 prefixEnd_5212005 2676263738636985740167931 := by
  unfold tailWord_5212005
  simp only [CollatzResearch.WordTrace]
  refine ⟨190097439482803499431477469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126731626321868999620984979 190097439482803499431477469)
  ·
    refine ⟨71286539806051312286804051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190097439482803499431477469 71286539806051312286804051)
    ·
      refine ⟨106929809709076968430206077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71286539806051312286804051 106929809709076968430206077)
      ·
        refine ⟨40098678640903863161327279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106929809709076968430206077 40098678640903863161327279)
        ·
          refine ⟨60148017961355794741990919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40098678640903863161327279 60148017961355794741990919)
          ·
            refine ⟨90222026942033692112986379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60148017961355794741990919 90222026942033692112986379)
            ·
              refine ⟨135333040413050538169479569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90222026942033692112986379 135333040413050538169479569)
              ·
                refine ⟨101499780309787903627109677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135333040413050538169479569 101499780309787903627109677)
                ·
                  refine ⟨38062417616170463860166129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101499780309787903627109677 38062417616170463860166129)
                  ·
                    refine ⟨28546813212127847895124597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38062417616170463860166129 28546813212127847895124597)
                    ·
                      refine ⟨2676263738636985740167931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28546813212127847895124597 2676263738636985740167931)
                      ·
                        rfl

theorem cell23_5212005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_5212005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212005 prefixEnd_5212005 := by exact prefixLift 5212005
  have htrace : WordTrace (prefixWord ++ tailWord_5212005) baseStart_5212005 baseEnd_5212005 := by
    simpa [prefixWord, tailWord_5212005, baseEnd_5212005] using wordTrace_append hprefix tailTrace_5212005
  have hstable : (prefixWord ++ tailWord_5212005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212005).length < 2 ^ (prefixWord ++ tailWord_5212005).sum := by decide
  have hdescent : baseEnd_5212005 < baseStart_5212005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212032 : List Nat := [2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 4]
def baseStart_5212032 : Nat := 118140960795 + 5212032 * 2 ^ 59
def prefixEnd_5212032 : Nat := 4983230072969 + 3 ^ 40 * 5212032 * 2
def baseEnd_5212032 : Nat := 2676277602614657134530307

theorem tailTrace_5212032 : CollatzResearch.WordTrace tailWord_5212032 prefixEnd_5212032 2676277602614657134530307 := by
  unfold tailWord_5212032
  simp only [CollatzResearch.WordTrace]
  refine ⟨95049212126852841521355175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126732282835803788695140233 95049212126852841521355175)
  ·
    refine ⟨142573818190279262282032763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95049212126852841521355175 142573818190279262282032763)
    ·
      refine ⟨213860727285418893423049145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142573818190279262282032763 213860727285418893423049145)
      ·
        refine ⟨160395545464064170067286859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213860727285418893423049145 160395545464064170067286859)
        ·
          refine ⟨240593318196096255100930289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160395545464064170067286859 240593318196096255100930289)
          ·
            refine ⟨180444988647072191325697717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240593318196096255100930289 180444988647072191325697717)
            ·
              refine ⟨16916717685663017936784161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 180444988647072191325697717 16916717685663017936784161)
              ·
                refine ⟨12687538264247263452588121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16916717685663017936784161 12687538264247263452588121)
                ·
                  refine ⟨9515653698185447589441091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12687538264247263452588121 9515653698185447589441091)
                  ·
                    refine ⟨14273480547278171384161637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9515653698185447589441091 14273480547278171384161637)
                    ·
                      refine ⟨2676277602614657134530307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14273480547278171384161637 2676277602614657134530307)
                      ·
                        rfl

theorem cell23_5212032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_5212032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212032 prefixEnd_5212032 := by exact prefixLift 5212032
  have htrace : WordTrace (prefixWord ++ tailWord_5212032) baseStart_5212032 baseEnd_5212032 := by
    simpa [prefixWord, tailWord_5212032, baseEnd_5212032] using wordTrace_append hprefix tailTrace_5212032
  have hstable : (prefixWord ++ tailWord_5212032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212032).length < 2 ^ (prefixWord ++ tailWord_5212032).sum := by decide
  have hdescent : baseEnd_5212032 < baseStart_5212032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212033 : List Nat := [1, 2, 4, 4, 1, 1, 3, 2, 5]
def baseStart_5212033 : Nat := 118140960795 + 5212033 * 2 ^ 59
def prefixEnd_5212033 : Nat := 4983230072969 + 3 ^ 40 * 5212033 * 2
def baseEnd_5212033 : Nat := 297364235121701292290867

theorem tailTrace_5212033 : CollatzResearch.WordTrace tailWord_5212033 prefixEnd_5212033 297364235121701292290867 := by
  unfold tailWord_5212033
  simp only [CollatzResearch.WordTrace]
  refine ⟨190098460726702060213496753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126732307151134706808997835 190098460726702060213496753)
  ·
    refine ⟨142573845545026545160122565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190098460726702060213496753 142573845545026545160122565)
    ·
      refine ⟨26732596039692477217522981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142573845545026545160122565 26732596039692477217522981)
      ·
        refine ⟨5012361757442339478285559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26732596039692477217522981 5012361757442339478285559)
        ·
          refine ⟨7518542636163509217428339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5012361757442339478285559 7518542636163509217428339)
          ·
            refine ⟨11277813954245263826142509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7518542636163509217428339 11277813954245263826142509)
            ·
              refine ⟨4229180232841973934803441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11277813954245263826142509 4229180232841973934803441)
              ·
                refine ⟨3171885174631480451102581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4229180232841973934803441 3171885174631480451102581)
                ·
                  refine ⟨297364235121701292290867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3171885174631480451102581 297364235121701292290867)
                  ·
                    rfl

theorem cell23_5212033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 5].length) (baseStart_5212033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212033 prefixEnd_5212033 := by exact prefixLift 5212033
  have htrace : WordTrace (prefixWord ++ tailWord_5212033) baseStart_5212033 baseEnd_5212033 := by
    simpa [prefixWord, tailWord_5212033, baseEnd_5212033] using wordTrace_append hprefix tailTrace_5212033
  have hstable : (prefixWord ++ tailWord_5212033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212033).length < 2 ^ (prefixWord ++ tailWord_5212033).sum := by decide
  have hdescent : baseEnd_5212033 < baseStart_5212033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212066 : List Nat := [3, 3, 1, 2, 3, 1, 2, 1, 2, 1, 4]
def baseStart_5212066 : Nat := 118140960795 + 5212066 * 2 ^ 59
def prefixEnd_5212066 : Nat := 4983230072969 + 3 ^ 40 * 5212066 * 2
def baseEnd_5212066 : Nat := 2676295060956910001505151

theorem tailTrace_5212066 : CollatzResearch.WordTrace tailWord_5212066 prefixEnd_5212066 2676295060956910001505151 := by
  unfold tailWord_5212066
  simp only [CollatzResearch.WordTrace]
  refine ⟨47524916083895626712362013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126733109557055004566298701 47524916083895626712362013)
  ·
    refine ⟨17821843531460860017135755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47524916083895626712362013 17821843531460860017135755)
    ·
      refine ⟨26732765297191290025703633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17821843531460860017135755 26732765297191290025703633)
      ·
        refine ⟨20049573972893467519277725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26732765297191290025703633 20049573972893467519277725)
        ·
          refine ⟨7518590239835050319729147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20049573972893467519277725 7518590239835050319729147)
          ·
            refine ⟨11277885359752575479593721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7518590239835050319729147 11277885359752575479593721)
            ·
              refine ⟨8458414019814431609695291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11277885359752575479593721 8458414019814431609695291)
              ·
                refine ⟨12687621029721647414542937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8458414019814431609695291 12687621029721647414542937)
                ·
                  refine ⟨9515715772291235560907203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12687621029721647414542937 9515715772291235560907203)
                  ·
                    refine ⟨14273573658436853341360805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9515715772291235560907203 14273573658436853341360805)
                    ·
                      refine ⟨2676295060956910001505151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14273573658436853341360805 2676295060956910001505151)
                      ·
                        rfl

theorem cell23_5212066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_5212066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212066 prefixEnd_5212066 := by exact prefixLift 5212066
  have htrace : WordTrace (prefixWord ++ tailWord_5212066) baseStart_5212066 baseEnd_5212066 := by
    simpa [prefixWord, tailWord_5212066, baseEnd_5212066] using wordTrace_append hprefix tailTrace_5212066
  have hstable : (prefixWord ++ tailWord_5212066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212066).length < 2 ^ (prefixWord ++ tailWord_5212066).sum := by decide
  have hdescent : baseEnd_5212066 < baseStart_5212066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212093 : List Nat := [1, 4, 1, 2, 3, 1, 4, 2, 1, 4]
def baseStart_5212093 : Nat := 118140960795 + 5212093 * 2 ^ 59
def prefixEnd_5212093 : Nat := 4983230072969 + 3 ^ 40 * 5212093 * 2
def baseEnd_5212093 : Nat := 892102974978193798622509

theorem tailTrace_5212093 : CollatzResearch.WordTrace tailWord_5212093 prefixEnd_5212093 892102974978193798622509 := by
  unfold tailWord_5212093
  simp only [CollatzResearch.WordTrace]
  refine ⟨190100649106484690460680933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126733766070989793640453955 190100649106484690460680933)
  ·
    refine ⟨35643871707465879461377675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190100649106484690460680933 35643871707465879461377675)
    ·
      refine ⟨53465807561198819192066513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35643871707465879461377675 53465807561198819192066513)
      ·
        refine ⟨40099355670899114394049885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53465807561198819192066513 40099355670899114394049885)
        ·
          refine ⟨15037258376587167897768707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40099355670899114394049885 15037258376587167897768707)
          ·
            refine ⟨22555887564880751846653061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15037258376587167897768707 22555887564880751846653061)
            ·
              refine ⟨4229228918415140971247449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22555887564880751846653061 4229228918415140971247449)
              ·
                refine ⟨3171921688811355728435587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4229228918415140971247449 3171921688811355728435587)
                ·
                  refine ⟨4757882533217033592653381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3171921688811355728435587 4757882533217033592653381)
                  ·
                    refine ⟨892102974978193798622509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4757882533217033592653381 892102974978193798622509)
                    ·
                      rfl

theorem cell23_5212093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_5212093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212093 prefixEnd_5212093 := by exact prefixLift 5212093
  have htrace : WordTrace (prefixWord ++ tailWord_5212093) baseStart_5212093 baseEnd_5212093 := by
    simpa [prefixWord, tailWord_5212093, baseEnd_5212093] using wordTrace_append hprefix tailTrace_5212093
  have hstable : (prefixWord ++ tailWord_5212093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212093).length < 2 ^ (prefixWord ++ tailWord_5212093).sum := by decide
  have hdescent : baseEnd_5212093 < baseStart_5212093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212116 : List Nat := [2, 4, 1, 2, 1, 1, 3, 2, 3, 1, 3]
def baseStart_5212116 : Nat := 118140960795 + 5212116 * 2 ^ 59
def prefixEnd_5212116 : Nat := 4983230072969 + 3 ^ 40 * 5212116 * 2
def baseEnd_5212116 : Nat := 2676320734989634805879921

theorem tailTrace_5212116 : CollatzResearch.WordTrace tailWord_5212116 prefixEnd_5212116 2676320734989634805879921 := by
  unfold tailWord_5212116
  simp only [CollatzResearch.WordTrace]
  refine ⟨95050743992700682694384101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126734325323600910259178801 95050743992700682694384101)
  ·
    refine ⟨17822014498631378005197019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95050743992700682694384101 17822014498631378005197019)
    ·
      refine ⟨26733021747947067007795529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17822014498631378005197019 26733021747947067007795529)
      ·
        refine ⟨20049766310960300255846647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26733021747947067007795529 20049766310960300255846647)
        ·
          refine ⟨30074649466440450383769971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20049766310960300255846647 30074649466440450383769971)
          ·
            refine ⟨45111974199660675575654957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30074649466440450383769971 45111974199660675575654957)
            ·
              refine ⟨16916990324872753340870609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45111974199660675575654957 16916990324872753340870609)
              ·
                refine ⟨12687742743654565005652957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16916990324872753340870609 12687742743654565005652957)
                ·
                  refine ⟨4757903528870461877119859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12687742743654565005652957 4757903528870461877119859)
                  ·
                    refine ⟨7136855293305692815679789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4757903528870461877119859 7136855293305692815679789)
                    ·
                      refine ⟨2676320734989634805879921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7136855293305692815679789 2676320734989634805879921)
                      ·
                        rfl

theorem cell23_5212116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_5212116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212116 prefixEnd_5212116 := by exact prefixLift 5212116
  have htrace : WordTrace (prefixWord ++ tailWord_5212116) baseStart_5212116 baseEnd_5212116 := by
    simpa [prefixWord, tailWord_5212116, baseEnd_5212116] using wordTrace_append hprefix tailTrace_5212116
  have hstable : (prefixWord ++ tailWord_5212116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212116).length < 2 ^ (prefixWord ++ tailWord_5212116).sum := by decide
  have hdescent : baseEnd_5212116 < baseStart_5212116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212132 : List Nat := [2, 3, 1, 1, 1, 1, 3, 4, 1, 6]
def baseStart_5212132 : Nat := 118140960795 + 5212132 * 2 ^ 59
def prefixEnd_5212132 : Nat := 4983230072969 + 3 ^ 40 * 5212132 * 2
def baseEnd_5212132 : Nat := 892109650226702247759949

theorem tailTrace_5212132 : CollatzResearch.WordTrace tailWord_5212132 prefixEnd_5212132 892109650226702247759949 := by
  unfold tailWord_5212132
  simp only [CollatzResearch.WordTrace]
  refine ⟨95051035776671700060675325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126734714368895600080900433 95051035776671700060675325)
  ·
    refine ⟨35644138416251887522753247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95051035776671700060675325 35644138416251887522753247)
    ·
      refine ⟨53466207624377831284129871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35644138416251887522753247 53466207624377831284129871)
      ·
        refine ⟨80199311436566746926194807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53466207624377831284129871 80199311436566746926194807)
        ·
          refine ⟨120298967154850120389292211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80199311436566746926194807 120298967154850120389292211)
          ·
            refine ⟨180448450732275180583938317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120298967154850120389292211 180448450732275180583938317)
            ·
              refine ⟨67668169024603192718976869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180448450732275180583938317 67668169024603192718976869)
              ·
                refine ⟨12687781692113098634808163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67668169024603192718976869 12687781692113098634808163)
                ·
                  refine ⟨19031672538169647952212245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12687781692113098634808163 19031672538169647952212245)
                  ·
                    refine ⟨892109650226702247759949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19031672538169647952212245 892109650226702247759949)
                    ·
                      rfl

theorem cell23_5212132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_5212132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212132 prefixEnd_5212132 := by exact prefixLift 5212132
  have htrace : WordTrace (prefixWord ++ tailWord_5212132) baseStart_5212132 baseEnd_5212132 := by
    simpa [prefixWord, tailWord_5212132, baseEnd_5212132] using wordTrace_append hprefix tailTrace_5212132
  have hstable : (prefixWord ++ tailWord_5212132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212132).length < 2 ^ (prefixWord ++ tailWord_5212132).sum := by decide
  have hdescent : baseEnd_5212132 < baseStart_5212132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212152 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 3, 2, 4]
def baseStart_5212152 : Nat := 118140960795 + 5212152 * 2 ^ 59
def prefixEnd_5212152 : Nat := 4983230072969 + 3 ^ 40 * 5212152 * 2
def baseEnd_5212152 : Nat := 2676339220293196665029755

theorem tailTrace_5212152 : CollatzResearch.WordTrace tailWord_5212152 prefixEnd_5212152 2676339220293196665029755 := by
  unfold tailWord_5212152
  simp only [CollatzResearch.WordTrace]
  refine ⟨95051400506635471768539355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126735200675513962358052473 95051400506635471768539355)
  ·
    refine ⟨142577100759953207652809033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95051400506635471768539355 142577100759953207652809033)
    ·
      refine ⟨106932825569964905739606775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142577100759953207652809033 106932825569964905739606775)
      ·
        refine ⟨160399238354947358609410163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106932825569964905739606775 160399238354947358609410163)
        ·
          refine ⟨240598857532421037914115245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160399238354947358609410163 240598857532421037914115245)
          ·
            refine ⟨90224571574657889217793217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240598857532421037914115245 90224571574657889217793217)
            ·
              refine ⟨67668428680993416913344913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90224571574657889217793217 67668428680993416913344913)
              ·
                refine ⟨50751321510745062685008685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67668428680993416913344913 50751321510745062685008685)
                ·
                  refine ⟨19031745566529398506878257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50751321510745062685008685 19031745566529398506878257)
                  ·
                    refine ⟨14273809174897048880158693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19031745566529398506878257 14273809174897048880158693)
                    ·
                      refine ⟨2676339220293196665029755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14273809174897048880158693 2676339220293196665029755)
                      ·
                        rfl

theorem cell23_5212152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_5212152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212152 prefixEnd_5212152 := by exact prefixLift 5212152
  have htrace : WordTrace (prefixWord ++ tailWord_5212152) baseStart_5212152 baseEnd_5212152 := by
    simpa [prefixWord, tailWord_5212152, baseEnd_5212152] using wordTrace_append hprefix tailTrace_5212152
  have hstable : (prefixWord ++ tailWord_5212152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212152).length < 2 ^ (prefixWord ++ tailWord_5212152).sum := by decide
  have hdescent : baseEnd_5212152 < baseStart_5212152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212196 : List Nat := [2, 3, 1, 4, 3, 1, 9]
def baseStart_5212196 : Nat := 118140960795 + 5212196 * 2 ^ 59
def prefixEnd_5212196 : Nat := 4983230072969 + 3 ^ 40 * 5212196 * 2
def baseEnd_5212196 : Nat := 33041503869654252998513

theorem tailTrace_5212196 : CollatzResearch.WordTrace tailWord_5212196 prefixEnd_5212196 33041503869654252998513 := by
  unfold tailWord_5212196
  simp only [CollatzResearch.WordTrace]
  refine ⟨95052202912555769525840221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126736270550074359367786961 95052202912555769525840221)
  ·
    refine ⟨35644576092208413572190083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95052202912555769525840221 35644576092208413572190083)
    ·
      refine ⟨53466864138312620358285125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35644576092208413572190083 53466864138312620358285125)
      ·
        refine ⟨10025037025933616317178461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53466864138312620358285125 10025037025933616317178461)
        ·
          refine ⟨3759388884725106118941923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10025037025933616317178461 3759388884725106118941923)
          ·
            refine ⟨5639083327087659178412885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3759388884725106118941923 5639083327087659178412885)
            ·
              refine ⟨33041503869654252998513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5639083327087659178412885 33041503869654252998513)
              ·
                rfl

theorem cell23_5212196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 9].length) (baseStart_5212196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212196 prefixEnd_5212196 := by exact prefixLift 5212196
  have htrace : WordTrace (prefixWord ++ tailWord_5212196) baseStart_5212196 baseEnd_5212196 := by
    simpa [prefixWord, tailWord_5212196, baseEnd_5212196] using wordTrace_append hprefix tailTrace_5212196
  have hstable : (prefixWord ++ tailWord_5212196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212196).length < 2 ^ (prefixWord ++ tailWord_5212196).sum := by decide
  have hdescent : baseEnd_5212196 < baseStart_5212196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212223 : List Nat := [1, 1, 2, 2, 3, 1, 6, 1, 2, 1, 3]
def baseStart_5212223 : Nat := 118140960795 + 5212223 * 2 ^ 59
def prefixEnd_5212223 : Nat := 4983230072969 + 3 ^ 40 * 5212223 * 2
def baseEnd_5212223 : Nat := 2676375677419665887241929

theorem tailTrace_5212223 : CollatzResearch.WordTrace tailWord_5212223 prefixEnd_5212223 2676375677419665887241929 := by
  unfold tailWord_5212223
  simp only [CollatzResearch.WordTrace]
  refine ⟨190105390596013722662913323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126736927064009148441942215 190105390596013722662913323)
  ·
    refine ⟨285158085894020583994369985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190105390596013722662913323 285158085894020583994369985)
    ·
      refine ⟨213868564420515437995777489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285158085894020583994369985 213868564420515437995777489)
      ·
        refine ⟨160401423315386578496833117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213868564420515437995777489 160401423315386578496833117)
        ·
          refine ⟨60150533743269966936312419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160401423315386578496833117 60150533743269966936312419)
          ·
            refine ⟨90225800614904950404468629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60150533743269966936312419 90225800614904950404468629)
            ·
              refine ⟨4229334403823669550209467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90225800614904950404468629 4229334403823669550209467)
              ·
                refine ⟨6344001605735504325314201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4229334403823669550209467 6344001605735504325314201)
                ·
                  refine ⟨4758001204301628243985651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6344001605735504325314201 4758001204301628243985651)
                  ·
                    refine ⟨7137001806452442365978477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4758001204301628243985651 7137001806452442365978477)
                    ·
                      refine ⟨2676375677419665887241929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7137001806452442365978477 2676375677419665887241929)
                      ·
                        rfl

theorem cell23_5212223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 2, 1, 3].length) (baseStart_5212223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212223 prefixEnd_5212223 := by exact prefixLift 5212223
  have htrace : WordTrace (prefixWord ++ tailWord_5212223) baseStart_5212223 baseEnd_5212223 := by
    simpa [prefixWord, tailWord_5212223, baseEnd_5212223] using wordTrace_append hprefix tailTrace_5212223
  have hstable : (prefixWord ++ tailWord_5212223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212223).length < 2 ^ (prefixWord ++ tailWord_5212223).sum := by decide
  have hdescent : baseEnd_5212223 < baseStart_5212223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212269 : List Nat := [1, 5, 1, 1, 2, 1, 2, 3, 7]
def baseStart_5212269 : Nat := 118140960795 + 5212269 * 2 ^ 59
def prefixEnd_5212269 : Nat := 4983230072969 + 3 ^ 40 * 5212269 * 2
def baseEnd_5212269 : Nat := 297377699725530300807413

theorem tailTrace_5212269 : CollatzResearch.WordTrace tailWord_5212269 prefixEnd_5212269 297377699725530300807413 := by
  unfold tailWord_5212269
  simp only [CollatzResearch.WordTrace]
  refine ⟨190107068353847072519087861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126738045569231381679391907 190107068353847072519087861)
  ·
    refine ⟨17822537658173163048664487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 190107068353847072519087861 17822537658173163048664487)
    ·
      refine ⟨26733806487259744572996731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17822537658173163048664487 26733806487259744572996731)
      ·
        refine ⟨40100709730889616859495097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26733806487259744572996731 40100709730889616859495097)
        ·
          refine ⟨30075532298167212644621323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40100709730889616859495097 30075532298167212644621323)
          ·
            refine ⟨45113298447250818966931985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30075532298167212644621323 45113298447250818966931985)
            ·
              refine ⟨33834973835438114225198989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45113298447250818966931985 33834973835438114225198989)
              ·
                refine ⟨12688115188289292834449621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33834973835438114225198989 12688115188289292834449621)
                ·
                  refine ⟨297377699725530300807413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12688115188289292834449621 297377699725530300807413)
                  ·
                    rfl

theorem cell23_5212269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_5212269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212269 prefixEnd_5212269 := by exact prefixLift 5212269
  have htrace : WordTrace (prefixWord ++ tailWord_5212269) baseStart_5212269 baseEnd_5212269 := by
    simpa [prefixWord, tailWord_5212269, baseEnd_5212269] using wordTrace_append hprefix tailTrace_5212269
  have hstable : (prefixWord ++ tailWord_5212269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212269).length < 2 ^ (prefixWord ++ tailWord_5212269).sum := by decide
  have hdescent : baseEnd_5212269 < baseStart_5212269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212279 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 3]
def baseStart_5212279 : Nat := 118140960795 + 5212279 * 2 ^ 59
def prefixEnd_5212279 : Nat := 4983230072969 + 3 ^ 40 * 5212279 * 2
def baseEnd_5212279 : Nat := 2676404432336317668141671

theorem tailTrace_5212279 : CollatzResearch.WordTrace tailWord_5212279 prefixEnd_5212279 2676404432336317668141671 := by
  unfold tailWord_5212279
  simp only [CollatzResearch.WordTrace]
  refine ⟨190107433083810844226951891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126738288722540562817967927 190107433083810844226951891)
  ·
    refine ⟨285161149625716266340427837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190107433083810844226951891 285161149625716266340427837)
    ·
      refine ⟨106935431109643599877660439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285161149625716266340427837 106935431109643599877660439)
      ·
        refine ⟨160403146664465399816490659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106935431109643599877660439 160403146664465399816490659)
        ·
          refine ⟨240604719996698099724735989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160403146664465399816490659 240604719996698099724735989)
          ·
            refine ⟨22556692499690446849193999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 240604719996698099724735989 22556692499690446849193999)
            ·
              refine ⟨33835038749535670273790999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22556692499690446849193999 33835038749535670273790999)
              ·
                refine ⟨50752558124303505410686499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33835038749535670273790999 50752558124303505410686499)
                ·
                  refine ⟨76128837186455258116029749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50752558124303505410686499 76128837186455258116029749)
                  ·
                    refine ⟨7137078486230180448377789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76128837186455258116029749 7137078486230180448377789)
                    ·
                      refine ⟨2676404432336317668141671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7137078486230180448377789 2676404432336317668141671)
                      ·
                        rfl

theorem cell23_5212279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 3].length) (baseStart_5212279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212279 prefixEnd_5212279 := by exact prefixLift 5212279
  have htrace : WordTrace (prefixWord ++ tailWord_5212279) baseStart_5212279 baseEnd_5212279 := by
    simpa [prefixWord, tailWord_5212279, baseEnd_5212279] using wordTrace_append hprefix tailTrace_5212279
  have hstable : (prefixWord ++ tailWord_5212279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212279).length < 2 ^ (prefixWord ++ tailWord_5212279).sum := by decide
  have hdescent : baseEnd_5212279 < baseStart_5212279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212314 : List Nat := [3, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2]
def baseStart_5212314 : Nat := 118140960795 + 5212314 * 2 ^ 59
def prefixEnd_5212314 : Nat := 4983230072969 + 3 ^ 40 * 5212314 * 2
def baseEnd_5212314 : Nat := 2676422404159225031204011

theorem tailTrace_5212314 : CollatzResearch.WordTrace tailWord_5212314 prefixEnd_5212314 2676422404159225031204011 := by
  unfold tailWord_5212314
  simp only [CollatzResearch.WordTrace]
  refine ⟨47527177409671011301118999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126739139759122696802983997 47527177409671011301118999)
  ·
    refine ⟨71290766114506516951678499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47527177409671011301118999 71290766114506516951678499)
    ·
      refine ⟨106936149171759775427517749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71290766114506516951678499 106936149171759775427517749)
      ·
        refine ⟨10025263984852478946329789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106936149171759775427517749 10025263984852478946329789)
        ·
          refine ⟨3759473994319679604873671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10025263984852478946329789 3759473994319679604873671)
          ·
            refine ⟨5639210991479519407310507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3759473994319679604873671 5639210991479519407310507)
            ·
              refine ⟨8458816487219279110965761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5639210991479519407310507 8458816487219279110965761)
              ·
                refine ⟨6344112365414459333224321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8458816487219279110965761 6344112365414459333224321)
                ·
                  refine ⟨4758084274060844499918241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6344112365414459333224321 4758084274060844499918241)
                  ·
                    refine ⟨3568563205545633374938681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4758084274060844499918241 3568563205545633374938681)
                    ·
                      refine ⟨2676422404159225031204011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3568563205545633374938681 2676422404159225031204011)
                      ·
                        rfl

theorem cell23_5212314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_5212314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212314 prefixEnd_5212314 := by exact prefixLift 5212314
  have htrace : WordTrace (prefixWord ++ tailWord_5212314) baseStart_5212314 baseEnd_5212314 := by
    simpa [prefixWord, tailWord_5212314, baseEnd_5212314] using wordTrace_append hprefix tailTrace_5212314
  have hstable : (prefixWord ++ tailWord_5212314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212314).length < 2 ^ (prefixWord ++ tailWord_5212314).sum := by decide
  have hdescent : baseEnd_5212314 < baseStart_5212314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212346 : List Nat := [3, 1, 1, 1, 2, 2, 4, 2, 3, 4]
def baseStart_5212346 : Nat := 118140960795 + 5212346 * 2 ^ 59
def prefixEnd_5212346 : Nat := 4983230072969 + 3 ^ 40 * 5212346 * 2
def baseEnd_5212346 : Nat := 892146278513389635334621

theorem tailTrace_5212346 : CollatzResearch.WordTrace tailWord_5212346 prefixEnd_5212346 892146278513389635334621 := by
  unfold tailWord_5212346
  simp only [CollatzResearch.WordTrace]
  refine ⟨47527469193642028667410223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126739917849712076446427261 47527469193642028667410223)
  ·
    refine ⟨71291203790463043001115335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47527469193642028667410223 71291203790463043001115335)
    ·
      refine ⟨106936805685694564501673003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71291203790463043001115335 106936805685694564501673003)
      ·
        refine ⟨160405208528541846752509505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106936805685694564501673003 160405208528541846752509505)
        ·
          refine ⟨120303906396406385064382129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160405208528541846752509505 120303906396406385064382129)
          ·
            refine ⟨90227929797304788798286597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120303906396406385064382129 90227929797304788798286597)
            ·
              refine ⟨16917736836994647899678737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90227929797304788798286597 16917736836994647899678737)
              ·
                refine ⟨12688302627745985924759053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16917736836994647899678737 12688302627745985924759053)
                ·
                  refine ⟨4758113485404744721784645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12688302627745985924759053 4758113485404744721784645)
                  ·
                    refine ⟨892146278513389635334621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4758113485404744721784645 892146278513389635334621)
                    ·
                      rfl

theorem cell23_5212346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 3, 4].length) (baseStart_5212346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212346 prefixEnd_5212346 := by exact prefixLift 5212346
  have htrace : WordTrace (prefixWord ++ tailWord_5212346) baseStart_5212346 baseEnd_5212346 := by
    simpa [prefixWord, tailWord_5212346, baseEnd_5212346] using wordTrace_append hprefix tailTrace_5212346
  have hstable : (prefixWord ++ tailWord_5212346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212346).length < 2 ^ (prefixWord ++ tailWord_5212346).sum := by decide
  have hdescent : baseEnd_5212346 < baseStart_5212346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212349 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 1, 6, 4]
def baseStart_5212349 : Nat := 118140960795 + 5212349 * 2 ^ 59
def prefixEnd_5212349 : Nat := 4983230072969 + 3 ^ 40 * 5212349 * 2
def baseEnd_5212349 : Nat := 2676440375982132394266349

theorem tailTrace_5212349 : CollatzResearch.WordTrace tailWord_5212349 prefixEnd_5212349 2676440375982132394266349 := by
  unfold tailWord_5212349
  simp only [CollatzResearch.WordTrace]
  refine ⟨190109986193557246182000101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126739990795704830788000067 190109986193557246182000101)
  ·
    refine ⟨35645622411291983659125019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190109986193557246182000101 35645622411291983659125019)
    ·
      refine ⟨53468433616937975488687529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35645622411291983659125019 53468433616937975488687529)
      ·
        refine ⟨40101325212703481616515647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53468433616937975488687529 40101325212703481616515647)
        ·
          refine ⟨60151987819055222424773471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40101325212703481616515647 60151987819055222424773471)
          ·
            refine ⟨90227981728582833637160207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60151987819055222424773471 90227981728582833637160207)
            ·
              refine ⟨135341972592874250455740311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90227981728582833637160207 135341972592874250455740311)
              ·
                refine ⟨203012958889311375683610467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135341972592874250455740311 203012958889311375683610467)
                ·
                  refine ⟨304519438333967063525415701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203012958889311375683610467 304519438333967063525415701)
                  ·
                    refine ⟨14274348671904706102753861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 304519438333967063525415701 14274348671904706102753861)
                    ·
                      refine ⟨2676440375982132394266349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14274348671904706102753861 2676440375982132394266349)
                      ·
                        rfl

theorem cell23_5212349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_5212349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212349 prefixEnd_5212349 := by exact prefixLift 5212349
  have htrace : WordTrace (prefixWord ++ tailWord_5212349) baseStart_5212349 baseEnd_5212349 := by
    simpa [prefixWord, tailWord_5212349, baseEnd_5212349] using wordTrace_append hprefix tailTrace_5212349
  have hstable : (prefixWord ++ tailWord_5212349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212349).length < 2 ^ (prefixWord ++ tailWord_5212349).sum := by decide
  have hdescent : baseEnd_5212349 < baseStart_5212349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212437 : List Nat := [1, 3, 2, 1, 2, 1, 6, 2, 1, 1, 3]
def baseStart_5212437 : Nat := 118140960795 + 5212437 * 2 ^ 59
def prefixEnd_5212437 : Nat := 4983230072969 + 3 ^ 40 * 5212437 * 2
def baseEnd_5212437 : Nat := 2676485562279728049965945

theorem tailTrace_5212437 : CollatzResearch.WordTrace tailWord_5212437 prefixEnd_5212437 2676485562279728049965945 := by
  unfold tailWord_5212437
  simp only [CollatzResearch.WordTrace]
  refine ⟨190113195817238437211203565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126742130544825624807469043 190113195817238437211203565)
  ·
    refine ⟨71292448431464413954201337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190113195817238437211203565 71292448431464413954201337)
    ·
      refine ⟨53469336323598310465651003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71292448431464413954201337 53469336323598310465651003)
      ·
        refine ⟨80204004485397465698476505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53469336323598310465651003 80204004485397465698476505)
        ·
          refine ⟨60153003364048099273857379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80204004485397465698476505 60153003364048099273857379)
          ·
            refine ⟨90229505046072148910786069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60153003364048099273857379 90229505046072148910786069)
            ·
              refine ⟨4229508049034631980193097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90229505046072148910786069 4229508049034631980193097)
              ·
                refine ⟨3172131036775973985144823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4229508049034631980193097 3172131036775973985144823)
                ·
                  refine ⟨4758196555163960977717235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3172131036775973985144823 4758196555163960977717235)
                  ·
                    refine ⟨7137294832745941466575853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4758196555163960977717235 7137294832745941466575853)
                    ·
                      refine ⟨2676485562279728049965945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7137294832745941466575853 2676485562279728049965945)
                      ·
                        rfl

theorem cell23_5212437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 1, 1, 3].length) (baseStart_5212437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212437 prefixEnd_5212437 := by exact prefixLift 5212437
  have htrace : WordTrace (prefixWord ++ tailWord_5212437) baseStart_5212437 baseEnd_5212437 := by
    simpa [prefixWord, tailWord_5212437, baseEnd_5212437] using wordTrace_append hprefix tailTrace_5212437
  have hstable : (prefixWord ++ tailWord_5212437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212437).length < 2 ^ (prefixWord ++ tailWord_5212437).sum := by decide
  have hdescent : baseEnd_5212437 < baseStart_5212437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212453 : List Nat := [1, 3, 1, 2, 5, 1, 2, 1, 1, 6]
def baseStart_5212453 : Nat := 118140960795 + 5212453 * 2 ^ 59
def prefixEnd_5212453 : Nat := 4983230072969 + 3 ^ 40 * 5212453 * 2
def baseEnd_5212453 : Nat := 892164592656733329121957

theorem tailTrace_5212453 : CollatzResearch.WordTrace tailWord_5212453 prefixEnd_5212453 892164592656733329121957 := by
  unfold tailWord_5212453
  simp only [CollatzResearch.WordTrace]
  refine ⟨190113779385180471943786013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126742519590120314629190675 190113779385180471943786013)
  ·
    refine ⟨71292667269442676978919755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190113779385180471943786013 71292667269442676978919755)
    ·
      refine ⟨106939000904164015468379633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71292667269442676978919755 106939000904164015468379633)
      ·
        refine ⟨80204250678123011601284725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106939000904164015468379633 80204250678123011601284725)
        ·
          refine ⟨7519148501074032337620443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80204250678123011601284725 7519148501074032337620443)
          ·
            refine ⟨11278722751611048506430665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7519148501074032337620443 11278722751611048506430665)
            ·
              refine ⟨8459042063708286379822999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11278722751611048506430665 8459042063708286379822999)
              ·
                refine ⟨12688563095562429569734499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8459042063708286379822999 12688563095562429569734499)
                ·
                  refine ⟨19032844643343644354601749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12688563095562429569734499 19032844643343644354601749)
                  ·
                    refine ⟨892164592656733329121957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19032844643343644354601749 892164592656733329121957)
                    ·
                      rfl

theorem cell23_5212453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 6].length) (baseStart_5212453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212453 prefixEnd_5212453 := by exact prefixLift 5212453
  have htrace : WordTrace (prefixWord ++ tailWord_5212453) baseStart_5212453 baseEnd_5212453 := by
    simpa [prefixWord, tailWord_5212453, baseEnd_5212453] using wordTrace_append hprefix tailTrace_5212453
  have hstable : (prefixWord ++ tailWord_5212453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212453).length < 2 ^ (prefixWord ++ tailWord_5212453).sum := by decide
  have hdescent : baseEnd_5212453 < baseStart_5212453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212473 : List Nat := [1, 2, 1, 6, 1, 1, 2, 2, 1, 2, 4]
def baseStart_5212473 : Nat := 118140960795 + 5212473 * 2 ^ 59
def prefixEnd_5212473 : Nat := 4983230072969 + 3 ^ 40 * 5212473 * 2
def baseEnd_5212473 : Nat := 2676504047583289909115779

theorem tailTrace_5212473 : CollatzResearch.WordTrace tailWord_5212473 prefixEnd_5212473 2676504047583289909115779 := by
  unfold tailWord_5212473
  simp only [CollatzResearch.WordTrace]
  refine ⟨190114508845108015359514073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126743005896738676906342715 190114508845108015359514073)
  ·
    refine ⟨142585881633831011519635555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190114508845108015359514073 142585881633831011519635555)
    ·
      refine ⟨213878822450746517279453333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142585881633831011519635555 213878822450746517279453333)
      ·
        refine ⟨10025569802378742997474375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 213878822450746517279453333 10025569802378742997474375)
        ·
          refine ⟨15038354703568114496211563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10025569802378742997474375 15038354703568114496211563)
          ·
            refine ⟨22557532055352171744317345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15038354703568114496211563 22557532055352171744317345)
            ·
              refine ⟨16918149041514128808238009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22557532055352171744317345 16918149041514128808238009)
              ·
                refine ⟨12688611781135596606178507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16918149041514128808238009 12688611781135596606178507)
                ·
                  refine ⟨19032917671703394909267761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12688611781135596606178507 19032917671703394909267761)
                  ·
                    refine ⟨14274688253777546181950821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19032917671703394909267761 14274688253777546181950821)
                    ·
                      refine ⟨2676504047583289909115779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14274688253777546181950821 2676504047583289909115779)
                      ·
                        rfl

theorem cell23_5212473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_5212473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212473 prefixEnd_5212473 := by exact prefixLift 5212473
  have htrace : WordTrace (prefixWord ++ tailWord_5212473) baseStart_5212473 baseEnd_5212473 := by
    simpa [prefixWord, tailWord_5212473, baseEnd_5212473] using wordTrace_append hprefix tailTrace_5212473
  have hstable : (prefixWord ++ tailWord_5212473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212473).length < 2 ^ (prefixWord ++ tailWord_5212473).sum := by decide
  have hdescent : baseEnd_5212473 < baseStart_5212473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212747 : List Nat := [1, 1, 1, 1, 3, 1, 4, 4, 3, 2, 2]
def baseStart_5212747 : Nat := 118140960795 + 5212747 * 2 ^ 59
def prefixEnd_5212747 : Nat := 4983230072969 + 3 ^ 40 * 5212747 * 2
def baseEnd_5212747 : Nat := 2676644741282621837089519

theorem tailTrace_5212747 : CollatzResearch.WordTrace tailWord_5212747 prefixEnd_5212747 2676644741282621837089519 := by
  unfold tailWord_5212747
  simp only [CollatzResearch.WordTrace]
  refine ⟨190124502446115360154988495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126749668297410240103325663 190124502446115360154988495)
  ·
    refine ⟨285186753669173040232482743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190124502446115360154988495 285186753669173040232482743)
    ·
      refine ⟨427780130503759560348724115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285186753669173040232482743 427780130503759560348724115)
      ·
        refine ⟨641670195755639340523086173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427780130503759560348724115 641670195755639340523086173)
        ·
          refine ⟨240626323408364752696157315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 641670195755639340523086173 240626323408364752696157315)
          ·
            refine ⟨360939485112547129044235973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240626323408364752696157315 360939485112547129044235973)
            ·
              refine ⟨67676153458602586695794245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 360939485112547129044235973 67676153458602586695794245)
              ·
                refine ⟨12689278773487985005461421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67676153458602586695794245 12689278773487985005461421)
                ·
                  refine ⟨4758479540057994377048033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12689278773487985005461421 4758479540057994377048033)
                  ·
                    refine ⟨3568859655043495782786025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4758479540057994377048033 3568859655043495782786025)
                    ·
                      refine ⟨2676644741282621837089519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3568859655043495782786025 2676644741282621837089519)
                      ·
                        rfl

theorem cell23_5212747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 2, 2].length) (baseStart_5212747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212747 prefixEnd_5212747 := by exact prefixLift 5212747
  have htrace : WordTrace (prefixWord ++ tailWord_5212747) baseStart_5212747 baseEnd_5212747 := by
    simpa [prefixWord, tailWord_5212747, baseEnd_5212747] using wordTrace_append hprefix tailTrace_5212747
  have hstable : (prefixWord ++ tailWord_5212747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212747).length < 2 ^ (prefixWord ++ tailWord_5212747).sum := by decide
  have hdescent : baseEnd_5212747 < baseStart_5212747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212753 : List Nat := [1, 2, 2, 1, 3, 3, 2, 9]
def baseStart_5212753 : Nat := 118140960795 + 5212753 * 2 ^ 59
def prefixEnd_5212753 : Nat := 4983230072969 + 3 ^ 40 * 5212753 * 2
def baseEnd_5212753 : Nat := 99135104524686993096833

theorem tailTrace_5212753 : CollatzResearch.WordTrace tailWord_5212753 prefixEnd_5212753 99135104524686993096833 := by
  unfold tailWord_5212753
  simp only [CollatzResearch.WordTrace]
  refine ⟨190124721284093623179706913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126749814189395748786471275 190124721284093623179706913)
  ·
    refine ⟨142593540963070217384780185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190124721284093623179706913 142593540963070217384780185)
    ·
      refine ⟨106945155722302663038585139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142593540963070217384780185 106945155722302663038585139)
      ·
        refine ⟨160417733583453994557877709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106945155722302663038585139 160417733583453994557877709)
        ·
          refine ⟨60156650093795247959204141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160417733583453994557877709 60156650093795247959204141)
          ·
            refine ⟨22558743785173217984701553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60156650093795247959204141 22558743785173217984701553)
            ·
              refine ⟨16919057838879913488526165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22558743785173217984701553 16919057838879913488526165)
              ·
                refine ⟨99135104524686993096833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16919057838879913488526165 99135104524686993096833)
                ·
                  rfl

theorem cell23_5212753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 9].length) (baseStart_5212753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212753 prefixEnd_5212753 := by exact prefixLift 5212753
  have htrace : WordTrace (prefixWord ++ tailWord_5212753) baseStart_5212753 baseEnd_5212753 := by
    simpa [prefixWord, tailWord_5212753, baseEnd_5212753] using wordTrace_append hprefix tailTrace_5212753
  have hstable : (prefixWord ++ tailWord_5212753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212753).length < 2 ^ (prefixWord ++ tailWord_5212753).sum := by decide
  have hdescent : baseEnd_5212753 < baseStart_5212753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212770 : List Nat := [3, 3, 2, 3, 12]
def baseStart_5212770 : Nat := 118140960795 + 5212770 * 2 ^ 59
def prefixEnd_5212770 : Nat := 4983230072969 + 3 ^ 40 * 5212770 * 2
def baseEnd_5212770 : Nat := 3671682512123011312897

theorem tailTrace_5212770 : CollatzResearch.WordTrace tailWord_5212770 prefixEnd_5212770 3671682512123011312897 := by
  unfold tailWord_5212770
  simp only [CollatzResearch.WordTrace]
  refine ⟨47531335331258008770768941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126750227550021356722050509 47531335331258008770768941)
  ·
    refine ⟨17824250749221753289038353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47531335331258008770768941 17824250749221753289038353)
    ·
      refine ⟨13368188061916314966778765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17824250749221753289038353 13368188061916314966778765)
      ·
        refine ⟨5013070523218618112542037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13368188061916314966778765 5013070523218618112542037)
        ·
          refine ⟨3671682512123011312897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5013070523218618112542037 3671682512123011312897)
          ·
            rfl

theorem cell23_5212770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 12].length) (baseStart_5212770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212770 prefixEnd_5212770 := by exact prefixLift 5212770
  have htrace : WordTrace (prefixWord ++ tailWord_5212770) baseStart_5212770 baseEnd_5212770 := by
    simpa [prefixWord, tailWord_5212770, baseEnd_5212770] using wordTrace_append hprefix tailTrace_5212770
  have hstable : (prefixWord ++ tailWord_5212770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212770).length < 2 ^ (prefixWord ++ tailWord_5212770).sum := by decide
  have hdescent : baseEnd_5212770 < baseStart_5212770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212783 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 2, 7]
def baseStart_5212783 : Nat := 118140960795 + 5212783 * 2 ^ 59
def prefixEnd_5212783 : Nat := 4983230072969 + 3 ^ 40 * 5212783 * 2
def baseEnd_5212783 : Nat := 892221075528727898746451

theorem tailTrace_5212783 : CollatzResearch.WordTrace tailWord_5212783 prefixEnd_5212783 892221075528727898746451 := by
  unfold tailWord_5212783
  simp only [CollatzResearch.WordTrace]
  refine ⟨190125815473984938303299003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126750543649323292202199335 190125815473984938303299003)
  ·
    refine ⟨285188723210977407454948505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190125815473984938303299003 285188723210977407454948505)
    ·
      refine ⟨213891542408233055591211379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285188723210977407454948505 213891542408233055591211379)
      ·
        refine ⟨320837313612349583386817069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213891542408233055591211379 320837313612349583386817069)
        ·
          refine ⟨120313992604631093770056401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320837313612349583386817069 120313992604631093770056401)
          ·
            refine ⟨90235494453473320327542301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120313992604631093770056401 90235494453473320327542301)
            ·
              refine ⟨33838310420052495122828363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90235494453473320327542301 33838310420052495122828363)
              ·
                refine ⟨50757465630078742684242545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33838310420052495122828363 50757465630078742684242545)
                ·
                  refine ⟨38068099222559057013181909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50757465630078742684242545 38068099222559057013181909)
                  ·
                    refine ⟨892221075528727898746451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38068099222559057013181909 892221075528727898746451)
                    ·
                      rfl

theorem cell23_5212783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 7].length) (baseStart_5212783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212783 prefixEnd_5212783 := by exact prefixLift 5212783
  have htrace : WordTrace (prefixWord ++ tailWord_5212783) baseStart_5212783 baseEnd_5212783 := by
    simpa [prefixWord, tailWord_5212783, baseEnd_5212783] using wordTrace_append hprefix tailTrace_5212783
  have hstable : (prefixWord ++ tailWord_5212783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212783).length < 2 ^ (prefixWord ++ tailWord_5212783).sum := by decide
  have hdescent : baseEnd_5212783 < baseStart_5212783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212802 : List Nat := [3, 4, 3, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_5212802 : Nat := 118140960795 + 5212802 * 2 ^ 59
def prefixEnd_5212802 : Nat := 4983230072969 + 3 ^ 40 * 5212802 * 2
def baseEnd_5212802 : Nat := 2676672982718619121901767

theorem tailTrace_5212802 : CollatzResearch.WordTrace tailWord_5212802 prefixEnd_5212802 2676672982718619121901767 := by
  unfold tailWord_5212802
  simp only [CollatzResearch.WordTrace]
  refine ⟨47531627115229026137060165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126751005640610736365493773 47531627115229026137060165)
  ·
    refine ⟨8912180084105442400698781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47531627115229026137060165 8912180084105442400698781)
    ·
      refine ⟨3342067531539540900262043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8912180084105442400698781 3342067531539540900262043)
      ·
        refine ⟨5013101297309311350393065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3342067531539540900262043 5013101297309311350393065)
        ·
          refine ⟨3759825972981983512794799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5013101297309311350393065 3759825972981983512794799)
          ·
            refine ⟨5639738959472975269192199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3759825972981983512794799 5639738959472975269192199)
            ·
              refine ⟨8459608439209462903788299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5639738959472975269192199 8459608439209462903788299)
              ·
                refine ⟨12689412658814194355682449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8459608439209462903788299 12689412658814194355682449)
                ·
                  refine ⟨9517059494110645766761837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12689412658814194355682449 9517059494110645766761837)
                  ·
                    refine ⟨3568897310291492162535689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9517059494110645766761837 3568897310291492162535689)
                    ·
                      refine ⟨2676672982718619121901767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3568897310291492162535689 2676672982718619121901767)
                      ·
                        rfl

theorem cell23_5212802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_5212802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212802 prefixEnd_5212802 := by exact prefixLift 5212802
  have htrace : WordTrace (prefixWord ++ tailWord_5212802) baseStart_5212802 baseEnd_5212802 := by
    simpa [prefixWord, tailWord_5212802, baseEnd_5212802] using wordTrace_append hprefix tailTrace_5212802
  have hstable : (prefixWord ++ tailWord_5212802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212802).length < 2 ^ (prefixWord ++ tailWord_5212802).sum := by decide
  have hdescent : baseEnd_5212802 < baseStart_5212802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212807 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 3, 3, 2]
def baseStart_5212807 : Nat := 118140960795 + 5212807 * 2 ^ 59
def prefixEnd_5212807 : Nat := 4983230072969 + 3 ^ 40 * 5212807 * 2
def baseEnd_5212807 : Nat := 2676675550121891602339243

theorem tailTrace_5212807 : CollatzResearch.WordTrace tailWord_5212807 prefixEnd_5212807 2676675550121891602339243 := by
  unfold tailWord_5212807
  simp only [CollatzResearch.WordTrace]
  refine ⟨190126690825897990402172675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126751127217265326934781783 190126690825897990402172675)
  ·
    refine ⟨285190036238846985603259013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190126690825897990402172675 285190036238846985603259013)
    ·
      refine ⟨53473131794783809800611065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 285190036238846985603259013 53473131794783809800611065)
      ·
        refine ⟨40104848846087857350458299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53473131794783809800611065 40104848846087857350458299)
        ·
          refine ⟨60157273269131786025687449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40104848846087857350458299 60157273269131786025687449)
          ·
            refine ⟨45117954951848839519265587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60157273269131786025687449 45117954951848839519265587)
            ·
              refine ⟨67676932427773259278898381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45117954951848839519265587 67676932427773259278898381)
              ·
                refine ⟨25378849660414972229586893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67676932427773259278898381 25378849660414972229586893)
                ·
                  refine ⟨9517068622655614586095085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25378849660414972229586893 9517068622655614586095085)
                  ·
                    refine ⟨3568900733495855469785657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9517068622655614586095085 3568900733495855469785657)
                    ·
                      refine ⟨2676675550121891602339243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3568900733495855469785657 2676675550121891602339243)
                      ·
                        rfl

theorem cell23_5212807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_5212807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212807 prefixEnd_5212807 := by exact prefixLift 5212807
  have htrace : WordTrace (prefixWord ++ tailWord_5212807) baseStart_5212807 baseEnd_5212807 := by
    simpa [prefixWord, tailWord_5212807, baseEnd_5212807] using wordTrace_append hprefix tailTrace_5212807
  have hstable : (prefixWord ++ tailWord_5212807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212807).length < 2 ^ (prefixWord ++ tailWord_5212807).sum := by decide
  have hdescent : baseEnd_5212807 < baseStart_5212807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212824 : List Nat := [2, 1, 2, 4, 1, 1, 3, 3, 1, 3, 2]
def baseStart_5212824 : Nat := 118140960795 + 5212824 * 2 ^ 59
def prefixEnd_5212824 : Nat := 4983230072969 + 3 ^ 40 * 5212824 * 2
def baseEnd_5212824 : Nat := 2676684279293018035826665

theorem tailTrace_5212824 : CollatzResearch.WordTrace tailWord_5212824 prefixEnd_5212824 2676684279293018035826665 := by
  unfold tailWord_5212824
  simp only [CollatzResearch.WordTrace]
  refine ⟨95063655433418201152770763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126751540577890934870361017 95063655433418201152770763)
  ·
    refine ⟨142595483150127301729156145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95063655433418201152770763 142595483150127301729156145)
    ·
      refine ⟨106946612362595476296867109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142595483150127301729156145 106946612362595476296867109)
      ·
        refine ⟨20052489817986651805662583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106946612362595476296867109 20052489817986651805662583)
        ·
          refine ⟨30078734726979977708493875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20052489817986651805662583 30078734726979977708493875)
          ·
            refine ⟨45118102090469966562740813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30078734726979977708493875 45118102090469966562740813)
            ·
              refine ⟨16919288283926237461027805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45118102090469966562740813 16919288283926237461027805)
              ·
                refine ⟨6344733106472339047885427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16919288283926237461027805 6344733106472339047885427)
                ·
                  refine ⟨9517099659708508571828141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6344733106472339047885427 9517099659708508571828141)
                  ·
                    refine ⟨3568912372390690714435553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9517099659708508571828141 3568912372390690714435553)
                    ·
                      refine ⟨2676684279293018035826665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3568912372390690714435553 2676684279293018035826665)
                      ·
                        rfl

theorem cell23_5212824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_5212824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212824 prefixEnd_5212824 := by exact prefixLift 5212824
  have htrace : WordTrace (prefixWord ++ tailWord_5212824) baseStart_5212824 baseEnd_5212824 := by
    simpa [prefixWord, tailWord_5212824, baseEnd_5212824] using wordTrace_append hprefix tailTrace_5212824
  have hstable : (prefixWord ++ tailWord_5212824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212824).length < 2 ^ (prefixWord ++ tailWord_5212824).sum := by decide
  have hdescent : baseEnd_5212824 < baseStart_5212824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212860 : List Nat := [2, 2, 2, 3, 1, 1, 1, 4, 7]
def baseStart_5212860 : Nat := 118140960795 + 5212860 * 2 ^ 59
def prefixEnd_5212860 : Nat := 4983230072969 + 3 ^ 40 * 5212860 * 2
def baseEnd_5212860 : Nat := 297411418288508877219611

theorem tailTrace_5212860 : CollatzResearch.WordTrace tailWord_5212860 prefixEnd_5212860 297411418288508877219611 := by
  unfold tailWord_5212860
  simp only [CollatzResearch.WordTrace]
  refine ⟨95064311947352990226926017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126752415929803986969234689 95064311947352990226926017)
  ·
    refine ⟨71298233960514742670194513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95064311947352990226926017 71298233960514742670194513)
    ·
      refine ⟨53473675470386057002645885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71298233960514742670194513 53473675470386057002645885)
      ·
        refine ⟨20052628301394771375992207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53473675470386057002645885 20052628301394771375992207)
        ·
          refine ⟨30078942452092157063988311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20052628301394771375992207 30078942452092157063988311)
          ·
            refine ⟨45118413678138235595982467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30078942452092157063988311 45118413678138235595982467)
            ·
              refine ⟨67677620517207353393973701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45118413678138235595982467 67677620517207353393973701)
              ·
                refine ⟨12689553846976378761370069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67677620517207353393973701 12689553846976378761370069)
                ·
                  refine ⟨297411418288508877219611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12689553846976378761370069 297411418288508877219611)
                  ·
                    rfl

theorem cell23_5212860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 7].length) (baseStart_5212860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212860 prefixEnd_5212860 := by exact prefixLift 5212860
  have htrace : WordTrace (prefixWord ++ tailWord_5212860) baseStart_5212860 baseEnd_5212860 := by
    simpa [prefixWord, tailWord_5212860, baseEnd_5212860] using wordTrace_append hprefix tailTrace_5212860
  have hstable : (prefixWord ++ tailWord_5212860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212860).length < 2 ^ (prefixWord ++ tailWord_5212860).sum := by decide
  have hdescent : baseEnd_5212860 < baseStart_5212860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212900 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 1, 1, 7]
def baseStart_5212900 : Nat := 118140960795 + 5212900 * 2 ^ 59
def prefixEnd_5212900 : Nat := 4983230072969 + 3 ^ 40 * 5212900 * 2
def baseEnd_5212900 : Nat := 2676723303822759738476315

theorem tailTrace_5212900 : CollatzResearch.WordTrace tailWord_5212900 prefixEnd_5212900 2676723303822759738476315 := by
  unfold tailWord_5212900
  simp only [CollatzResearch.WordTrace]
  refine ⟨95065041407280533642654077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126753388543040711523538769 95065041407280533642654077)
  ·
    refine ⟨35649390527730200115995279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95065041407280533642654077 35649390527730200115995279)
    ·
      refine ⟨53474085791595300173992919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35649390527730200115995279 53474085791595300173992919)
      ·
        refine ⟨80211128687392950260989379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53474085791595300173992919 80211128687392950260989379)
        ·
          refine ⟨120316693031089425391484069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80211128687392950260989379 120316693031089425391484069)
          ·
            refine ⟨22559379943329267260903263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120316693031089425391484069 22559379943329267260903263)
            ·
              refine ⟨33839069914993900891354895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22559379943329267260903263 33839069914993900891354895)
              ·
                refine ⟨50758604872490851337032343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33839069914993900891354895 50758604872490851337032343)
                ·
                  refine ⟨76137907308736277005548515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50758604872490851337032343 76137907308736277005548515)
                  ·
                    refine ⟨114206860963104415508322773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76137907308736277005548515 114206860963104415508322773)
                    ·
                      refine ⟨2676723303822759738476315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114206860963104415508322773 2676723303822759738476315)
                      ·
                        rfl

theorem cell23_5212900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_5212900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212900 prefixEnd_5212900 := by exact prefixLift 5212900
  have htrace : WordTrace (prefixWord ++ tailWord_5212900) baseStart_5212900 baseEnd_5212900 := by
    simpa [prefixWord, tailWord_5212900, baseEnd_5212900] using wordTrace_append hprefix tailTrace_5212900
  have hstable : (prefixWord ++ tailWord_5212900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212900).length < 2 ^ (prefixWord ++ tailWord_5212900).sum := by decide
  have hdescent : baseEnd_5212900 < baseStart_5212900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212927 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 4, 4, 2]
def baseStart_5212927 : Nat := 118140960795 + 5212927 * 2 ^ 59
def prefixEnd_5212927 : Nat := 4983230072969 + 3 ^ 40 * 5212927 * 2
def baseEnd_5212927 : Nat := 2676737167800431132838691

theorem tailTrace_5212927 : CollatzResearch.WordTrace tailWord_5212927 prefixEnd_5212927 2676737167800431132838691 := by
  unfold tailWord_5212927
  simp only [CollatzResearch.WordTrace]
  refine ⟨190131067585463250896541035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126754045056975500597694023 190131067585463250896541035)
  ·
    refine ⟨285196601378194876344811553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190131067585463250896541035 285196601378194876344811553)
    ·
      refine ⟨213897451033646157258608665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285196601378194876344811553 213897451033646157258608665)
      ·
        refine ⟨160423088275234617943956499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213897451033646157258608665 160423088275234617943956499)
        ·
          refine ⟨240634632412851926915934749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160423088275234617943956499 240634632412851926915934749)
          ·
            refine ⟨90237987154819472593475531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240634632412851926915934749 90237987154819472593475531)
            ·
              refine ⟨135356980732229208890213297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90237987154819472593475531 135356980732229208890213297)
              ·
                refine ⟨101517735549171906667659973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135356980732229208890213297 101517735549171906667659973)
                ·
                  refine ⟨19034575415469732500186245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101517735549171906667659973 19034575415469732500186245)
                  ·
                    refine ⟨3568982890400574843784921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19034575415469732500186245 3568982890400574843784921)
                    ·
                      refine ⟨2676737167800431132838691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3568982890400574843784921 2676737167800431132838691)
                      ·
                        rfl

theorem cell23_5212927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 4, 2].length) (baseStart_5212927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212927 prefixEnd_5212927 := by exact prefixLift 5212927
  have htrace : WordTrace (prefixWord ++ tailWord_5212927) baseStart_5212927 baseEnd_5212927 := by
    simpa [prefixWord, tailWord_5212927, baseEnd_5212927] using wordTrace_append hprefix tailTrace_5212927
  have hstable : (prefixWord ++ tailWord_5212927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212927).length < 2 ^ (prefixWord ++ tailWord_5212927).sum := by decide
  have hdescent : baseEnd_5212927 < baseStart_5212927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212940 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 2, 1, 6]
def baseStart_5212940 : Nat := 118140960795 + 5212940 * 2 ^ 59
def prefixEnd_5212940 : Nat := 4983230072969 + 3 ^ 40 * 5212940 * 2
def baseEnd_5212940 : Nat := 2676743843048939581976131

theorem tailTrace_5212940 : CollatzResearch.WordTrace tailWord_5212940 prefixEnd_5212940 2676743843048939581976131 := by
  unfold tailWord_5212940
  simp only [CollatzResearch.WordTrace]
  refine ⟨95065770867208077058382137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126754361156277436077842849 95065770867208077058382137)
  ·
    refine ⟨71299328150406057793786603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95065770867208077058382137 71299328150406057793786603)
    ·
      refine ⟨106948992225609086690679905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71299328150406057793786603 106948992225609086690679905)
      ·
        refine ⟨80211744169206815018009929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106948992225609086690679905 80211744169206815018009929)
        ·
          refine ⟨60158808126905111263507447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80211744169206815018009929 60158808126905111263507447)
          ·
            refine ⟨90238212190357666895261171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60158808126905111263507447 90238212190357666895261171)
            ·
              refine ⟨135357318285536500342891757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90238212190357666895261171 135357318285536500342891757)
              ·
                refine ⟨50758994357076187628584409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135357318285536500342891757 50758994357076187628584409)
                ·
                  refine ⟨38069245767807140721438307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50758994357076187628584409 38069245767807140721438307)
                  ·
                    refine ⟨57103868651710711082157461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38069245767807140721438307 57103868651710711082157461)
                    ·
                      refine ⟨2676743843048939581976131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57103868651710711082157461 2676743843048939581976131)
                      ·
                        rfl

theorem cell23_5212940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_5212940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212940 prefixEnd_5212940 := by exact prefixLift 5212940
  have htrace : WordTrace (prefixWord ++ tailWord_5212940) baseStart_5212940 baseEnd_5212940 := by
    simpa [prefixWord, tailWord_5212940, baseEnd_5212940] using wordTrace_append hprefix tailTrace_5212940
  have hstable : (prefixWord ++ tailWord_5212940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212940).length < 2 ^ (prefixWord ++ tailWord_5212940).sum := by decide
  have hdescent : baseEnd_5212940 < baseStart_5212940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212947 : List Nat := [1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 3]
def baseStart_5212947 : Nat := 118140960795 + 5212947 * 2 ^ 59
def prefixEnd_5212947 : Nat := 4983230072969 + 3 ^ 40 * 5212947 * 2
def baseEnd_5212947 : Nat := 2676747437413521054588599

theorem tailTrace_5212947 : CollatzResearch.WordTrace tailWord_5212947 prefixEnd_5212947 2676747437413521054588599 := by
  unfold tailWord_5212947
  simp only [CollatzResearch.WordTrace]
  refine ⟨190131797045390794312269095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126754531363593862874846063 190131797045390794312269095)
  ·
    refine ⟨285197695568086191468403643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190131797045390794312269095 285197695568086191468403643)
    ·
      refine ⟨427796543352129287202605465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285197695568086191468403643 427796543352129287202605465)
      ·
        refine ⟨320847407514096965401954099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 427796543352129287202605465 320847407514096965401954099)
        ·
          refine ⟨481271111271145448102931149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320847407514096965401954099 481271111271145448102931149)
          ·
            refine ⟨180476666726679543038599181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 481271111271145448102931149 180476666726679543038599181)
            ·
              refine ⟨67678750022504828639474693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180476666726679543038599181 67678750022504828639474693)
              ·
                refine ⟨12689765629219655369901505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67678750022504828639474693 12689765629219655369901505)
                ·
                  refine ⟨9517324221914741527426129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12689765629219655369901505 9517324221914741527426129)
                  ·
                    refine ⟨7137993166436056145569597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9517324221914741527426129 7137993166436056145569597)
                    ·
                      refine ⟨2676747437413521054588599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7137993166436056145569597 2676747437413521054588599)
                      ·
                        rfl

theorem cell23_5212947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 3].length) (baseStart_5212947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212947 prefixEnd_5212947 := by exact prefixLift 5212947
  have htrace : WordTrace (prefixWord ++ tailWord_5212947) baseStart_5212947 baseEnd_5212947 := by
    simpa [prefixWord, tailWord_5212947, baseEnd_5212947] using wordTrace_append hprefix tailTrace_5212947
  have hstable : (prefixWord ++ tailWord_5212947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212947).length < 2 ^ (prefixWord ++ tailWord_5212947).sum := by decide
  have hdescent : baseEnd_5212947 < baseStart_5212947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5212981 : List Nat := [1, 3, 3, 1, 3, 3, 1, 1, 2, 2, 3]
def baseStart_5212981 : Nat := 118140960795 + 5212981 * 2 ^ 59
def prefixEnd_5212981 : Nat := 4983230072969 + 3 ^ 40 * 5212981 * 2
def baseEnd_5212981 : Nat := 2676764895755773921563443

theorem tailTrace_5212981 : CollatzResearch.WordTrace tailWord_5212981 prefixEnd_5212981 2676764895755773921563443 := by
  unfold tailWord_5212981
  simp only [CollatzResearch.WordTrace]
  refine ⟨190133037127267618119006797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126755358084845078746004531 190133037127267618119006797)
  ·
    refine ⟨71299888922725356794627549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190133037127267618119006797 71299888922725356794627549)
    ·
      refine ⟨26737458346022008797985331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71299888922725356794627549 26737458346022008797985331)
      ·
        refine ⟨40106187519033013196977997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26737458346022008797985331 40106187519033013196977997)
        ·
          refine ⟨15039820319637379948866749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40106187519033013196977997 15039820319637379948866749)
          ·
            refine ⟨5639932619864017480825031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15039820319637379948866749 5639932619864017480825031)
            ·
              refine ⟨8459898929796026221237547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5639932619864017480825031 8459898929796026221237547)
              ·
                refine ⟨12689848394694039331856321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8459898929796026221237547 12689848394694039331856321)
                ·
                  refine ⟨9517386296020529498892241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12689848394694039331856321 9517386296020529498892241)
                  ·
                    refine ⟨7138039722015397124169181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9517386296020529498892241 7138039722015397124169181)
                    ·
                      refine ⟨2676764895755773921563443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7138039722015397124169181 2676764895755773921563443)
                      ·
                        rfl

theorem cell23_5212981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_5212981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5212981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5212981 prefixEnd_5212981 := by exact prefixLift 5212981
  have htrace : WordTrace (prefixWord ++ tailWord_5212981) baseStart_5212981 baseEnd_5212981 := by
    simpa [prefixWord, tailWord_5212981, baseEnd_5212981] using wordTrace_append hprefix tailTrace_5212981
  have hstable : (prefixWord ++ tailWord_5212981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5212981).length < 2 ^ (prefixWord ++ tailWord_5212981).sum := by decide
  have hdescent : baseEnd_5212981 < baseStart_5212981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5212981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213037 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_5213037 : Nat := 118140960795 + 5213037 * 2 ^ 59
def prefixEnd_5213037 : Nat := 4983230072969 + 3 ^ 40 * 5213037 * 2
def baseEnd_5213037 : Nat := 2676793650672425702463185

theorem tailTrace_5213037 : CollatzResearch.WordTrace tailWord_5213037 prefixEnd_5213037 2676793650672425702463185 := by
  unfold tailWord_5213037
  simp only [CollatzResearch.WordTrace]
  refine ⟨190135079615064739683045365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126756719743376493122030243 190135079615064739683045365)
  ·
    refine ⟨17825163713912319345285503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 190135079615064739683045365 17825163713912319345285503)
    ·
      refine ⟨26737745570868479017928255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17825163713912319345285503 26737745570868479017928255)
      ·
        refine ⟨40106618356302718526892383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26737745570868479017928255 40106618356302718526892383)
        ·
          refine ⟨60159927534454077790338575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40106618356302718526892383 60159927534454077790338575)
          ·
            refine ⟨90239891301681116685507863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60159927534454077790338575 90239891301681116685507863)
            ·
              refine ⟨135359836952521675028261795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90239891301681116685507863 135359836952521675028261795)
              ·
                refine ⟨203039755428782512542392693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135359836952521675028261795 203039755428782512542392693)
                ·
                  refine ⟨19034977071448360550849315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 203039755428782512542392693 19034977071448360550849315)
                  ·
                    refine ⟨28552465607172540826273973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19034977071448360550849315 28552465607172540826273973)
                    ·
                      refine ⟨2676793650672425702463185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28552465607172540826273973 2676793650672425702463185)
                      ·
                        rfl

theorem cell23_5213037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_5213037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213037 prefixEnd_5213037 := by exact prefixLift 5213037
  have htrace : WordTrace (prefixWord ++ tailWord_5213037) baseStart_5213037 baseEnd_5213037 := by
    simpa [prefixWord, tailWord_5213037, baseEnd_5213037] using wordTrace_append hprefix tailTrace_5213037
  have hstable : (prefixWord ++ tailWord_5213037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213037).length < 2 ^ (prefixWord ++ tailWord_5213037).sum := by decide
  have hdescent : baseEnd_5213037 < baseStart_5213037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213045 : List Nat := [1, 3, 4, 1, 1, 4, 1, 3, 1, 1, 3]
def baseStart_5213045 : Nat := 118140960795 + 5213045 * 2 ^ 59
def prefixEnd_5213045 : Nat := 4983230072969 + 3 ^ 40 * 5213045 * 2
def baseEnd_5213045 : Nat := 2676797758517661671163149

theorem tailTrace_5213045 : CollatzResearch.WordTrace tailWord_5213045 prefixEnd_5213045 2676797758517661671163149 := by
  unfold tailWord_5213045
  simp only [CollatzResearch.WordTrace]
  refine ⟨190135371399035757049336589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126756914266023838032891059 190135371399035757049336589)
  ·
    refine ⟨71300764274638408893501221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190135371399035757049336589 71300764274638408893501221)
    ·
      refine ⟨13368893301494701667531479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71300764274638408893501221 13368893301494701667531479)
      ·
        refine ⟨20053339952242052501297219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13368893301494701667531479 20053339952242052501297219)
        ·
          refine ⟨30080009928363078751945829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20053339952242052501297219 30080009928363078751945829)
          ·
            refine ⟨5640001861568077265989843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30080009928363078751945829 5640001861568077265989843)
            ·
              refine ⟨8460002792352115898984765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5640001861568077265989843 8460002792352115898984765)
              ·
                refine ⟨3172501047132043462119287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8460002792352115898984765 3172501047132043462119287)
                ·
                  refine ⟨4758751570698065193178931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3172501047132043462119287 4758751570698065193178931)
                  ·
                    refine ⟨7138127356047097789768397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4758751570698065193178931 7138127356047097789768397)
                    ·
                      refine ⟨2676797758517661671163149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7138127356047097789768397 2676797758517661671163149)
                      ·
                        rfl

theorem cell23_5213045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_5213045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213045 prefixEnd_5213045 := by exact prefixLift 5213045
  have htrace : WordTrace (prefixWord ++ tailWord_5213045) baseStart_5213045 baseEnd_5213045 := by
    simpa [prefixWord, tailWord_5213045, baseEnd_5213045] using wordTrace_append hprefix tailTrace_5213045
  have hstable : (prefixWord ++ tailWord_5213045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213045).length < 2 ^ (prefixWord ++ tailWord_5213045).sum := by decide
  have hdescent : baseEnd_5213045 < baseStart_5213045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213047 : List Nat := [1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 4]
def baseStart_5213047 : Nat := 118140960795 + 5213047 * 2 ^ 59
def prefixEnd_5213047 : Nat := 4983230072969 + 3 ^ 40 * 5213047 * 2
def baseEnd_5213047 : Nat := 2676798785478970663338139

theorem tailTrace_5213047 : CollatzResearch.WordTrace tailWord_5213047 prefixEnd_5213047 2676798785478970663338139 := by
  unfold tailWord_5213047
  simp only [CollatzResearch.WordTrace]
  refine ⟨190135444345028511390909395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126756962896685674260606263 190135444345028511390909395)
  ·
    refine ⟨285203166517542767086364093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190135444345028511390909395 285203166517542767086364093)
    ·
      refine ⟨106951187444078537657386535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285203166517542767086364093 106951187444078537657386535)
      ·
        refine ⟨160426781166117806486079803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106951187444078537657386535 160426781166117806486079803)
        ·
          refine ⟨240640171749176709729119705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160426781166117806486079803 240640171749176709729119705)
          ·
            refine ⟨180480128811882532296839779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240640171749176709729119705 180480128811882532296839779)
            ·
              refine ⟨270720193217823798445259669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180480128811882532296839779 270720193217823798445259669)
              ·
                refine ⟨12690009057085490552121547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 270720193217823798445259669 12690009057085490552121547)
                ·
                  refine ⟨19035013585628235828182321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12690009057085490552121547 19035013585628235828182321)
                  ·
                    refine ⟨14276260189221176871136741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19035013585628235828182321 14276260189221176871136741)
                    ·
                      refine ⟨2676798785478970663338139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14276260189221176871136741 2676798785478970663338139)
                      ·
                        rfl

theorem cell23_5213047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_5213047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213047 prefixEnd_5213047 := by exact prefixLift 5213047
  have htrace : WordTrace (prefixWord ++ tailWord_5213047) baseStart_5213047 baseEnd_5213047 := by
    simpa [prefixWord, tailWord_5213047, baseEnd_5213047] using wordTrace_append hprefix tailTrace_5213047
  have hstable : (prefixWord ++ tailWord_5213047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213047).length < 2 ^ (prefixWord ++ tailWord_5213047).sum := by decide
  have hdescent : baseEnd_5213047 < baseStart_5213047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213068 : List Nat := [2, 2, 1, 2, 1, 2, 2, 6, 1, 2, 2]
def baseStart_5213068 : Nat := 118140960795 + 5213068 * 2 ^ 59
def prefixEnd_5213068 : Nat := 4983230072969 + 3 ^ 40 * 5213068 * 2
def baseEnd_5213068 : Nat := 2676809568572715081175543

theorem tailTrace_5213068 : CollatzResearch.WordTrace tailWord_5213068 prefixEnd_5213068 2676809568572715081175543 := by
  unfold tailWord_5213068
  simp only [CollatzResearch.WordTrace]
  refine ⟨95068105138976215988711929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126757473518634954651615905 95068105138976215988711929)
  ·
    refine ⟨71301078854232161991533947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95068105138976215988711929 71301078854232161991533947)
    ·
      refine ⟨106951618281348242987300921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71301078854232161991533947 106951618281348242987300921)
      ·
        refine ⟨80213713711011182240475691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106951618281348242987300921 80213713711011182240475691)
        ·
          refine ⟨120320570566516773360713537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80213713711011182240475691 120320570566516773360713537)
          ·
            refine ⟨90240427924887580020535153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120320570566516773360713537 90240427924887580020535153)
            ·
              refine ⟨67680320943665685015401365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90240427924887580020535153 67680320943665685015401365)
              ·
                refine ⟨3172515044234328985096939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67680320943665685015401365 3172515044234328985096939)
                ·
                  refine ⟨4758772566351493477645409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3172515044234328985096939 4758772566351493477645409)
                  ·
                    refine ⟨3569079424763620108234057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4758772566351493477645409 3569079424763620108234057)
                    ·
                      refine ⟨2676809568572715081175543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3569079424763620108234057 2676809568572715081175543)
                      ·
                        rfl

theorem cell23_5213068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 1, 2, 2].length) (baseStart_5213068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213068 prefixEnd_5213068 := by exact prefixLift 5213068
  have htrace : WordTrace (prefixWord ++ tailWord_5213068) baseStart_5213068 baseEnd_5213068 := by
    simpa [prefixWord, tailWord_5213068, baseEnd_5213068] using wordTrace_append hprefix tailTrace_5213068
  have hstable : (prefixWord ++ tailWord_5213068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213068).length < 2 ^ (prefixWord ++ tailWord_5213068).sum := by decide
  have hdescent : baseEnd_5213068 < baseStart_5213068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213111 : List Nat := [1, 1, 3, 1, 3, 1, 2, 5, 1, 3, 2]
def baseStart_5213111 : Nat := 118140960795 + 5213111 * 2 ^ 59
def prefixEnd_5213111 : Nat := 4983230072969 + 3 ^ 40 * 5213111 * 2
def baseEnd_5213111 : Nat := 2676831648240858412937845

theorem tailTrace_5213111 : CollatzResearch.WordTrace tailWord_5213111 prefixEnd_5213111 2676831648240858412937845 := by
  unfold tailWord_5213111
  simp only [CollatzResearch.WordTrace]
  refine ⟨190137778616796650321239187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126758519077864433547492791 190137778616796650321239187)
  ·
    refine ⟨285206667925194975481858781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190137778616796650321239187 285206667925194975481858781)
    ·
      refine ⟨106952500471948115805697043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285206667925194975481858781 106952500471948115805697043)
      ·
        refine ⟨160428750707922173708545565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106952500471948115805697043 160428750707922173708545565)
        ·
          refine ⟨60160781515470815140704587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160428750707922173708545565 60160781515470815140704587)
          ·
            refine ⟨90241172273206222711056881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60160781515470815140704587 90241172273206222711056881)
            ·
              refine ⟨67680879204904667033292661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90241172273206222711056881 67680879204904667033292661)
              ·
                refine ⟨6345082425459812534371187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67680879204904667033292661 6345082425459812534371187)
                ·
                  refine ⟨9517623638189718801556781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6345082425459812534371187 9517623638189718801556781)
                  ·
                    refine ⟨3569108864321144550583793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9517623638189718801556781 3569108864321144550583793)
                    ·
                      refine ⟨2676831648240858412937845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3569108864321144550583793 2676831648240858412937845)
                      ·
                        rfl

theorem cell23_5213111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 3, 2].length) (baseStart_5213111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213111 prefixEnd_5213111 := by exact prefixLift 5213111
  have htrace : WordTrace (prefixWord ++ tailWord_5213111) baseStart_5213111 baseEnd_5213111 := by
    simpa [prefixWord, tailWord_5213111, baseEnd_5213111] using wordTrace_append hprefix tailTrace_5213111
  have hstable : (prefixWord ++ tailWord_5213111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213111).length < 2 ^ (prefixWord ++ tailWord_5213111).sum := by decide
  have hdescent : baseEnd_5213111 < baseStart_5213111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213118 : List Nat := [4, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3]
def baseStart_5213118 : Nat := 118140960795 + 5213118 * 2 ^ 59
def prefixEnd_5213118 : Nat := 4983230072969 + 3 ^ 40 * 5213118 * 2
def baseEnd_5213118 : Nat := 2676835242605439885550313

theorem tailTrace_5213118 : CollatzResearch.WordTrace tailWord_5213118 prefixEnd_5213118 2676835242605439885550313 := by
  unfold tailWord_5213118
  simp only [CollatzResearch.WordTrace]
  refine ⟨23767254240971411314593001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126758689285180860344496005 23767254240971411314593001)
  ·
    refine ⟨17825440680728558485944751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23767254240971411314593001 17825440680728558485944751)
    ·
      refine ⟨26738161021092837728917127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17825440680728558485944751 26738161021092837728917127)
      ·
        refine ⟨40107241531639256593375691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26738161021092837728917127 40107241531639256593375691)
        ·
          refine ⟨60160862297458884890063537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40107241531639256593375691 60160862297458884890063537)
          ·
            refine ⟨45120646723094163667547653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60160862297458884890063537 45120646723094163667547653)
            ·
              refine ⟨8460121260580155687665185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45120646723094163667547653 8460121260580155687665185)
              ·
                refine ⟨6345090945435116765748889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8460121260580155687665185 6345090945435116765748889)
                ·
                  refine ⟨4758818209076337574311667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6345090945435116765748889 4758818209076337574311667)
                  ·
                    refine ⟨7138227313614506361467501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4758818209076337574311667 7138227313614506361467501)
                    ·
                      refine ⟨2676835242605439885550313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7138227313614506361467501 2676835242605439885550313)
                      ·
                        rfl

theorem cell23_5213118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_5213118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213118 prefixEnd_5213118 := by exact prefixLift 5213118
  have htrace : WordTrace (prefixWord ++ tailWord_5213118) baseStart_5213118 baseEnd_5213118 := by
    simpa [prefixWord, tailWord_5213118, baseEnd_5213118] using wordTrace_append hprefix tailTrace_5213118
  have hstable : (prefixWord ++ tailWord_5213118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213118).length < 2 ^ (prefixWord ++ tailWord_5213118).sum := by decide
  have hdescent : baseEnd_5213118 < baseStart_5213118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213127 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 5]
def baseStart_5213127 : Nat := 118140960795 + 5213127 * 2 ^ 59
def prefixEnd_5213127 : Nat := 4983230072969 + 3 ^ 40 * 5213127 * 2
def baseEnd_5213127 : Nat := 2676839863931330350337771

theorem tailTrace_5213127 : CollatzResearch.WordTrace tailWord_5213127 prefixEnd_5213127 2676839863931330350337771 := by
  unfold tailWord_5213127
  simp only [CollatzResearch.WordTrace]
  refine ⟨190138362184738685053821635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126758908123159123369214423 190138362184738685053821635)
  ·
    refine ⟨285207543277108027580732453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190138362184738685053821635 285207543277108027580732453)
    ·
      refine ⟨53476414364457755171387335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 285207543277108027580732453 53476414364457755171387335)
      ·
        refine ⟨80214621546686632757081003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53476414364457755171387335 80214621546686632757081003)
        ·
          refine ⟨120321932320029949135621505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80214621546686632757081003 120321932320029949135621505)
          ·
            refine ⟨90241449240022461851716129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120321932320029949135621505 90241449240022461851716129)
            ·
              refine ⟨67681086930016846388787097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90241449240022461851716129 67681086930016846388787097)
              ·
                refine ⟨50760815197512634791590323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67681086930016846388787097 50760815197512634791590323)
                ·
                  refine ⟨76141222796268952187385485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50760815197512634791590323 76141222796268952187385485)
                  ·
                    refine ⟨28552958548600857070269557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76141222796268952187385485 28552958548600857070269557)
                    ·
                      refine ⟨2676839863931330350337771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28552958548600857070269557 2676839863931330350337771)
                      ·
                        rfl

theorem cell23_5213127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_5213127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213127 prefixEnd_5213127 := by exact prefixLift 5213127
  have htrace : WordTrace (prefixWord ++ tailWord_5213127) baseStart_5213127 baseEnd_5213127 := by
    simpa [prefixWord, tailWord_5213127, baseEnd_5213127] using wordTrace_append hprefix tailTrace_5213127
  have hstable : (prefixWord ++ tailWord_5213127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213127).length < 2 ^ (prefixWord ++ tailWord_5213127).sum := by decide
  have hdescent : baseEnd_5213127 < baseStart_5213127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213134 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 2, 6]
def baseStart_5213134 : Nat := 118140960795 + 5213134 * 2 ^ 59
def prefixEnd_5213134 : Nat := 4983230072969 + 3 ^ 40 * 5213134 * 2
def baseEnd_5213134 : Nat := 892281152765303940983413

theorem tailTrace_5213134 : CollatzResearch.WordTrace tailWord_5213134 prefixEnd_5213134 892281152765303940983413 := by
  unfold tailWord_5213134
  simp only [CollatzResearch.WordTrace]
  refine ⟨23767327186964165656165807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126759078330475550166217637 23767327186964165656165807)
  ·
    refine ⟨35650990780446248484248711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23767327186964165656165807 35650990780446248484248711)
    ·
      refine ⟨53476486170669372726373067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35650990780446248484248711 53476486170669372726373067)
      ·
        refine ⟨80214729256004059089559601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53476486170669372726373067 80214729256004059089559601)
        ·
          refine ⟨60161046942003044317169701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80214729256004059089559601 60161046942003044317169701)
          ·
            refine ⟨11280196301625570809469319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60161046942003044317169701 11280196301625570809469319)
            ·
              refine ⟨16920294452438356214203979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11280196301625570809469319 16920294452438356214203979)
              ·
                refine ⟨25380441678657534321305969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16920294452438356214203979 25380441678657534321305969)
                ·
                  refine ⟨19035331258993150740979477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25380441678657534321305969 19035331258993150740979477)
                  ·
                    refine ⟨892281152765303940983413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19035331258993150740979477 892281152765303940983413)
                    ·
                      rfl

theorem cell23_5213134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_5213134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213134 prefixEnd_5213134 := by exact prefixLift 5213134
  have htrace : WordTrace (prefixWord ++ tailWord_5213134) baseStart_5213134 baseEnd_5213134 := by
    simpa [prefixWord, tailWord_5213134, baseEnd_5213134] using wordTrace_append hprefix tailTrace_5213134
  have hstable : (prefixWord ++ tailWord_5213134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213134).length < 2 ^ (prefixWord ++ tailWord_5213134).sum := by decide
  have hdescent : baseEnd_5213134 < baseStart_5213134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213194 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 1, 7]
def baseStart_5213194 : Nat := 118140960795 + 5213194 * 2 ^ 59
def prefixEnd_5213194 : Nat := 4983230072969 + 3 ^ 40 * 5213194 * 2
def baseEnd_5213194 : Nat := 892291422378393862733321

theorem tailTrace_5213194 : CollatzResearch.WordTrace tailWord_5213194 prefixEnd_5213194 892291422378393862733321 := by
  unfold tailWord_5213194
  simp only [CollatzResearch.WordTrace]
  refine ⟨47535201468873988874127659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126760537250330636997673757 47535201468873988874127659)
  ·
    refine ⟨71302802203310983311191489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47535201468873988874127659 71302802203310983311191489)
    ·
      refine ⟨53477101652483237483393617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71302802203310983311191489 53477101652483237483393617)
      ·
        refine ⟨40107826239362428112545213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53477101652483237483393617 40107826239362428112545213)
        ·
          refine ⟨15040434839760910542204455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40107826239362428112545213 15040434839760910542204455)
          ·
            refine ⟨22560652259641365813306683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15040434839760910542204455 22560652259641365813306683)
            ·
              refine ⟨33840978389462048719960025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22560652259641365813306683 33840978389462048719960025)
              ·
                refine ⟨25380733792096536539970019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33840978389462048719960025 25380733792096536539970019)
                ·
                  refine ⟨38071100688144804809955029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25380733792096536539970019 38071100688144804809955029)
                  ·
                    refine ⟨892291422378393862733321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38071100688144804809955029 892291422378393862733321)
                    ·
                      rfl

theorem cell23_5213194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_5213194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213194 prefixEnd_5213194 := by exact prefixLift 5213194
  have htrace : WordTrace (prefixWord ++ tailWord_5213194) baseStart_5213194 baseEnd_5213194 := by
    simpa [prefixWord, tailWord_5213194, baseEnd_5213194] using wordTrace_append hprefix tailTrace_5213194
  have hstable : (prefixWord ++ tailWord_5213194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213194).length < 2 ^ (prefixWord ++ tailWord_5213194).sum := by decide
  have hdescent : baseEnd_5213194 < baseStart_5213194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213264 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 3]
def baseStart_5213264 : Nat := 118140960795 + 5213264 * 2 ^ 59
def prefixEnd_5213264 : Nat := 4983230072969 + 3 ^ 40 * 5213264 * 2
def baseEnd_5213264 : Nat := 2676910210780996314324641

theorem tailTrace_5213264 : CollatzResearch.WordTrace tailWord_5213264 prefixEnd_5213264 2676910210780996314324641 := by
  unfold tailWord_5213264
  simp only [CollatzResearch.WordTrace]
  refine ⟨95071679492621178725779423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126762239323494904967705897 95071679492621178725779423)
  ·
    refine ⟨142607519238931768088669135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95071679492621178725779423 142607519238931768088669135)
    ·
      refine ⟨213911278858397652133003703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142607519238931768088669135 213911278858397652133003703)
      ·
        refine ⟨320866918287596478199505555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213911278858397652133003703 320866918287596478199505555)
        ·
          refine ⟨481300377431394717299258333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320866918287596478199505555 481300377431394717299258333)
          ·
            refine ⟨180487641536773018987221875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 481300377431394717299258333 180487641536773018987221875)
            ·
              refine ⟨270731462305159528480832813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180487641536773018987221875 270731462305159528480832813)
              ·
                refine ⟨101524298364434823180312305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 270731462305159528480832813 101524298364434823180312305)
                ·
                  refine ⟨76143223773326117385234229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101524298364434823180312305 76143223773326117385234229)
                  ·
                    refine ⟨7138427228749323504865709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76143223773326117385234229 7138427228749323504865709)
                    ·
                      refine ⟨2676910210780996314324641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7138427228749323504865709 2676910210780996314324641)
                      ·
                        rfl

theorem cell23_5213264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 3].length) (baseStart_5213264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213264 prefixEnd_5213264 := by exact prefixLift 5213264
  have htrace : WordTrace (prefixWord ++ tailWord_5213264) baseStart_5213264 baseEnd_5213264 := by
    simpa [prefixWord, tailWord_5213264, baseEnd_5213264] using wordTrace_append hprefix tailTrace_5213264
  have hstable : (prefixWord ++ tailWord_5213264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213264).length < 2 ^ (prefixWord ++ tailWord_5213264).sum := by decide
  have hdescent : baseEnd_5213264 < baseStart_5213264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213298 : List Nat := [3, 2, 1, 2, 2, 1, 2, 3, 3, 1, 3]
def baseStart_5213298 : Nat := 118140960795 + 5213298 * 2 ^ 59
def prefixEnd_5213298 : Nat := 4983230072969 + 3 ^ 40 * 5213298 * 2
def baseEnd_5213298 : Nat := 2676927669123249181299485

theorem tailTrace_5213298 : CollatzResearch.WordTrace tailWord_5213298 prefixEnd_5213298 2676927669123249181299485 := by
  unfold tailWord_5213298
  simp only [CollatzResearch.WordTrace]
  refine ⟨47536149766779795314574137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126763066044746120838864365 47536149766779795314574137)
  ·
    refine ⟨35652112325084846485930603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47536149766779795314574137 35652112325084846485930603)
    ·
      refine ⟨53478168487627269728895905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35652112325084846485930603 53478168487627269728895905)
      ·
        refine ⟨40108626365720452296671929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53478168487627269728895905 40108626365720452296671929)
        ·
          refine ⟨30081469774290339222503947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40108626365720452296671929 30081469774290339222503947)
          ·
            refine ⟨45122204661435508833755921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30081469774290339222503947 45122204661435508833755921)
            ·
              refine ⟨33841653496076631625316941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45122204661435508833755921 33841653496076631625316941)
              ·
                refine ⟨12690620061028736859493853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33841653496076631625316941 12690620061028736859493853)
                ·
                  refine ⟨4758982522885776322310195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12690620061028736859493853 4758982522885776322310195)
                  ·
                    refine ⟨7138473784328664483465293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4758982522885776322310195 7138473784328664483465293)
                    ·
                      refine ⟨2676927669123249181299485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7138473784328664483465293 2676927669123249181299485)
                      ·
                        rfl

theorem cell23_5213298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_5213298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213298 prefixEnd_5213298 := by exact prefixLift 5213298
  have htrace : WordTrace (prefixWord ++ tailWord_5213298) baseStart_5213298 baseEnd_5213298 := by
    simpa [prefixWord, tailWord_5213298, baseEnd_5213298] using wordTrace_append hprefix tailTrace_5213298
  have hstable : (prefixWord ++ tailWord_5213298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213298).length < 2 ^ (prefixWord ++ tailWord_5213298).sum := by decide
  have hdescent : baseEnd_5213298 < baseStart_5213298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213321 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 3, 1, 4]
def baseStart_5213321 : Nat := 118140960795 + 5213321 * 2 ^ 59
def prefixEnd_5213321 : Nat := 4983230072969 + 3 ^ 40 * 5213321 * 2
def baseEnd_5213321 : Nat := 2676939479178302591311879

theorem tailTrace_5213321 : CollatzResearch.WordTrace tailWord_5213321 prefixEnd_5213321 2676939479178302591311879 := by
  unfold tailWord_5213321
  simp only [CollatzResearch.WordTrace]
  refine ⟨190145437946035856186383817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126763625297357237457589211 190145437946035856186383817)
  ·
    refine ⟨142609078459526892139787863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190145437946035856186383817 142609078459526892139787863)
    ·
      refine ⟨213913617689290338209681795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142609078459526892139787863 213913617689290338209681795)
      ·
        refine ⟨320870426533935507314522693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213913617689290338209681795 320870426533935507314522693)
        ·
          refine ⟨60163204975112907621473005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 320870426533935507314522693 60163204975112907621473005)
          ·
            refine ⟨22561201865667340358052377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60163204975112907621473005 22561201865667340358052377)
            ·
              refine ⟨16920901399250505268539283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22561201865667340358052377 16920901399250505268539283)
              ·
                refine ⟨25381352098875757902808925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16920901399250505268539283 25381352098875757902808925)
                ·
                  refine ⟨9518007037078409213553347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25381352098875757902808925 9518007037078409213553347)
                  ·
                    refine ⟨14277010555617613820330021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9518007037078409213553347 14277010555617613820330021)
                    ·
                      refine ⟨2676939479178302591311879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14277010555617613820330021 2676939479178302591311879)
                      ·
                        rfl

theorem cell23_5213321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 1, 4].length) (baseStart_5213321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213321 prefixEnd_5213321 := by exact prefixLift 5213321
  have htrace : WordTrace (prefixWord ++ tailWord_5213321) baseStart_5213321 baseEnd_5213321 := by
    simpa [prefixWord, tailWord_5213321, baseEnd_5213321] using wordTrace_append hprefix tailTrace_5213321
  have hstable : (prefixWord ++ tailWord_5213321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213321).length < 2 ^ (prefixWord ++ tailWord_5213321).sum := by decide
  have hdescent : baseEnd_5213321 < baseStart_5213321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213335 : List Nat := [1, 1, 3, 3, 3, 3, 2, 1, 1, 5]
def baseStart_5213335 : Nat := 118140960795 + 5213335 * 2 ^ 59
def prefixEnd_5213335 : Nat := 4983230072969 + 3 ^ 40 * 5213335 * 2
def baseEnd_5213335 : Nat := 892315555969155178845605

theorem tailTrace_5213335 : CollatzResearch.WordTrace tailWord_5213335 prefixEnd_5213335 892315555969155178845605 := by
  unfold tailWord_5213335
  simp only [CollatzResearch.WordTrace]
  refine ⟨190145948567985136577393459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126763965711990091051595639 190145948567985136577393459)
  ·
    refine ⟨285218922851977704866090189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190145948567985136577393459 285218922851977704866090189)
    ·
      refine ⟨106957096069491639324783821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285218922851977704866090189 106957096069491639324783821)
      ·
        refine ⟨40108911026059364746793933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106957096069491639324783821 40108911026059364746793933)
        ·
          refine ⟨15040841634772261780047725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40108911026059364746793933 15040841634772261780047725)
          ·
            refine ⟨5640315613039598167517897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15040841634772261780047725 5640315613039598167517897)
            ·
              refine ⟨4230236709779698625638423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5640315613039598167517897 4230236709779698625638423)
              ·
                refine ⟨6345355064669547938457635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4230236709779698625638423 6345355064669547938457635)
                ·
                  refine ⟨9518032597004321907686453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6345355064669547938457635 9518032597004321907686453)
                  ·
                    refine ⟨892315555969155178845605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9518032597004321907686453 892315555969155178845605)
                    ·
                      rfl

theorem cell23_5213335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 1, 5].length) (baseStart_5213335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213335 prefixEnd_5213335 := by exact prefixLift 5213335
  have htrace : WordTrace (prefixWord ++ tailWord_5213335) baseStart_5213335 baseEnd_5213335 := by
    simpa [prefixWord, tailWord_5213335, baseEnd_5213335] using wordTrace_append hprefix tailTrace_5213335
  have hstable : (prefixWord ++ tailWord_5213335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213335).length < 2 ^ (prefixWord ++ tailWord_5213335).sum := by decide
  have hdescent : baseEnd_5213335 < baseStart_5213335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213341 : List Nat := [1, 4, 2, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_5213341 : Nat := 118140960795 + 5213341 * 2 ^ 59
def prefixEnd_5213341 : Nat := 4983230072969 + 3 ^ 40 * 5213341 * 2
def baseEnd_5213341 : Nat := 2676949748791392513061787

theorem tailTrace_5213341 : CollatzResearch.WordTrace tailWord_5213341 prefixEnd_5213341 2676949748791392513061787 := by
  unfold tailWord_5213341
  simp only [CollatzResearch.WordTrace]
  refine ⟨190146167405963399602111877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126764111603975599734741251 190146167405963399602111877)
  ·
    refine ⟨35652406388618137425395977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190146167405963399602111877 35652406388618137425395977)
    ·
      refine ⟨26739304791463603069046983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35652406388618137425395977 26739304791463603069046983)
      ·
        refine ⟨40108957187195404603570475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26739304791463603069046983 40108957187195404603570475)
        ·
          refine ⟨60163435780793106905355713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40108957187195404603570475 60163435780793106905355713)
          ·
            refine ⟨45122576835594830179016785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60163435780793106905355713 45122576835594830179016785)
            ·
              refine ⟨33841932626696122634262589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45122576835594830179016785 33841932626696122634262589)
              ·
                refine ⟨12690724735011045987848471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33841932626696122634262589 12690724735011045987848471)
                ·
                  refine ⟨19036087102516568981772707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12690724735011045987848471 19036087102516568981772707)
                  ·
                    refine ⟨28554130653774853472659061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19036087102516568981772707 28554130653774853472659061)
                    ·
                      refine ⟨2676949748791392513061787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28554130653774853472659061 2676949748791392513061787)
                      ·
                        rfl

theorem cell23_5213341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_5213341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213341 prefixEnd_5213341 := by exact prefixLift 5213341
  have htrace : WordTrace (prefixWord ++ tailWord_5213341) baseStart_5213341 baseEnd_5213341 := by
    simpa [prefixWord, tailWord_5213341, baseEnd_5213341] using wordTrace_append hprefix tailTrace_5213341
  have hstable : (prefixWord ++ tailWord_5213341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213341).length < 2 ^ (prefixWord ++ tailWord_5213341).sum := by decide
  have hdescent : baseEnd_5213341 < baseStart_5213341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213344 : List Nat := [2, 1, 1, 4, 2, 1, 12]
def baseStart_5213344 : Nat := 118140960795 + 5213344 * 2 ^ 59
def prefixEnd_5213344 : Nat := 4983230072969 + 3 ^ 40 * 5213344 * 2
def baseEnd_5213344 : Nat := 33048781348559950633633

theorem tailTrace_5213344 : CollatzResearch.WordTrace tailWord_5213344 prefixEnd_5213344 33048781348559950633633 := by
  unfold tailWord_5213344
  simp only [CollatzResearch.WordTrace]
  refine ⟨95073138412476265557235543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126764184549968354076314057 95073138412476265557235543)
  ·
    refine ⟨142609707618714398335853315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95073138412476265557235543 142609707618714398335853315)
    ·
      refine ⟨213914561428071597503779973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142609707618714398335853315 213914561428071597503779973)
      ·
        refine ⟨40108980267763424531958745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213914561428071597503779973 40108980267763424531958745)
        ·
          refine ⟨30081735200822568398969059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40108980267763424531958745 30081735200822568398969059)
          ·
            refine ⟨45122602801233852598453589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30081735200822568398969059 45122602801233852598453589)
            ·
              refine ⟨33048781348559950633633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 45122602801233852598453589 33048781348559950633633)
              ·
                rfl

theorem cell23_5213344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 12].length) (baseStart_5213344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213344 prefixEnd_5213344 := by exact prefixLift 5213344
  have htrace : WordTrace (prefixWord ++ tailWord_5213344) baseStart_5213344 baseEnd_5213344 := by
    simpa [prefixWord, tailWord_5213344, baseEnd_5213344] using wordTrace_append hprefix tailTrace_5213344
  have hstable : (prefixWord ++ tailWord_5213344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213344).length < 2 ^ (prefixWord ++ tailWord_5213344).sum := by decide
  have hdescent : baseEnd_5213344 < baseStart_5213344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213348 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 4, 4]
def baseStart_5213348 : Nat := 118140960795 + 5213348 * 2 ^ 59
def prefixEnd_5213348 : Nat := 4983230072969 + 3 ^ 40 * 5213348 * 2
def baseEnd_5213348 : Nat := 892317781051991328558085

theorem tailTrace_5213348 : CollatzResearch.WordTrace tailWord_5213348 prefixEnd_5213348 892317781051991328558085 := by
  unfold tailWord_5213348
  simp only [CollatzResearch.WordTrace]
  refine ⟨95073211358469019898808349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126764281811292026531744465 95073211358469019898808349)
  ·
    refine ⟨35652454259425882462053131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95073211358469019898808349 35652454259425882462053131)
    ·
      refine ⟨53478681389138823693079697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35652454259425882462053131 53478681389138823693079697)
      ·
        refine ⟨40109011041854117769809773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53478681389138823693079697 40109011041854117769809773)
        ·
          refine ⟨15040879140695294163678665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40109011041854117769809773 15040879140695294163678665)
          ·
            refine ⟨11280659355521470622758999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15040879140695294163678665 11280659355521470622758999)
            ·
              refine ⟨16920989033282205934138499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11280659355521470622758999 16920989033282205934138499)
              ·
                refine ⟨25381483549923308901207749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16920989033282205934138499 25381483549923308901207749)
                ·
                  refine ⟨4759028165610620418976453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25381483549923308901207749 4759028165610620418976453)
                  ·
                    refine ⟨892317781051991328558085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4759028165610620418976453 892317781051991328558085)
                    ·
                      rfl

theorem cell23_5213348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_5213348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213348 prefixEnd_5213348 := by exact prefixLift 5213348
  have htrace : WordTrace (prefixWord ++ tailWord_5213348) baseStart_5213348 baseEnd_5213348 := by
    simpa [prefixWord, tailWord_5213348, baseEnd_5213348] using wordTrace_append hprefix tailTrace_5213348
  have hstable : (prefixWord ++ tailWord_5213348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213348).length < 2 ^ (prefixWord ++ tailWord_5213348).sum := by decide
  have hdescent : baseEnd_5213348 < baseStart_5213348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213371 : List Nat := [1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 3]
def baseStart_5213371 : Nat := 118140960795 + 5213371 * 2 ^ 59
def prefixEnd_5213371 : Nat := 4983230072969 + 3 ^ 40 * 5213371 * 2
def baseEnd_5213371 : Nat := 2676965153211027395686649

theorem tailTrace_5213371 : CollatzResearch.WordTrace tailWord_5213371 prefixEnd_5213371 2676965153211027395686649 := by
  unfold tailWord_5213371
  simp only [CollatzResearch.WordTrace]
  refine ⟨190147261595854714725703967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126764841063903143150469311 190147261595854714725703967)
  ·
    refine ⟨285220892393782072088555951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190147261595854714725703967 285220892393782072088555951)
    ·
      refine ⟨427831338590673108132833927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285220892393782072088555951 427831338590673108132833927)
      ·
        refine ⟨641747007886009662199250891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427831338590673108132833927 641747007886009662199250891)
        ·
          refine ⟨962620511829014493298876337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 641747007886009662199250891 962620511829014493298876337)
          ·
            refine ⟨721965383871760869974157253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 962620511829014493298876337 721965383871760869974157253)
            ·
              refine ⟨135368509475955163120154485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 721965383871760869974157253 135368509475955163120154485)
              ·
                refine ⟨12690797763370796542514483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135368509475955163120154485 12690797763370796542514483)
                ·
                  refine ⟨19036196645056194813771725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12690797763370796542514483 19036196645056194813771725)
                  ·
                    refine ⟨7138573741896073055164397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19036196645056194813771725 7138573741896073055164397)
                    ·
                      refine ⟨2676965153211027395686649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7138573741896073055164397 2676965153211027395686649)
                      ·
                        rfl

theorem cell23_5213371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 3].length) (baseStart_5213371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213371 prefixEnd_5213371 := by exact prefixLift 5213371
  have htrace : WordTrace (prefixWord ++ tailWord_5213371) baseStart_5213371 baseEnd_5213371 := by
    simpa [prefixWord, tailWord_5213371, baseEnd_5213371] using wordTrace_append hprefix tailTrace_5213371
  have hstable : (prefixWord ++ tailWord_5213371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213371).length < 2 ^ (prefixWord ++ tailWord_5213371).sum := by decide
  have hdescent : baseEnd_5213371 < baseStart_5213371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213422 : List Nat := [4, 1, 2, 1, 1, 1, 6, 1, 2, 1, 3]
def baseStart_5213422 : Nat := 118140960795 + 5213422 * 2 ^ 59
def prefixEnd_5213422 : Nat := 4983230072969 + 3 ^ 40 * 5213422 * 2
def baseEnd_5213422 : Nat := 2676991340724406696148915

theorem tailTrace_5213422 : CollatzResearch.WordTrace tailWord_5213422 prefixEnd_5213422 2676991340724406696148915 := by
  unfold tailWord_5213422
  simp only [CollatzResearch.WordTrace]
  refine ⟨23768640214833743804476315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126766081145779966957207013 23768640214833743804476315)
  ·
    refine ⟨35652960322250615706714473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23768640214833743804476315 35652960322250615706714473)
    ·
      refine ⟨26739720241687961780035855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35652960322250615706714473 26739720241687961780035855)
      ·
        refine ⟨40109580362531942670053783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26739720241687961780035855 40109580362531942670053783)
        ·
          refine ⟨60164370543797914005080675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40109580362531942670053783 60164370543797914005080675)
          ·
            refine ⟨90246555815696871007621013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60164370543797914005080675 90246555815696871007621013)
            ·
              refine ⟨4230307303860790828482235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90246555815696871007621013 4230307303860790828482235)
              ·
                refine ⟨6345460955791186242723353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4230307303860790828482235 6345460955791186242723353)
                ·
                  refine ⟨4759095716843389682042515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6345460955791186242723353 4759095716843389682042515)
                  ·
                    refine ⟨7138643575265084523063773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4759095716843389682042515 7138643575265084523063773)
                    ·
                      refine ⟨2676991340724406696148915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7138643575265084523063773 2676991340724406696148915)
                      ·
                        rfl

theorem cell23_5213422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_5213422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213422 prefixEnd_5213422 := by exact prefixLift 5213422
  have htrace : WordTrace (prefixWord ++ tailWord_5213422) baseStart_5213422 baseEnd_5213422 := by
    simpa [prefixWord, tailWord_5213422, baseEnd_5213422] using wordTrace_append hprefix tailTrace_5213422
  have hstable : (prefixWord ++ tailWord_5213422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213422).length < 2 ^ (prefixWord ++ tailWord_5213422).sum := by decide
  have hdescent : baseEnd_5213422 < baseStart_5213422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213431 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 3]
def baseStart_5213431 : Nat := 118140960795 + 5213431 * 2 ^ 59
def prefixEnd_5213431 : Nat := 4983230072969 + 3 ^ 40 * 5213431 * 2
def baseEnd_5213431 : Nat := 2676995962050297160936373

theorem tailTrace_5213431 : CollatzResearch.WordTrace tailWord_5213431 prefixEnd_5213431 2676995962050297160936373 := by
  unfold tailWord_5213431
  simp only [CollatzResearch.WordTrace]
  refine ⟨190149449975637344972888147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126766299983758229981925431 190149449975637344972888147)
  ·
    refine ⟨285224174963456017459332221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190149449975637344972888147 285224174963456017459332221)
    ·
      refine ⟨106959065611296006547249583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285224174963456017459332221 106959065611296006547249583)
      ·
        refine ⟨160438598416944009820874375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106959065611296006547249583 160438598416944009820874375)
        ·
          refine ⟨240657897625416014731311563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160438598416944009820874375 240657897625416014731311563)
          ·
            refine ⟨360986846438124022096967345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240657897625416014731311563 360986846438124022096967345)
            ·
              refine ⟨270740134828593016572725509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360986846438124022096967345 270740134828593016572725509)
              ·
                refine ⟨50763775280361190607386033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 270740134828593016572725509 50763775280361190607386033)
                ·
                  refine ⟨38072831460270892955539525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50763775280361190607386033 38072831460270892955539525)
                  ·
                    refine ⟨7138655898800792429163661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38072831460270892955539525 7138655898800792429163661)
                    ·
                      refine ⟨2676995962050297160936373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7138655898800792429163661 2676995962050297160936373)
                      ·
                        rfl

theorem cell23_5213431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 3].length) (baseStart_5213431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213431 prefixEnd_5213431 := by exact prefixLift 5213431
  have htrace : WordTrace (prefixWord ++ tailWord_5213431) baseStart_5213431 baseEnd_5213431 := by
    simpa [prefixWord, tailWord_5213431, baseEnd_5213431] using wordTrace_append hprefix tailTrace_5213431
  have hstable : (prefixWord ++ tailWord_5213431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213431).length < 2 ^ (prefixWord ++ tailWord_5213431).sum := by decide
  have hdescent : baseEnd_5213431 < baseStart_5213431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213485 : List Nat := [1, 5, 3, 1, 1, 2, 1, 2, 7]
def baseStart_5213485 : Nat := 118140960795 + 5213485 * 2 ^ 59
def prefixEnd_5213485 : Nat := 4983230072969 + 3 ^ 40 * 5213485 * 2
def baseEnd_5213485 : Nat := 297447076667293327740125

theorem tailTrace_5213485 : CollatzResearch.WordTrace tailWord_5213485 prefixEnd_5213485 297447076667293327740125 := by
  unfold tailWord_5213485
  simp only [CollatzResearch.WordTrace]
  refine ⟨190151419517441712195353909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126767613011627808130235939 190151419517441712195353909)
  ·
    refine ⟨17826695579760160518314429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 190151419517441712195353909 17826695579760160518314429)
    ·
      refine ⟨6685010842410060194367911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17826695579760160518314429 6685010842410060194367911)
      ·
        refine ⟨10027516263615090291551867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6685010842410060194367911 10027516263615090291551867)
        ·
          refine ⟨15041274395422635437327801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10027516263615090291551867 15041274395422635437327801)
          ·
            refine ⟨11280955796566976577995851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15041274395422635437327801 11280955796566976577995851)
            ·
              refine ⟨16921433694850464866993777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11280955796566976577995851 16921433694850464866993777)
              ·
                refine ⟨12691075271137848650245333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16921433694850464866993777 12691075271137848650245333)
                ·
                  refine ⟨297447076667293327740125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12691075271137848650245333 297447076667293327740125)
                  ·
                    rfl

theorem cell23_5213485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_5213485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213485 prefixEnd_5213485 := by exact prefixLift 5213485
  have htrace : WordTrace (prefixWord ++ tailWord_5213485) baseStart_5213485 baseEnd_5213485 := by
    simpa [prefixWord, tailWord_5213485, baseEnd_5213485] using wordTrace_append hprefix tailTrace_5213485
  have hstable : (prefixWord ++ tailWord_5213485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213485).length < 2 ^ (prefixWord ++ tailWord_5213485).sum := by decide
  have hdescent : baseEnd_5213485 < baseStart_5213485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213488 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 2, 5, 2]
def baseStart_5213488 : Nat := 118140960795 + 5213488 * 2 ^ 59
def prefixEnd_5213488 : Nat := 4983230072969 + 3 ^ 40 * 5213488 * 2
def baseEnd_5213488 : Nat := 2677025230447603437923611

theorem tailTrace_5213488 : CollatzResearch.WordTrace tailWord_5213488 prefixEnd_5213488 2677025230447603437923611 := by
  unfold tailWord_5213488
  simp only [CollatzResearch.WordTrace]
  refine ⟨95075764468215421853856559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126767685957620562471808745 95075764468215421853856559)
  ·
    refine ⟨142613646702323132780784839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95075764468215421853856559 142613646702323132780784839)
    ·
      refine ⟨213920470053484699171177259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142613646702323132780784839 213920470053484699171177259)
      ·
        refine ⟨320880705080227048756765889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213920470053484699171177259 320880705080227048756765889)
        ·
          refine ⟨240660528810170286567574417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320880705080227048756765889 240660528810170286567574417)
          ·
            refine ⟨180495396607627714925680813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240660528810170286567574417 180495396607627714925680813)
            ·
              refine ⟨67685773727860393097130305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180495396607627714925680813 67685773727860393097130305)
              ·
                refine ⟨50764330295895294822847729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67685773727860393097130305 50764330295895294822847729)
                ·
                  refine ⟨38073247721921471117135797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50764330295895294822847729 38073247721921471117135797)
                  ·
                    refine ⟨3569366973930137917231481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38073247721921471117135797 3569366973930137917231481)
                    ·
                      refine ⟨2677025230447603437923611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3569366973930137917231481 2677025230447603437923611)
                      ·
                        rfl

theorem cell23_5213488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 2, 5, 2].length) (baseStart_5213488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213488 prefixEnd_5213488 := by exact prefixLift 5213488
  have htrace : WordTrace (prefixWord ++ tailWord_5213488) baseStart_5213488 baseEnd_5213488 := by
    simpa [prefixWord, tailWord_5213488, baseEnd_5213488] using wordTrace_append hprefix tailTrace_5213488
  have hstable : (prefixWord ++ tailWord_5213488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213488).length < 2 ^ (prefixWord ++ tailWord_5213488).sum := by decide
  have hdescent : baseEnd_5213488 < baseStart_5213488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213518 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4]
def baseStart_5213518 : Nat := 118140960795 + 5213518 * 2 ^ 59
def prefixEnd_5213518 : Nat := 4983230072969 + 3 ^ 40 * 5213518 * 2
def baseEnd_5213518 : Nat := 2677040634867238320548473

theorem tailTrace_5213518 : CollatzResearch.WordTrace tailWord_5213518 prefixEnd_5213518 2677040634867238320548473 := by
  unfold tailWord_5213518
  simp only [CollatzResearch.WordTrace]
  refine ⟨23769077890790269853913151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126768415417548105887536805 23769077890790269853913151)
  ·
    refine ⟨35653616836185404780869727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23769077890790269853913151 35653616836185404780869727)
    ·
      refine ⟨53480425254278107171304591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35653616836185404780869727 53480425254278107171304591)
      ·
        refine ⟨80220637881417160756956887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53480425254278107171304591 80220637881417160756956887)
        ·
          refine ⟨120330956822125741135435331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80220637881417160756956887 120330956822125741135435331)
          ·
            refine ⟨180496435233188611703152997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120330956822125741135435331 180496435233188611703152997)
            ·
              refine ⟨33843081606222864694341187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 180496435233188611703152997 33843081606222864694341187)
              ·
                refine ⟨50764622409334297041511781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33843081606222864694341187 50764622409334297041511781)
                ·
                  refine ⟨9518366701750180695283459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50764622409334297041511781 9518366701750180695283459)
                  ·
                    refine ⟨14277550052625271042925189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9518366701750180695283459 14277550052625271042925189)
                    ·
                      refine ⟨2677040634867238320548473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14277550052625271042925189 2677040634867238320548473)
                      ·
                        rfl

theorem cell23_5213518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_5213518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213518 prefixEnd_5213518 := by exact prefixLift 5213518
  have htrace : WordTrace (prefixWord ++ tailWord_5213518) baseStart_5213518 baseEnd_5213518 := by
    simpa [prefixWord, tailWord_5213518, baseEnd_5213518] using wordTrace_append hprefix tailTrace_5213518
  have hstable : (prefixWord ++ tailWord_5213518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213518).length < 2 ^ (prefixWord ++ tailWord_5213518).sum := by decide
  have hdescent : baseEnd_5213518 < baseStart_5213518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213635 : List Nat := [1, 1, 1, 3, 1, 1, 5, 4, 2, 4]
def baseStart_5213635 : Nat := 118140960795 + 5213635 * 2 ^ 59
def prefixEnd_5213635 : Nat := 4983230072969 + 3 ^ 40 * 5213635 * 2
def baseEnd_5213635 : Nat := 892366904034604787595145

theorem tailTrace_5213635 : CollatzResearch.WordTrace tailWord_5213635 prefixEnd_5213635 892366904034604787595145 := by
  unfold tailWord_5213635
  simp only [CollatzResearch.WordTrace]
  refine ⟨190156890466898287813314359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126771260311265525208876239 190156890466898287813314359)
  ·
    refine ⟨285235335700347431719971539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190156890466898287813314359 285235335700347431719971539)
    ·
      refine ⟨427853003550521147579957309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285235335700347431719971539 427853003550521147579957309)
      ·
        refine ⟨160444876331445430342483991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 427853003550521147579957309 160444876331445430342483991)
        ·
          refine ⟨240667314497168145513725987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160444876331445430342483991 240667314497168145513725987)
          ·
            refine ⟨361000971745752218270588981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240667314497168145513725987 361000971745752218270588981)
            ·
              refine ⟨33843841101164270462867717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 361000971745752218270588981 33843841101164270462867717)
              ·
                refine ⟨6345720206468300711787697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33843841101164270462867717 6345720206468300711787697)
                ·
                  refine ⟨4759290154851225533840773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6345720206468300711787697 4759290154851225533840773)
                  ·
                    refine ⟨892366904034604787595145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4759290154851225533840773 892366904034604787595145)
                    ·
                      rfl

theorem cell23_5213635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 4].length) (baseStart_5213635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213635 prefixEnd_5213635 := by exact prefixLift 5213635
  have htrace : WordTrace (prefixWord ++ tailWord_5213635) baseStart_5213635 baseEnd_5213635 := by
    simpa [prefixWord, tailWord_5213635, baseEnd_5213635] using wordTrace_append hprefix tailTrace_5213635
  have hstable : (prefixWord ++ tailWord_5213635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213635).length < 2 ^ (prefixWord ++ tailWord_5213635).sum := by decide
  have hdescent : baseEnd_5213635 < baseStart_5213635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213636 : List Nat := [2, 3, 3, 2, 1, 2, 1, 4, 1, 1, 3]
def baseStart_5213636 : Nat := 118140960795 + 5213636 * 2 ^ 59
def prefixEnd_5213636 : Nat := 4983230072969 + 3 ^ 40 * 5213636 * 2
def baseEnd_5213636 : Nat := 2677101225584468858872931

theorem tailTrace_5213636 : CollatzResearch.WordTrace tailWord_5213636 prefixEnd_5213636 2677101225584468858872931 := by
  unfold tailWord_5213636
  simp only [CollatzResearch.WordTrace]
  refine ⟨95078463469947332492050381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126771284626596443322733841 95078463469947332492050381)
  ·
    refine ⟨35654423801230249684518893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95078463469947332492050381 35654423801230249684518893)
    ·
      refine ⟨13370408925461343631694585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35654423801230249684518893 13370408925461343631694585)
      ·
        refine ⟨10027806694096007723770939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13370408925461343631694585 10027806694096007723770939)
        ·
          refine ⟨15041710041144011585656409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10027806694096007723770939 15041710041144011585656409)
          ·
            refine ⟨11281282530858008689242307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15041710041144011585656409 11281282530858008689242307)
            ·
              refine ⟨16921923796287013033863461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11281282530858008689242307 16921923796287013033863461)
              ·
                refine ⟨3172860711803814943849399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16921923796287013033863461 3172860711803814943849399)
                ·
                  refine ⟨4759291067705722415774099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3172860711803814943849399 4759291067705722415774099)
                  ·
                    refine ⟨7138936601558583623661149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4759291067705722415774099 7138936601558583623661149)
                    ·
                      refine ⟨2677101225584468858872931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7138936601558583623661149 2677101225584468858872931)
                      ·
                        rfl

theorem cell23_5213636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_5213636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213636 prefixEnd_5213636 := by exact prefixLift 5213636
  have htrace : WordTrace (prefixWord ++ tailWord_5213636) baseStart_5213636 baseEnd_5213636 := by
    simpa [prefixWord, tailWord_5213636, baseEnd_5213636] using wordTrace_append hprefix tailTrace_5213636
  have hstable : (prefixWord ++ tailWord_5213636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213636).length < 2 ^ (prefixWord ++ tailWord_5213636).sum := by decide
  have hdescent : baseEnd_5213636 < baseStart_5213636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213652 : List Nat := [2, 4, 1, 2, 3, 1, 2, 1, 1, 6]
def baseStart_5213652 : Nat := 118140960795 + 5213652 * 2 ^ 59
def prefixEnd_5213652 : Nat := 4983230072969 + 3 ^ 40 * 5213652 * 2
def baseEnd_5213652 : Nat := 892369813758313598757619

theorem tailTrace_5213652 : CollatzResearch.WordTrace tailWord_5213652 prefixEnd_5213652 892369813758313598757619 := by
  unfold tailWord_5213652
  simp only [CollatzResearch.WordTrace]
  refine ⟨95078755253918349858341605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126771673671891133144455473 95078755253918349858341605)
  ·
    refine ⟨17827266610109690598439051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95078755253918349858341605 17827266610109690598439051)
    ·
      refine ⟨26740899915164535897658577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17827266610109690598439051 26740899915164535897658577)
      ·
        refine ⟨20055674936373401923243933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26740899915164535897658577 20055674936373401923243933)
        ·
          refine ⟨7520878101140025721216475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20055674936373401923243933 7520878101140025721216475)
          ·
            refine ⟨11281317151710038581824713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7520878101140025721216475 11281317151710038581824713)
            ·
              refine ⟨8460987863782528936368535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11281317151710038581824713 8460987863782528936368535)
              ·
                refine ⟨12691481795673793404552803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8460987863782528936368535 12691481795673793404552803)
                ·
                  refine ⟨19037222693510690106829205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12691481795673793404552803 19037222693510690106829205)
                  ·
                    refine ⟨892369813758313598757619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19037222693510690106829205 892369813758313598757619)
                    ·
                      rfl

theorem cell23_5213652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_5213652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213652 prefixEnd_5213652 := by exact prefixLift 5213652
  have htrace : WordTrace (prefixWord ++ tailWord_5213652) baseStart_5213652 baseEnd_5213652 := by
    simpa [prefixWord, tailWord_5213652, baseEnd_5213652] using wordTrace_append hprefix tailTrace_5213652
  have hstable : (prefixWord ++ tailWord_5213652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213652).length < 2 ^ (prefixWord ++ tailWord_5213652).sum := by decide
  have hdescent : baseEnd_5213652 < baseStart_5213652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213665 : List Nat := [1, 2, 3, 1, 2, 4, 3, 7]
def baseStart_5213665 : Nat := 118140960795 + 5213665 * 2 ^ 59
def prefixEnd_5213665 : Nat := 4983230072969 + 3 ^ 40 * 5213665 * 2
def baseEnd_5213665 : Nat := 99152448760127749830011

theorem tailTrace_5213665 : CollatzResearch.WordTrace tailWord_5213665 prefixEnd_5213665 99152448760127749830011 := by
  unfold tailWord_5213665
  simp only [CollatzResearch.WordTrace]
  refine ⟨190157984656789602936906449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126771989771193068624604299 190157984656789602936906449)
  ·
    refine ⟨142618488492592202202679837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190157984656789602936906449 142618488492592202202679837)
    ·
      refine ⟨53481933184722075826004939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142618488492592202202679837 53481933184722075826004939)
      ·
        refine ⟨80222899777083113739007409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53481933184722075826004939 80222899777083113739007409)
        ·
          refine ⟨60167174832812335304255557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80222899777083113739007409 60167174832812335304255557)
          ·
            refine ⟨11281345281152312869547917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60167174832812335304255557 11281345281152312869547917)
            ·
              refine ⟨4230504480432117326080469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11281345281152312869547917 4230504480432117326080469)
              ·
                refine ⟨99152448760127749830011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4230504480432117326080469 99152448760127749830011)
                ·
                  rfl

theorem cell23_5213665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 7].length) (baseStart_5213665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213665 prefixEnd_5213665 := by exact prefixLift 5213665
  have htrace : WordTrace (prefixWord ++ tailWord_5213665) baseStart_5213665 baseEnd_5213665 := by
    simpa [prefixWord, tailWord_5213665, baseEnd_5213665] using wordTrace_append hprefix tailTrace_5213665
  have hstable : (prefixWord ++ tailWord_5213665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213665).length < 2 ^ (prefixWord ++ tailWord_5213665).sum := by decide
  have hdescent : baseEnd_5213665 < baseStart_5213665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213716 : List Nat := [2, 4, 3, 1, 3, 1, 2, 7]
def baseStart_5213716 : Nat := 118140960795 + 5213716 * 2 ^ 59
def prefixEnd_5213716 : Nat := 4983230072969 + 3 ^ 40 * 5213716 * 2
def baseEnd_5213716 : Nat := 99153418668030686884169

theorem tailTrace_5213716 : CollatzResearch.WordTrace tailWord_5213716 prefixEnd_5213716 99153418668030686884169 := by
  unfold tailWord_5213716
  simp only [CollatzResearch.WordTrace]
  refine ⟨95079922389802419323506501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126773229853069892431342001 95079922389802419323506501)
  ·
    refine ⟨17827485448087953623157469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95079922389802419323506501 17827485448087953623157469)
    ·
      refine ⟨6685307043032982608684051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17827485448087953623157469 6685307043032982608684051)
      ·
        refine ⟨10027960564549473913026077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6685307043032982608684051 10027960564549473913026077)
        ·
          refine ⟨3760485211706052717384779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10027960564549473913026077 3760485211706052717384779)
          ·
            refine ⟨5640727817559079076077169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3760485211706052717384779 5640727817559079076077169)
            ·
              refine ⟨4230545863169309307057877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5640727817559079076077169 4230545863169309307057877)
              ·
                refine ⟨99153418668030686884169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4230545863169309307057877 99153418668030686884169)
                ·
                  rfl

theorem cell23_5213716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 7].length) (baseStart_5213716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213716 prefixEnd_5213716 := by exact prefixLift 5213716
  have htrace : WordTrace (prefixWord ++ tailWord_5213716) baseStart_5213716 baseEnd_5213716 := by
    simpa [prefixWord, tailWord_5213716, baseEnd_5213716] using wordTrace_append hprefix tailTrace_5213716
  have hstable : (prefixWord ++ tailWord_5213716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213716).length < 2 ^ (prefixWord ++ tailWord_5213716).sum := by decide
  have hdescent : baseEnd_5213716 < baseStart_5213716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213749 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 4, 2, 2]
def baseStart_5213749 : Nat := 118140960795 + 5213749 * 2 ^ 59
def prefixEnd_5213749 : Nat := 4983230072969 + 3 ^ 40 * 5213749 * 2
def baseEnd_5213749 : Nat := 2677159248898426916759911

theorem tailTrace_5213749 : CollatzResearch.WordTrace tailWord_5213749 prefixEnd_5213749 2677159248898426916759911 := by
  unfold tailWord_5213749
  simp only [CollatzResearch.WordTrace]
  refine ⟨190161048388485285282964301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126774032258990190188642867 190161048388485285282964301)
  ·
    refine ⟨71310393145681981981111613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190161048388485285282964301 71310393145681981981111613)
    ·
      refine ⟨26741397429630743242916855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71310393145681981981111613 26741397429630743242916855)
      ·
        refine ⟨40112096144446114864375283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26741397429630743242916855 40112096144446114864375283)
        ·
          refine ⟨60168144216669172296562925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40112096144446114864375283 60168144216669172296562925)
          ·
            refine ⟨22563054081250939611211097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60168144216669172296562925 22563054081250939611211097)
            ·
              refine ⟨16922290560938204708408323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22563054081250939611211097 16922290560938204708408323)
              ·
                refine ⟨25383435841407307062612485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16922290560938204708408323 25383435841407307062612485)
                ·
                  refine ⟨4759394220263870074239841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25383435841407307062612485 4759394220263870074239841)
                  ·
                    refine ⟨3569545665197902555679881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4759394220263870074239841 3569545665197902555679881)
                    ·
                      refine ⟨2677159248898426916759911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3569545665197902555679881 2677159248898426916759911)
                      ·
                        rfl

theorem cell23_5213749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_5213749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213749 prefixEnd_5213749 := by exact prefixLift 5213749
  have htrace : WordTrace (prefixWord ++ tailWord_5213749) baseStart_5213749 baseEnd_5213749 := by
    simpa [prefixWord, tailWord_5213749, baseEnd_5213749] using wordTrace_append hprefix tailTrace_5213749
  have hstable : (prefixWord ++ tailWord_5213749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213749).length < 2 ^ (prefixWord ++ tailWord_5213749).sum := by decide
  have hdescent : baseEnd_5213749 < baseStart_5213749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213765 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 1, 5, 3]
def baseStart_5213765 : Nat := 118140960795 + 5213765 * 2 ^ 59
def prefixEnd_5213765 : Nat := 4983230072969 + 3 ^ 40 * 5213765 * 2
def baseEnd_5213765 : Nat := 2677167464588898854159837

theorem tailTrace_5213765 : CollatzResearch.WordTrace tailWord_5213765 prefixEnd_5213765 2677167464588898854159837 := by
  unfold tailWord_5213765
  simp only [CollatzResearch.WordTrace]
  refine ⟨190161631956427320015546749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126774421304284880010364499 190161631956427320015546749)
  ·
    refine ⟨71310611983660245005830031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190161631956427320015546749 71310611983660245005830031)
    ·
      refine ⟨106965917975490367508745047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71310611983660245005830031 106965917975490367508745047)
      ·
        refine ⟨160448876963235551263117571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106965917975490367508745047 160448876963235551263117571)
        ·
          refine ⟨240673315444853326894676357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160448876963235551263117571 240673315444853326894676357)
          ·
            refine ⟨45126246645909998792751817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 240673315444853326894676357 45126246645909998792751817)
            ·
              refine ⟨33844684984432499094563863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45126246645909998792751817 33844684984432499094563863)
              ·
                refine ⟨50767027476648748641845795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33844684984432499094563863 50767027476648748641845795)
                ·
                  refine ⟨76150541214973122962768693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50767027476648748641845795 76150541214973122962768693)
                  ·
                    refine ⟨7139113238903730277759565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76150541214973122962768693 7139113238903730277759565)
                    ·
                      refine ⟨2677167464588898854159837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7139113238903730277759565 2677167464588898854159837)
                      ·
                        rfl

theorem cell23_5213765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 5, 3].length) (baseStart_5213765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213765 prefixEnd_5213765 := by exact prefixLift 5213765
  have htrace : WordTrace (prefixWord ++ tailWord_5213765) baseStart_5213765 baseEnd_5213765 := by
    simpa [prefixWord, tailWord_5213765, baseEnd_5213765] using wordTrace_append hprefix tailTrace_5213765
  have hstable : (prefixWord ++ tailWord_5213765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213765).length < 2 ^ (prefixWord ++ tailWord_5213765).sum := by decide
  have hdescent : baseEnd_5213765 < baseStart_5213765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5213795 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 5]
def baseStart_5213795 : Nat := 118140960795 + 5213795 * 2 ^ 59
def prefixEnd_5213795 : Nat := 4983230072969 + 3 ^ 40 * 5213795 * 2
def baseEnd_5213795 : Nat := 2677182869008533736784699

theorem tailTrace_5213795 : CollatzResearch.WordTrace tailWord_5213795 prefixEnd_5213795 2677182869008533736784699 := by
  unfold tailWord_5213795
  simp only [CollatzResearch.WordTrace]
  refine ⟨190162726146318635139138839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126775150764212423426092559 190162726146318635139138839)
  ·
    refine ⟨285244089219477952708708259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190162726146318635139138839 285244089219477952708708259)
    ·
      refine ⟨427866133829216929063062389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285244089219477952708708259 427866133829216929063062389)
      ·
        refine ⟨40112450046489087099662099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 427866133829216929063062389 40112450046489087099662099)
        ·
          refine ⟨60168675069733630649493149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40112450046489087099662099 60168675069733630649493149)
          ·
            refine ⟨22563253151150111493559931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60168675069733630649493149 22563253151150111493559931)
            ·
              refine ⟨33844879726725167240339897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22563253151150111493559931 33844879726725167240339897)
              ·
                refine ⟨25383659795043875430254923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33844879726725167240339897 25383659795043875430254923)
                ·
                  refine ⟨38075489692565813145382385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25383659795043875430254923 38075489692565813145382385)
                  ·
                    refine ⟨28556617269424359859036789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38075489692565813145382385 28556617269424359859036789)
                    ·
                      refine ⟨2677182869008533736784699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28556617269424359859036789 2677182869008533736784699)
                      ·
                        rfl

theorem cell23_5213795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_5213795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5213795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5213795 prefixEnd_5213795 := by exact prefixLift 5213795
  have htrace : WordTrace (prefixWord ++ tailWord_5213795) baseStart_5213795 baseEnd_5213795 := by
    simpa [prefixWord, tailWord_5213795, baseEnd_5213795] using wordTrace_append hprefix tailTrace_5213795
  have hstable : (prefixWord ++ tailWord_5213795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5213795).length < 2 ^ (prefixWord ++ tailWord_5213795).sum := by decide
  have hdescent : baseEnd_5213795 < baseStart_5213795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5213795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
